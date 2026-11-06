module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.CoverBound.MarkAverage

/-!
# Mark averages of functions of one index

A function of the views at one index reads only the marks at that index.

Its average over independent uniform marks depends only on the number of views at the index.

Sums of such functions over the indices average termwise, and products average factorwise.

The same holds one level down, for a mark that is a tuple of independent coordinates.

A FORS mark is such a tuple, with one leaf for each tree.
-/

@[expose] public section

open ENNReal

namespace SphincsSecurity.Security.H0Avg

open SphincsSecurity.Base.Domination SphincsSecurity.Base.H0

set_option linter.unusedSectionVars false

/-! ### Averages over `n` uniform elements -/

section AvgN

variable {U : Type} [Fintype U] [Nonempty U]

/-- The average of `φ` over `n` independent uniform elements added to `X`. -/
noncomputable def avgN (φ : Multiset U → ℝ≥0∞) : ℕ → Multiset U → ℝ≥0∞
  | 0, X => φ X
  | n + 1, X => freshAvg Finset.univ fun u : U => avgN φ n (X + {u})

theorem avgN_mono {φ ψ : Multiset U → ℝ≥0∞} (h : ∀ X, φ X ≤ ψ X) : ∀ n X, avgN φ n X ≤ avgN ψ n X
  | 0, X => h X
  | n + 1, _ => freshAvg_mono _ fun _ _ => avgN_mono h n _

theorem avgN_add (φ ψ : Multiset U → ℝ≥0∞) :
    ∀ n X, avgN (fun Y => φ Y + ψ Y) n X = avgN φ n X + avgN ψ n X
  | 0, X => rfl
  | n + 1, X => by
      simp only [avgN, avgN_add φ ψ n]
      exact freshAvg_add _ _ _

theorem avgN_const_mul (c : ℝ≥0∞) (φ : Multiset U → ℝ≥0∞) :
    ∀ n X, avgN (fun Y => c * φ Y) n X = c * avgN φ n X
  | 0, X => rfl
  | n + 1, X => by
      simp only [avgN, avgN_const_mul c φ n]
      exact freshAvg_mul _ _ _

theorem avgN_const (c : ℝ≥0∞) : ∀ n X, avgN (fun _ : Multiset U => c) n X = c
  | 0, X => rfl
  | n + 1, X => by
      simp only [avgN, avgN_const c n]
      exact freshAvg_const _ Finset.univ_nonempty c

end AvgN

/-! ### Marks at an index -/

section Marks

variable {ι M : Type} [Fintype ι] [DecidableEq ι] [Fintype M] [Nonempty M]

/-- The marks of the views at the index `l`. -/
def marksAt (l : ι) (d : Multiset (ι × M)) : Multiset M := (d.filter fun v => v.1 = l).map Prod.snd

theorem marksAt_zero (l : ι) : marksAt l (0 : Multiset (ι × M)) = 0 := by simp [marksAt]

theorem marksAt_add_single (l l0 : ι) (m : M) (d : Multiset (ι × M)) :
    marksAt l (d + {(l0, m)}) = marksAt l d + if l0 = l then {m} else 0 := by
  unfold marksAt
  rw [Multiset.filter_add, Multiset.map_add]
  congr 1
  by_cases h : l0 = l
  · rw [ite_eq_left h, Multiset.filter_singleton, ite_eq_left h]
    rfl
  · rw [ite_eq_right h, Multiset.filter_singleton, ite_eq_right h]
    rfl

theorem prod_update_split (F : ι → ℝ≥0∞) (l0 : ι) :
    ∏ l, F l = F l0 * ∏ l ∈ Finset.univ.erase l0, F l :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ l0)).symm

/-- A product of functions of the marks at each index averages factorwise. -/
theorem avgL_prod_marks (φ : ι → Multiset M → ℝ≥0∞) :
    ∀ (L : List ι) (d0 : Multiset (ι × M)),
      avgL (fun d => ∏ l, φ l (marksAt l d)) L d0 = ∏ l, avgN (φ l) (L.count l) (marksAt l d0)
  | [], d0 => by simp [avgL, avgN]
  | l0 :: L, d0 => by
      simp only [avgL, avgL_prod_marks φ L]
      have hpt : ∀ m : M, ∏ l, avgN (φ l) (L.count l) (marksAt l (d0 + {(l0, m)})) =
          avgN (φ l0) (L.count l0) (marksAt l0 d0 + {m}) *
            ∏ l ∈ Finset.univ.erase l0, avgN (φ l) (L.count l) (marksAt l d0) := by
        intro m
        rw [prod_update_split _ l0, marksAt_add_single, ite_eq_left rfl]
        congr 1
        refine Finset.prod_congr rfl fun l hl => ?_
        rw [marksAt_add_single, ite_eq_right (Ne.symm (Finset.ne_of_mem_erase hl)), add_zero]
      simp only [hpt]
      rw [show (fun m : M => avgN (φ l0) (L.count l0) (marksAt l0 d0 + {m}) *
          ∏ l ∈ Finset.univ.erase l0, avgN (φ l) (L.count l) (marksAt l d0)) =
        fun m => (∏ l ∈ Finset.univ.erase l0, avgN (φ l) (L.count l) (marksAt l d0)) *
          avgN (φ l0) (L.count l0) (marksAt l0 d0 + {m}) from
            funext fun m => mul_comm _ _, freshAvg_mul,
        prod_update_split (fun l => avgN (φ l) ((l0 :: L).count l) (marksAt l d0)) l0,
        List.count_cons_self, mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun l hl => ?_
      rw [List.count_cons, ite_eq_right (by simpa [beq_iff_eq] using
          (Ne.symm (Finset.ne_of_mem_erase hl))), add_zero]

/-- A sum of functions of the marks at each index averages termwise. -/
theorem avgL_sum_marks (φ : ι → Multiset M → ℝ≥0∞) :
    ∀ (L : List ι) (d0 : Multiset (ι × M)),
      avgL (fun d => ∑ l, φ l (marksAt l d)) L d0 = ∑ l, avgN (φ l) (L.count l) (marksAt l d0)
  | [], d0 => by simp [avgL, avgN]
  | l0 :: L, d0 => by
      simp only [avgL, avgL_sum_marks φ L]
      rw [show (fun m : M => ∑ l, avgN (φ l) (L.count l) (marksAt l (d0 + {(l0, m)}))) =
          fun m => ∑ l, avgN (φ l) (L.count l) (marksAt l d0 + if l0 = l then {m} else 0) from
        funext fun m => by simp only [marksAt_add_single]]
      unfold freshAvg
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases h : l0 = l
      · subst h
        simp only [ite_true, List.count_cons_self, avgN]
        rfl
      · simp only [ite_eq_right h, add_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [List.count_cons, ite_eq_right (by simp [beq_iff_eq, h]), add_zero, ← mul_assoc,
          ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero)
            (ENNReal.natCast_ne_top _), one_mul]

/-- Let `f` be at most a sum plus `A` times a product of functions of the marks at each index.

Let `gbar` and `hbar` bound the averages of the two functions over `n` uniform marks.

Then `f` is dominated by the same sum and product of `gbar` and `hbar` at the index counts. -/
theorem dominated_of_split {f : Multiset (ι × M) → ℝ≥0∞} (g h : Multiset M → ℝ≥0∞) (A : ℝ≥0∞)
    (hf : ∀ d, f d ≤ ∑ l, g (marksAt l d) + A * ∏ l, h (marksAt l d))
    (gbar hbar : ℕ → ℝ≥0∞) (hg : ∀ n, avgN g n 0 ≤ gbar n) (hh : ∀ n, avgN h n 0 ≤ hbar n) :
    Dominated f (fun e => ∑ l, gbar (e.count l) + A * ∏ l, hbar (e.count l)) := by
  intro L
  refine le_trans (avgL_mono hf L 0) ?_
  rw [avgL_add, avgL_const_mul, avgL_sum_marks (fun _ => g), avgL_prod_marks (fun _ => h)]
  simp only [marksAt_zero, Multiset.coe_count]
  gcongr with l _ l _
  · exact hg _
  · exact hh _

end Marks

/-! ### Marks with independent coordinates -/

section Coords

variable {κ X : Type} [Fintype κ] [DecidableEq κ] [Fintype X] [Nonempty X]

theorem freshAvg_pi_prod (G : κ → X → ℝ≥0∞) :
    freshAvg (Finset.univ : Finset (κ → X)) (fun m => ∏ c, G c (m c)) =
      ∏ c, freshAvg (Finset.univ : Finset X) (G c) := by
  unfold freshAvg
  rw [Finset.prod_mul_distrib, Fintype.prod_sum, Finset.prod_const, Finset.card_univ,
    Finset.card_univ, Finset.card_univ, Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]

/-- Over `n` uniform tuples, a product of functions of each coordinate averages factorwise. -/
theorem avgN_prod_coords (ψ : κ → Multiset X → ℝ≥0∞) :
    ∀ n (X0 : Multiset (κ → X)),
      avgN (fun Ms => ∏ c, ψ c (Ms.map fun m => m c)) n X0 = ∏ c, avgN (ψ c) n (X0.map fun m => m c)
  | 0, X0 => rfl
  | n + 1, X0 => by
      simp only [avgN, avgN_prod_coords ψ n, Multiset.map_add, Multiset.map_singleton]
      exact freshAvg_pi_prod (fun c x => avgN (ψ c) n (X0.map (fun m => m c) + {x}))

end Coords

end SphincsSecurity.Security.H0Avg
