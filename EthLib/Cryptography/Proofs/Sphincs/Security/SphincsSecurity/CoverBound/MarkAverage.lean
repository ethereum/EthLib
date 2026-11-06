module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Base.Poisson

/-!
# Averaging out the marks

A view is a pair of an index and a mark.

Let `f` be a function of view multisets and `F` a function of index multisets.

Then `f` is dominated by `F` if its average over uniform marks at any index list `L` is `≤ F(L)`.

Domination bounds the one-coin H-term of `f` over views by the H-term of `F` over indices.

Each step of the virtual future draws uniform views: fresh slots, item coins and future pairs.

So each step commutes with the average over the marks of the views that it draws.
-/

@[expose] public section

open ENNReal

namespace SphincsSecurity.Security.H0Avg

open SphincsSecurity.Base.Domination SphincsSecurity.Base.H0

variable {ι M : Type} [Fintype ι] [Fintype M] [Nonempty M]

set_option linter.unusedSectionVars false

/-! ### Averages over uniform marks -/

/-- The average of `f` over uniform marks at the listed indices, the new views added to `d`. -/
noncomputable def avgL (f : Multiset (ι × M) → ℝ≥0∞) : List ι → Multiset (ι × M) → ℝ≥0∞
  | [], d => f d
  | l :: L, d => freshAvg Finset.univ fun m : M => avgL f L (d + {(l, m)})

/-- The average of a function of an item list over independent uniform marks of the items. -/
noncomputable def avgI (Φ : List (ι × M) → ℝ≥0∞) : List ι → ℝ≥0∞
  | [] => Φ []
  | l :: J => freshAvg Finset.univ fun m : M => avgI (fun I => Φ ((l, m) :: I)) J

omit [Fintype ι] [Fintype M] [Nonempty M] in
theorem freshAvg_comm {α β : Type} (U : Finset α) (W : Finset β) (h : α → β → ℝ≥0∞) :
    freshAvg U (fun a => freshAvg W fun b => h a b) =
      freshAvg W (fun b => freshAvg U fun a => h a b) := by
  unfold freshAvg
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

omit [Nonempty M] in
theorem freshAvg_prod (h : ι × M → ℝ≥0∞) :
    freshAvg (Finset.univ : Finset (ι × M)) h =
      freshAvg Finset.univ fun l : ι => freshAvg Finset.univ fun m : M => h (l, m) := by
  unfold freshAvg
  rw [Finset.card_univ, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
    Fintype.sum_prod_type, Finset.card_univ, Finset.card_univ, mul_assoc]
  congr 1
  rw [Finset.mul_sum]

theorem freshAvg_const' (c : ℝ≥0∞) : freshAvg (Finset.univ : Finset M) (fun _ => c) = c :=
  freshAvg_const (Finset.univ : Finset M) Finset.univ_nonempty c

/-! ### Linearity of the mark averages -/

theorem avgL_shift (f : Multiset (ι × M) → ℝ≥0∞) (x : Multiset (ι × M)) :
    ∀ (L : List ι) d0, avgL (fun d => f (d + x)) L d0 = avgL f L (d0 + x)
  | [], d0 => rfl
  | l :: L, d0 => by
      simp only [avgL]
      congr 1
      funext m
      rw [avgL_shift f x L, add_right_comm]

theorem avgL_freshAvg {α : Type} (U : Finset α) (g : α → Multiset (ι × M) → ℝ≥0∞) :
    ∀ (L : List ι) d0,
      avgL (fun d => freshAvg U fun u => g u d) L d0 = freshAvg U fun u => avgL (g u) L d0
  | [], d0 => rfl
  | l :: L, d0 => by
      simp only [avgL]
      simp only [avgL_freshAvg U g L]
      exact freshAvg_comm _ _ _

theorem avgL_add (f g : Multiset (ι × M) → ℝ≥0∞) :
    ∀ (L : List ι) d0, avgL (fun d => f d + g d) L d0 = avgL f L d0 + avgL g L d0
  | [], d0 => rfl
  | l :: L, d0 => by
      simp only [avgL, avgL_add f g L]
      exact freshAvg_add _ _ _

theorem avgL_const_mul (c : ℝ≥0∞) (f : Multiset (ι × M) → ℝ≥0∞) :
    ∀ (L : List ι) d0, avgL (fun d => c * f d) L d0 = c * avgL f L d0
  | [], d0 => rfl
  | l :: L, d0 => by
      simp only [avgL, avgL_const_mul c f L]
      exact freshAvg_mul _ _ _

theorem avgL_mono {f g : Multiset (ι × M) → ℝ≥0∞} (h : ∀ d, f d ≤ g d) :
    ∀ (L : List ι) d0, avgL f L d0 ≤ avgL g L d0
  | [], d0 => h d0
  | _ :: L, _ => freshAvg_mono _ fun _ _ => avgL_mono h L _

theorem avgI_freshAvg {α : Type} (U : Finset α) (g : α → List (ι × M) → ℝ≥0∞) :
    ∀ (J : List ι), avgI (fun I => freshAvg U fun u => g u I) J = freshAvg U fun u => avgI (g u) J
  | [] => rfl
  | l :: J => by
      simp only [avgI]
      simp only [avgI_freshAvg U (fun u I => g u ((l, _) :: I)) J]
      exact freshAvg_comm _ _ _

theorem avgI_add (Φ Ψ : List (ι × M) → ℝ≥0∞) :
    ∀ (J : List ι), avgI (fun I => Φ I + Ψ I) J = avgI Φ J + avgI Ψ J
  | [] => rfl
  | l :: J => by
      simp only [avgI, avgI_add (fun I => Φ ((l, _) :: I)) (fun I => Ψ ((l, _) :: I)) J]
      exact freshAvg_add _ _ _

theorem avgI_const_mul (c : ℝ≥0∞) (Φ : List (ι × M) → ℝ≥0∞) :
    ∀ (J : List ι), avgI (fun I => c * Φ I) J = c * avgI Φ J
  | [] => rfl
  | l :: J => by
      simp only [avgI, avgI_const_mul c (fun I => Φ ((l, _) :: I)) J]
      exact freshAvg_mul _ _ _

/-! ### The operators of the virtual future -/

/-- For every index list, the average of `f` over the marks is at most `F` of the indices. -/
def Dominated (f : Multiset (ι × M) → ℝ≥0∞) (F : Multiset ι → ℝ≥0∞) : Prop :=
  ∀ L : List ι, avgL f L 0 ≤ F (L : Multiset ι)

omit [Fintype M] [Nonempty M] in
theorem coe_cons_eq (l : ι) (L : List ι) :
    ((l :: L : List ι) : Multiset ι) = (L : Multiset ι) + {l} := by
  rw [← Multiset.cons_coe, ← Multiset.singleton_add, add_comm]

/-- Domination carries over to the expected values after `m` fresh slots. -/
theorem fresh_dominated {f : Multiset (ι × M) → ℝ≥0∞} {F : Multiset ι → ℝ≥0∞} (h : Dominated f F) :
    ∀ m, Dominated (fresh Finset.univ f m) (fresh Finset.univ F m)
  | 0 => h
  | m + 1 => by
      intro L
      have ih := fresh_dominated h m
      simp only [fresh]
      rw [avgL_freshAvg, freshAvg_prod]
      refine freshAvg_mono _ fun l _ => ?_
      calc freshAvg Finset.univ (fun mk : M => avgL
          (fun d => fresh Finset.univ f m (d + {(l, mk)})) L 0)
          = avgL (fresh Finset.univ f m) (l :: L) 0 := by
            simp only [avgL]
            congr 1
            funext mk
            rw [avgL_shift]
        _ ≤ fresh Finset.univ F m ((l :: L : List ι) : Multiset ι) := ih (l :: L)
        _ = _ := by rw [coe_cons_eq]

/-- Domination carries over to the expected values after one coin of probability `w` per item. -/
theorem slot_dominated (w : ℝ≥0∞) {g : Multiset (ι × M) → ℝ≥0∞} {G : Multiset ι → ℝ≥0∞}
    (h : Dominated g G) :
    ∀ (J L : List ι), avgI (fun I => avgL (fun d => slotValue g d (itemCoins w I)) L 0) J ≤
      slotValue G (L : Multiset ι) (itemCoins w J)
  | [], L => by
      simp only [avgI, itemCoins, List.map_nil, slotValue]
      exact h L
  | l :: J, L => by
      have ih := slot_dominated w h J
      simp only [avgI, itemCoins_cons, slotValue]
      -- Split the coin of the first item.
      have hsplit : ∀ mk : M,
          (fun I => avgL (fun d => w * slotValue g (d + {(l, mk)}) (itemCoins w I) +
          (1 - w) * slotValue g d (itemCoins w I)) L 0) =
          fun I => w * avgL (fun d => slotValue g d (itemCoins w I)) L {(l, mk)} +
            (1 - w) * avgL (fun d => slotValue g d (itemCoins w I)) L 0 := by
        intro mk
        funext I
        rw [avgL_add, avgL_const_mul, avgL_const_mul,
          avgL_shift (fun d => slotValue g d (itemCoins w I)) {(l, mk)} L 0, zero_add]
      simp only [itemCoins] at hsplit
      simp only [itemCoins, hsplit, avgI_add, avgI_const_mul]
      rw [freshAvg_add, freshAvg_mul, freshAvg_mul, freshAvg_const']
      refine add_le_add (mul_le_mul_right ?_ _) (mul_le_mul_right ?_ _)
      · rw [← avgI_freshAvg]
        have hdef : (fun I => freshAvg Finset.univ fun mk : M =>
            avgL (fun d => slotValue g d (List.map
                (fun w' => (w, ({w'} : Multiset (ι × M)))) I)) L {(l, mk)}) =
            fun I => avgL (fun d => slotValue g d (itemCoins w I)) (l :: L) 0 := by
          funext I
          simp only [avgL, zero_add, itemCoins]
        rw [hdef]
        refine le_trans (ih (l :: L)) (le_of_eq ?_)
        rw [coe_cons_eq]
        rfl
      · exact ih L

/-- A bound on the item averages carries over to the expected values after `k` future pairs. -/
theorem creations_dominated (lam : ℝ≥0∞) {Gv : List (ι × M) → ℝ≥0∞} {Gi : List ι → ℝ≥0∞}
    (h : ∀ J, avgI Gv J ≤ Gi J) :
    ∀ k J, avgI (creations Finset.univ lam Gv k) J ≤ creations Finset.univ lam Gi k J
  | 0, J => h J
  | k + 1, J => by
      have ih := creations_dominated lam h k
      simp only [creations]
      rw [avgI_add, avgI_const_mul, avgI_const_mul, avgI_freshAvg, freshAvg_prod]
      refine add_le_add (mul_le_mul_right (ih J) _)
          (mul_le_mul_right (freshAvg_mono _ fun l _ => ?_) _)
      calc freshAvg Finset.univ (fun mk : M => avgI
          (fun I => creations Finset.univ lam Gv k ((l, mk) :: I)) J)
          = avgI (creations Finset.univ lam Gv k) (l :: J) := rfl
        _ ≤ _ := ih (l :: J)

/-- If `f` is dominated by `F`, the H-term of `f` over views is at most that of `F` over indices. -/
theorem hTermO_le_of_dominated (w lam : ℝ≥0∞) (N q : ℕ) {f : Multiset (ι × M) → ℝ≥0∞}
    {F : Multiset ι → ℝ≥0∞} (h : Dominated f F) :
    hTermO (Finset.univ : Finset (ι × M)) w lam N q f ≤
      hTermO (Finset.univ : Finset ι) w lam N q F := by
  unfold hTermO
  have hv : ∀ J, avgI (fun I => virtualOnce Finset.univ w f N I 0) J ≤
      virtualOnce Finset.univ w F N J 0 := by
    intro J
    have := slot_dominated w (fresh_dominated h N) J []
    simpa [virtualOnce, avgL] using this
  exact creations_dominated lam hv q []

end SphincsSecurity.Security.H0Avg
