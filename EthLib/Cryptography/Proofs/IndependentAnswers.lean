module

public import EthLib.Cryptography.Proofs.LazyPermutation
public import EthLib.Cryptography.Proofs.BadOnGrowth
public import VCVio.OracleComp.SimSemantics.StateT.UntilBad
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Proofs: a random permutation answered by independent uniform values

The lazy permutation answers a new forward query with a uniform value that is no cached image.

It answers a new inverse query with a uniform value that is no cached preimage.

The oracle here answers every new query with a uniform value of the whole set instead.

It keeps the same cache, and raises a flag when the new value is already in the cache.

Until the flag rises, the lazy permutation puts at least as much mass on each outcome.

A new query raises the flag with chance at most the size of the cache over `|A|`.

Take a run that asks the permutation, in either direction, at most `Q` times.

Compare an event under the lazy permutation with the same event here, with no flag raised.

The first chance exceeds the second by at most `Q (Q - 1) / 2` over `|A|`.

This is the birthday bound between a random permutation and independent answers.

The source is [Fersch, Kiltz, Poettering, CCS 2016](https://doi.org/10.1145/2976749.2978413).

The swap is the step from Game G0 to Game G1 of their §4.2, in the proof of their Theorem 2.

Their Game G1 is in their Figure 7.

Their bound there is `Q² / 2^L`; the bound here is half of it, or less.
-/

@[expose] public section

namespace EthLib.Cryptography.LazyPermutation

open OracleComp OracleSpec ENNReal

variable {A : Type} [FinEnum A]

/-! ## Uniform draws that avoid a list -/

/-- Draw a uniform value outside a list, and keep it only when it is outside a larger list.

That puts at most the mass of a uniform value outside the larger list, on each event. -/
theorem prEvent_uniformOutside_and_notMem_le {used used' : List A} (h : used ⊆ used')
    (d d' : A) (p : A → Prop) :
    Pr{let y ← uniformOutside used d}[p y ∧ y ∉ used'] ≤
      Pr{let y ← uniformOutside used' d'}[p y] := by
  classical
  have hsub : ∀ y, y ∉ used' → y ∉ used := fun _ hy hu => hy (h hu)
  by_cases hL : ((FinEnum.toList A).filter fun b => b ∉ used) = []
  · have hd : d ∈ used := by
      by_contra hd
      have hmem : d ∈ (FinEnum.toList A).filter fun b => b ∉ used :=
        List.mem_filter.2 ⟨FinEnum.mem_toList d, by simpa using hd⟩
      rw [hL] at hmem
      simp at hmem
    rw [uniformOutside, hL, uniformFrom]
    simp [h hd]
  have hcount : ((FinEnum.toList A).filter fun b => b ∉ used).countP
      (fun y => decide (p y ∧ y ∉ used')) =
      ((FinEnum.toList A).filter fun b => b ∉ used').countP (fun y => decide (p y)) := by
    rw [List.countP_filter, List.countP_filter]
    refine List.countP_congr fun y _ => ?_
    by_cases hy : y ∈ used' <;> simp [hy, hsub y]
  rw [uniformOutside, prEvent_uniformFrom_eq_countP hL d, hcount]
  by_cases hf : ((FinEnum.toList A).filter fun b => b ∉ used') = []
  · rw [hf]
    simp
  · rw [uniformOutside, prEvent_uniformFrom_eq_countP hf d']
    refine ENNReal.div_le_div_left ?_ _
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact_mod_cast List.countP_mono_left fun y _ hy => by simpa using hsub y (by simpa using hy)

/-- Draw a uniform value of `A`, and keep it only when it is outside a list.

That puts at most the mass of a uniform value outside the list, on each event. -/
theorem prEvent_uniformOutside_nil_and_notMem_le (used : List A) (d d' : A) (p : A → Prop) :
    Pr{let y ← uniformOutside [] d}[p y ∧ y ∉ used] ≤
      Pr{let y ← uniformOutside used d'}[p y] :=
  prEvent_uniformOutside_and_notMem_le (List.nil_subset _) d d' p

/-- A uniform value outside a list lies in a second list with chance at most a ratio.

Let `n` be the length of the first list.

The ratio is the length of the second list over `|A| - n`. -/
theorem prEvent_uniformOutside_mem_le (used L : List A) (d : A) :
    Pr{let y ← uniformOutside used d}[y ∈ L] ≤
      (L.length : ℝ≥0∞) / ((FinEnum.card A - used.length : ℕ) : ℝ≥0∞) := by
  have hcard := card_sub_length_le_length_filter used
  by_cases hL : ((FinEnum.toList A).filter fun b => b ∉ used) = []
  · rw [hL, List.length_nil, Nat.le_zero] at hcard
    rw [hcard, Nat.cast_zero]
    rcases L with _ | ⟨y, L⟩
    · rw [prEvent_eq_zero_of_forall_not _ _ fun y hy => List.not_mem_nil hy]
      exact zero_le
    · rw [ENNReal.div_zero (by simp)]
      exact le_top
  · rw [uniformOutside, prEvent_uniformFrom_eq_countP hL d]
    refine ENNReal.div_le_div ?_ (by exact_mod_cast hcard)
    rw [List.countP_eq_length_filter]
    exact_mod_cast (List.subperm_of_subset ((FinEnum.nodup_toList).filter _ |>.filter _)
      fun y hy => by simpa using (List.mem_filter.1 hy).2).length_le

/-- A uniform value of `A` lies in a list with chance at most its length over `|A|`. -/
theorem prEvent_uniformOutside_nil_mem_le (used : List A) (d : A) :
    Pr{let y ← uniformOutside [] d}[y ∈ used] ≤ (used.length : ℝ≥0∞) / FinEnum.card A := by
  simpa using prEvent_uniformOutside_mem_le [] used d

/-- A uniform value of `A` avoiding nothing is the framework's uniform sample of `A`. -/
theorem uniformOutside_nil_evalDistEq [SampleableType A] (d : A) :
    uniformOutside [] d =ᵈ ($ᵗ A : ProbComp A) := by
  refine evalDistEq_of_forall_prEvent_eq_output fun x => ?_
  have hnil : ((FinEnum.toList A).filter fun b => b ∉ []) = FinEnum.toList A := by simp
  rw [uniformOutside, hnil,
    prEvent_uniformFrom_eq_of_mem FinEnum.nodup_toList d (FinEnum.mem_toList x),
    SampleableType.prEvent_uniformSample_eq_singleton_natCard, Nat.card_eq_fintype_card,
    ← FinEnum.card_eq_fintypeCard]
  simp [FinEnum.toList]

/-! ## The oracle -/

/-- The state: the pairs answered so far, the most recent first, and the flag.

The most recent pair comes first, so a position in the cache counts back from the last query. -/
abbrev IndepState (A : Type) := PermCache A × Bool

/-- The state after a new forward pair `(a, b)`: the pair joins the cache.

The flag rises if `b` is already a cached image. -/
abbrev IndepState.addForward (s : IndepState A) (a b : A) : IndepState A :=
  ((a, b) :: s.1, s.2 || decide (b ∈ s.1.map Prod.snd))

/-- The state after a new inverse pair `(a, b)`: the pair joins the cache.

The flag rises if `a` is already a cached preimage. -/
abbrev IndepState.addInverse (s : IndepState A) (a b : A) : IndepState A :=
  ((a, b) :: s.1, s.2 || decide (a ∈ s.1.map Prod.fst))

/-- The permutation oracle answered by independent uniform values.

A query answered before gets its answer again, in either direction.

A new query gets a uniform value of `A`, and the pair joins the cache.

The flag rises when a new forward answer is a cached image.

It also rises when a new inverse answer is a cached preimage.

Once raised, the flag stays. -/
def indepPermOracle : QueryImpl (PermSpec A) (StateT (IndepState A) ProbComp)
  | .inl a => fun s =>
    match s.1.lookup a with
    | some b => pure (b, s)
    | none => (fun b => (b, IndepState.addForward s a b)) <$> (uniformOutside [] a : ProbComp A)
  | .inr b => fun s =>
    match (s.1.map Prod.swap).lookup b with
    | some a => pure (a, s)
    | none => (fun a => (a, IndepState.addInverse s a b)) <$> (uniformOutside [] b : ProbComp A)

/-- The oracles with independent answers: coins, passed through, then the oracle above. -/
abbrev indepPermImpl : QueryImpl (unifSpec + PermSpec A) (StateT (IndepState A) ProbComp) :=
  unifSpec.passthrough + indepPermOracle

/-- A query of the permutation goes to the oracle with independent answers. -/
theorem indepPermImpl_inr (t : (PermSpec A).Domain) :
    (indepPermImpl (.inr t) : StateT (IndepState A) ProbComp _) = indepPermOracle t := rfl

/-- A forward query reads the cache, or draws a uniform value and checks it against the images. -/
theorem indepPermOracle_inl_run (a : A) (c : PermCache A) (f : Bool) :
    (indepPermOracle (.inl a)).run (c, f) =
      match c.lookup a with
      | some b => pure (b, (c, f))
      | none => (fun b => (b, ((a, b) :: c, f || decide (b ∈ c.map Prod.snd)))) <$>
        (uniformOutside [] a : ProbComp A) := rfl

/-- An inverse query reads the cache, or draws a uniform value and checks it against the queries. -/
theorem indepPermOracle_inr_run (b : A) (c : PermCache A) (f : Bool) :
    (indepPermOracle (.inr b)).run (c, f) =
      match (c.map Prod.swap).lookup b with
      | some a => pure (a, (c, f))
      | none => (fun a => (a, ((a, b) :: c, f || decide (a ∈ c.map Prod.fst)))) <$>
        (uniformOutside [] b : ProbComp A) := rfl

/-- A query of the permutation keeps the state, or adds one pair and keeps a raised flag. -/
theorem indepPermOracle_step (q : (PermSpec A).Domain) (s : IndepState A) (z)
    (hz : z ∈ support ((indepPermOracle q).run s)) :
    z.2 = s ∨ ∃ p, z.2.1 = p :: s.1 ∧ (s.2 = true → z.2.2 = true) := by
  obtain ⟨c, f⟩ := s
  rcases q with a | b
  · rw [indepPermOracle_inl_run] at hz
    split at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      exact Or.inl (by rw [hz])
    · simp only [support_map, Set.mem_image] at hz
      obtain ⟨b, -, rfl⟩ := hz
      exact Or.inr ⟨(a, b), rfl, fun h => by simp only at h; simp [h]⟩
  · rw [indepPermOracle_inr_run] at hz
    split at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      exact Or.inl (by rw [hz])
    · simp only [support_map, Set.mem_image] at hz
      obtain ⟨a, -, rfl⟩ := hz
      exact Or.inr ⟨(a, b), rfl, fun h => by simp only at h; simp [h]⟩

/-- Once raised, the flag stays. -/
theorem indepPermImpl_preservesInv_flag :
    QueryImpl.PreservesInv (indepPermImpl (A := A)) fun s => s.2 = true := by
  refine (preservesInv_passthrough _).add fun q s hs z hz => ?_
  rcases indepPermOracle_step q s z hz with h | ⟨_, -, h⟩
  · rw [h]
    exact hs
  · exact h hs

/-- Each step adds at most one pair, and only a query of the permutation adds one. -/
theorem length_le_of_mem_support_indepPermImpl (t : (unifSpec + PermSpec A).Domain)
    (s : IndepState A) (z) (hz : z ∈ support ((indepPermImpl t).run s)) :
    z.2.1.length ≤ s.1.length + if t.isRight = true then 1 else 0 := by
  rcases t with n | q
  · rw [passthrough_add_inl_run] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨_, -, rfl⟩ := hz
    simp
  · rcases indepPermOracle_step q s z hz with h | ⟨_, h, -⟩
    · simp [h]
    · simp [h]

/-- Coins passed through keep a domination of permutation oracles until bad.

Beside the coins, an oracle dominated by the lazy permutation stays dominated by it. -/
theorem dominatedUntilBad_passthrough_add {σ : Type}
    {perm : QueryImpl (PermSpec A) (StateT σ ProbComp)} {f : σ → PermCache A}
    {inv bad : σ → Prop} (h : QueryImpl.DominatedUntilBad perm lazyPermOracle f inv bad) :
    QueryImpl.DominatedUntilBad (unifSpec.passthrough + perm) lazyPermImpl f inv bad := by
  rintro (n | t) s hs hb Q
  · rw [passthrough_add_inl_run, passthrough_add_inl_run, prEvent_map, prEvent_map]
    exact prEvent_mono _ _ _ fun _ h => h.1
  · exact h t s hs hb Q

/-- With no flag raised, each step of the lazy permutation dominates the step here.

Read the state here through its cache, and count only the outcomes that raise no flag. -/
theorem dominatedUntilBad_indepPermImpl :
    QueryImpl.DominatedUntilBad (indepPermImpl (A := A)) lazyPermImpl Prod.fst (fun _ => True)
      fun s => s.2 = true := by
  refine dominatedUntilBad_passthrough_add ?_
  rintro (a | b) ⟨c, f⟩ - hf P
  · rw [indepPermOracle_inl_run, lazyPermOracle_inl_run]
    simp only [Bool.not_eq_true] at hf
    cases c.lookup a with
    | some b => exact prEvent_pure_le_pure _ _ _ _ fun h => h.1
    | none =>
      simp only [prEvent_map, hf, Bool.false_or, decide_eq_true_eq]
      exact prEvent_uniformOutside_nil_and_notMem_le _ a a _
  · rw [indepPermOracle_inr_run, lazyPermOracle_inr_run]
    simp only [Bool.not_eq_true] at hf
    cases (c.map Prod.swap).lookup b with
    | some a => exact prEvent_pure_le_pure _ _ _ _ fun h => h.1
    | none =>
      simp only [prEvent_map, hf, Bool.false_or, decide_eq_true_eq]
      exact prEvent_uniformOutside_nil_and_notMem_le _ b b _

/-- A step that adds a pair raises the flag with chance at most the cache size over `|A|`. -/
theorem badOnGrowthBy_indepPermImpl :
    BadOnGrowthBy (indepPermImpl (A := A)) (fun s => s.1.length) (fun s => s.2 = true)
      fun k => (k : ℝ≥0∞) / FinEnum.card A := by
  refine ⟨fun t s z hz => ?_, fun t s hs => ?_⟩
  · rcases t with n | q
    · rw [passthrough_add_inl_run] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨_, -, rfl⟩ := hz
      exact le_rfl
    · rcases indepPermOracle_step q s z hz with h | ⟨_, h, -⟩
      · rw [h]
      · simp [h]
  obtain ⟨c, f⟩ := s
  simp only [Bool.not_eq_true] at hs
  subst hs
  rcases t with n | a | b
  · left
    intro z hz
    rw [passthrough_add_inl_run] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨_, -, rfl⟩ := hz
    simp
  · rw [indepPermImpl_inr, indepPermOracle_inl_run]
    cases c.lookup a with
    | some b => exact Or.inl fun z hz => by simp_all
    | none =>
      refine Or.inr ⟨fun z hz => ?_, ?_⟩
      · simp only [support_map, Set.mem_image] at hz
        obtain ⟨_, -, rfl⟩ := hz
        simp
      · simp only [prEvent_map, Bool.false_or, decide_eq_true_eq]
        refine (prEvent_uniformOutside_nil_mem_le (c.map Prod.snd) a).trans ?_
        rw [List.length_map]
  · rw [indepPermImpl_inr, indepPermOracle_inr_run]
    cases (c.map Prod.swap).lookup b with
    | some a => exact Or.inl fun z hz => by simp_all
    | none =>
      refine Or.inr ⟨fun z hz => ?_, ?_⟩
      · simp only [support_map, Set.mem_image] at hz
        obtain ⟨_, -, rfl⟩ := hz
        simp
      · simp only [prEvent_map, Bool.false_or, decide_eq_true_eq]
        refine (prEvent_uniformOutside_nil_mem_le (c.map Prod.fst) b).trans ?_
        rw [List.length_map]

omit [FinEnum A] in
/-- The sum of `i / N` for `i < Q` is the number of pairs among `Q` values over `N`. -/
theorem sum_range_natCast_div (Q : ℕ) (N : ℝ≥0∞) :
    ∑ i ∈ Finset.range Q, (i : ℝ≥0∞) / N = (Q.choose 2 : ℝ≥0∞) / N := by
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum, Finset.sum_range_id, Nat.choose_two_right]

/-- **The birthday bound between a random permutation and independent answers.**

Take a run that asks the permutation, in either direction, at most `Q` times.

Compare an event of its output under the lazy permutation with the event under independent answers.

Both runs start from the empty cache, and the second counts only runs that raise no flag.

The first chance exceeds the second by at most `Q (Q - 1) / 2` over `|A|`. -/
theorem prEvent_lazyPermImpl_le_indepPermImpl {α : Type} (oa : PermComp A α) {Q : ℕ}
    (hQ : IsQueryBoundP oa (·.isRight = true) Q) (P : α → Prop) :
    Pr{let z ← (simulateQ lazyPermImpl oa).run' []}[P z] ≤
      Pr{let z ← (simulateQ indepPermImpl oa).run ([], false)}[P z.1 ∧ z.2.2 = false] +
        (Q.choose 2 : ℝ≥0∞) / FinEnum.card A := by
  rw [StateT.run'_eq, prEvent_map]
  refine (dominatedUntilBad_indepPermImpl.prEvent_simulateQ_run_le_map_or_bad
    (fun _ _ _ _ _ => trivial) indepPermImpl_preservesInv_flag oa ([], false) trivial
    fun z => P z.1).trans ?_
  have hn : ∀ z ∈ support ((simulateQ indepPermImpl oa).run ([], false)), z.2.1.length ≤ Q := by
    intro z hz
    have := hQ.cost_le_of_mem_support_run_simulateQ (impl := indepPermImpl)
      (fun s => s.1.length)
      (fun t ht s w hw => by simpa [ht] using length_le_of_mem_support_indepPermImpl t s w hw)
      (fun t ht s w hw => by simpa [ht] using length_le_of_mem_support_indepPermImpl t s w hw)
      ([], false) z hz
    simpa using this
  have hbad := badOnGrowthBy_indepPermImpl.prEvent_bad_le oa ([], false) (by simp) hn
  rw [show List.length ([] : PermCache A) = 0 from rfl, ← Finset.range_eq_Ico,
    sum_range_natCast_div] at hbad
  refine (prEvent_mono _ _ (fun z => (P z.1 ∧ z.2.2 = false) ∨ z.2.2 = true) fun z h => ?_).trans
    ((prEvent_or_le _ _ _).trans (add_le_add le_rfl hbad))
  cases hb : z.2.2 <;> simp_all

end EthLib.Cryptography.LazyPermutation
