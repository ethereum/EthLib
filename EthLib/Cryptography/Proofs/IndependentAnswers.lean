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

The swap is the step from Game G0 to Game G1 in the proof of their Theorem 2.

Their bound there is `Q² / 2^L`; the bound here is half of it, or less.
-/

@[expose] public section

namespace EthLib.Cryptography.LazyPermutation

open OracleComp OracleSpec ENNReal

variable {A : Type} [FinEnum A]

/-! ## Uniform draws that avoid a list -/

/-- A draw from a nonempty list has the chance of an event as the share of the list in it. -/
theorem prEvent_uniformFrom_eq_countP {X : Type} {l : List X} (hl : l ≠ []) (d : X)
    (p : X → Prop) [DecidablePred p] :
    Pr{let y ← uniformFrom l d}[p y] = (l.countP (fun y => decide (p y)) : ℝ≥0∞) / l.length := by
  cases l with
  | nil => exact absurd rfl hl
  | cons b bs =>
    rw [uniformFrom, ProbComp.prEvent_uniformSelectListVector]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    rfl

/-- A uniform value of `A` that avoids a list puts at least the mass of a uniform value of `A`.

This holds for each event, and the uniform value of `A` counts only when it avoids the list. -/
theorem prEvent_uniformOutside_nil_and_notMem_le (used : List A) (d d' : A) (p : A → Prop) :
    Pr{let y ← uniformOutside [] d}[p y ∧ y ∉ used] ≤
      Pr{let y ← uniformOutside used d'}[p y] := by
  classical
  have hne : FinEnum.toList A ≠ [] := List.ne_nil_of_mem (FinEnum.mem_toList d)
  have hcount : (FinEnum.toList A).countP (fun y => decide (p y ∧ y ∉ used)) =
      ((FinEnum.toList A).filter fun b => b ∉ used).countP (fun y => decide (p y)) := by
    rw [List.countP_filter]
    simp only [Bool.decide_and]
  have hnil : ((FinEnum.toList A).filter fun b => b ∉ []) = FinEnum.toList A := by simp
  rw [uniformOutside, hnil, prEvent_uniformFrom_eq_countP hne d, hcount]
  by_cases hf : ((FinEnum.toList A).filter fun b => b ∉ used) = []
  · rw [hf]
    simp
  · rw [uniformOutside, prEvent_uniformFrom_eq_countP hf d']
    exact ENNReal.div_le_div_left (by exact_mod_cast List.length_filter_le _ _) _

/-- A uniform value of `A` lies in a list with chance at most its length over `|A|`. -/
theorem prEvent_uniformOutside_nil_mem_le (used : List A) (d : A) :
    Pr{let y ← uniformOutside [] d}[y ∈ used] ≤ (used.length : ℝ≥0∞) / FinEnum.card A := by
  have hne : FinEnum.toList A ≠ [] := List.ne_nil_of_mem (FinEnum.mem_toList d)
  have hnil : ((FinEnum.toList A).filter fun b => b ∉ []) = FinEnum.toList A := by simp
  rw [uniformOutside, hnil, prEvent_uniformFrom_eq_countP hne d]
  have hlen : (FinEnum.toList A).length = FinEnum.card A := by simp [FinEnum.toList]
  rw [hlen]
  refine ENNReal.div_le_div_right ?_ _
  rw [List.countP_eq_length_filter]
  exact_mod_cast ((List.subperm_of_subset ((FinEnum.nodup_toList).filter _)
    fun y hy => by simpa using (List.mem_filter.1 hy).2).length_le)

/-! ## The oracle -/

/-- The state: the pairs answered so far, the most recent first, and the flag. -/
abbrev IndepState (A : Type) := PermCache A × Bool

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
    | none => (fun b => (b, ((a, b) :: s.1, s.2 || decide (b ∈ s.1.map Prod.snd)))) <$>
      (uniformOutside [] a : ProbComp A)
  | .inr b => fun s =>
    match (s.1.map Prod.swap).lookup b with
    | some a => pure (a, s)
    | none => (fun a => (a, ((a, b) :: s.1, s.2 || decide (a ∈ s.1.map Prod.fst)))) <$>
      (uniformOutside [] b : ProbComp A)

/-- The oracles with independent answers: coins, passed through, then the oracle above. -/
abbrev indepPermImpl : QueryImpl (unifSpec + PermSpec A) (StateT (IndepState A) ProbComp) :=
  unifSpec.passthrough + indepPermOracle

omit [FinEnum A] in
/-- Coins pass through an oracle of the permutation, and leave its state unchanged. -/
theorem passthrough_add_inl_run {σ : Type} (perm : QueryImpl (PermSpec A) (StateT σ ProbComp))
    (n : ℕ) (s : σ) :
    ((unifSpec.passthrough + perm) (.inl n)).run s =
      (·, s) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1))) := by
  simp [StateT.run_monadLift]

/-- A query of the permutation keeps the state, or adds one pair and keeps a raised flag. -/
theorem indepPermOracle_step (q : (PermSpec A).Domain) (s : IndepState A) (z)
    (hz : z ∈ support ((indepPermOracle q).run s)) :
    z.2 = s ∨ ∃ p, z.2.1 = p :: s.1 ∧ (s.2 = true → z.2.2 = true) := by
  rcases q with a | b
  · change z ∈ support (match s.1.lookup a with
      | some b => pure (b, s)
      | none => (fun b => (b, ((a, b) :: s.1, s.2 || decide (b ∈ s.1.map Prod.snd)))) <$>
        (uniformOutside [] a : ProbComp A)) at hz
    split at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      exact Or.inl (by rw [hz])
    · simp only [support_map, Set.mem_image] at hz
      obtain ⟨b, -, rfl⟩ := hz
      exact Or.inr ⟨(a, b), rfl, fun h => by simp [h]⟩
  · change z ∈ support (match (s.1.map Prod.swap).lookup b with
      | some a => pure (a, s)
      | none => (fun a => (a, ((a, b) :: s.1, s.2 || decide (a ∈ s.1.map Prod.fst)))) <$>
        (uniformOutside [] b : ProbComp A)) at hz
    split at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      exact Or.inl (by rw [hz])
    · simp only [support_map, Set.mem_image] at hz
      obtain ⟨a, -, rfl⟩ := hz
      exact Or.inr ⟨(a, b), rfl, fun h => by simp [h]⟩

/-- Once raised, the flag stays. -/
theorem indepPermImpl_preservesInv_flag :
    QueryImpl.PreservesInv (indepPermImpl (A := A)) fun s => s.2 = true := by
  rintro (n | q) s hs z hz
  · rw [passthrough_add_inl_run] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨_, -, rfl⟩ := hz
    exact hs
  · rcases indepPermOracle_step q s z hz with h | ⟨_, -, h⟩
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

/-- With no flag raised, each step of the lazy permutation dominates the step here.

Read the state here through its cache, and count only the outcomes that raise no flag. -/
theorem dominatedUntilBad_indepPermImpl :
    QueryImpl.DominatedUntilBad (indepPermImpl (A := A)) lazyPermImpl Prod.fst (fun _ => True)
      fun s => s.2 = true := by
  rintro (n | a | b) ⟨c, f⟩ - hf P
  · rw [passthrough_add_inl_run, passthrough_add_inl_run, prEvent_map, prEvent_map]
    exact prEvent_mono _ _ _ fun _ h => h.1
  · change Pr{let z ← (match c.lookup a with
        | some b => pure (b, (c, f))
        | none => (fun b => (b, ((a, b) :: c, f || decide (b ∈ c.map Prod.snd)))) <$>
          (uniformOutside [] a : ProbComp A))}[P (z.1, z.2.1) ∧ ¬z.2.2 = true] ≤
      Pr{let z ← (match c.lookup a with
        | some b => pure (b, c)
        | none => (fun b => (b, (a, b) :: c)) <$>
          (uniformOutside (c.map Prod.snd) a : ProbComp A))}[P z]
    simp only [Bool.not_eq_true] at hf
    cases c.lookup a with
    | some b => exact prEvent_pure_le_pure _ _ _ _ fun h => h.1
    | none =>
      simp only [prEvent_map, hf, Bool.false_or, decide_eq_true_eq]
      exact prEvent_uniformOutside_nil_and_notMem_le _ a a _
  · change Pr{let z ← (match (c.map Prod.swap).lookup b with
        | some a => pure (a, (c, f))
        | none => (fun a => (a, ((a, b) :: c, f || decide (a ∈ c.map Prod.fst)))) <$>
          (uniformOutside [] b : ProbComp A))}[P (z.1, z.2.1) ∧ ¬z.2.2 = true] ≤
      Pr{let z ← (match (c.map Prod.swap).lookup b with
        | some a => pure (a, c)
        | none => (fun a => (a, (a, b) :: c)) <$>
          (uniformOutside (c.map Prod.fst) b : ProbComp A))}[P z]
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
  · change (∀ z ∈ support (match c.lookup a with
        | some b => pure (b, (c, false))
        | none => (fun b => (b, ((a, b) :: c, false || decide (b ∈ c.map Prod.snd)))) <$>
          (uniformOutside [] a : ProbComp A)), _) ∨
      ((∀ z ∈ support (match c.lookup a with
        | some b => pure (b, (c, false))
        | none => (fun b => (b, ((a, b) :: c, false || decide (b ∈ c.map Prod.snd)))) <$>
          (uniformOutside [] a : ProbComp A)), _) ∧
        Pr{let z ← (match c.lookup a with
        | some b => pure (b, (c, false))
        | none => (fun b => (b, ((a, b) :: c, false || decide (b ∈ c.map Prod.snd)))) <$>
          (uniformOutside [] a : ProbComp A))}[z.2.2 = true] ≤ _)
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
  · change (∀ z ∈ support (match (c.map Prod.swap).lookup b with
        | some a => pure (a, (c, false))
        | none => (fun a => (a, ((a, b) :: c, false || decide (a ∈ c.map Prod.fst)))) <$>
          (uniformOutside [] b : ProbComp A)), _) ∨
      ((∀ z ∈ support (match (c.map Prod.swap).lookup b with
        | some a => pure (a, (c, false))
        | none => (fun a => (a, ((a, b) :: c, false || decide (a ∈ c.map Prod.fst)))) <$>
          (uniformOutside [] b : ProbComp A)), _) ∧
        Pr{let z ← (match (c.map Prod.swap).lookup b with
        | some a => pure (a, (c, false))
        | none => (fun a => (a, ((a, b) :: c, false || decide (a ∈ c.map Prod.fst)))) <$>
          (uniformOutside [] b : ProbComp A))}[z.2.2 = true] ≤ _)
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

/-- The sum of `i / |A|` for `i < Q` is the number of pairs among `Q` over `|A|`. -/
theorem sum_range_div_card (Q : ℕ) :
    ∑ i ∈ Finset.Ico 0 Q, (i : ℝ≥0∞) / FinEnum.card A = (Q.choose 2 : ℝ≥0∞) / FinEnum.card A := by
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum, ← Finset.range_eq_Ico, Finset.sum_range_id,
    Nat.choose_two_right]

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
  rw [show List.length ([] : PermCache A) = 0 from rfl, sum_range_div_card] at hbad
  refine (prEvent_mono _ _ (fun z => (P z.1 ∧ z.2.2 = false) ∨ z.2.2 = true) fun z h => ?_).trans
    ((prEvent_or_le _ _ _).trans (add_le_add le_rfl hbad))
  cases hb : z.2.2 <;> simp_all

end EthLib.Cryptography.LazyPermutation
