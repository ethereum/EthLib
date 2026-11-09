module

public import VCVio.OracleComp.SimSemantics.StateT.UntilBad
public import VCVio.EvalDist.ProbabilityBounds
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Proofs: a handler that records the keys of its queries

A handler answers each query, and records a key for each query that has one.

Two handlers that agree on every query whose key is not `k` give the same run until `k` is recorded.

So an event of one run, with `k` never recorded, has at most its mass in the other run.

Recording changes no answer, and a run of at most `q` keyed queries records at most `q` keys.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal

namespace EthLib.Cryptography

/-! ## Two handlers that differ only at one key -/

section LogKeys

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {K : Type} [DecidableEq K]

/-- Answer each query with a handler, and record the key of each query that has one. -/
def logKeys (impl : QueryImpl spec (OracleComp spec')) (key : spec.Domain → Option K) :
    QueryImpl spec (StateT (Finset K) (OracleComp spec')) := fun t =>
  StateT.mk fun S => (fun u => (u, S ∪ (key t).toFinset)) <$> impl t

/-- **Identical until a key is recorded.**

Two handlers answer alike every query whose key is not `k`.

Both are run over a second, stateful handler, such as a random oracle.

An event of the first run, with `k` never recorded, has at most its mass in the second run. -/
theorem prEvent_logKeys_le {τ : Type} (ro : QueryImpl spec' (StateT τ ProbComp))
    {impl₁ impl₂ : QueryImpl spec (OracleComp spec')} {key : spec.Domain → Option K} {k : K}
    (hagree : ∀ t, key t ≠ some k → impl₁ t = impl₂ t)
    {α : Type} (oa : OracleComp spec α) (S : Finset K) (s : τ) (P : α → Prop) :
    Pr{let z ← (simulateQ ro ((simulateQ (logKeys impl₁ key) oa).run S)).run' s}[
        P z.1 ∧ k ∉ z.2]
      ≤ Pr{let z ← (simulateQ ro (simulateQ impl₂ oa)).run' s}[P z] := by
  let aux : (t : spec.Domain) → τ → spec.Range t → τ → Finset K → Finset K :=
    fun t _ _ _ S => S ∪ (key t).toFinset
  have hflat : ∀ impl : QueryImpl spec (OracleComp spec'),
      (ro.mapStateTBase (logKeys impl key)).flattenStateT = (ro ∘ₛ impl).extendStateLeft aux := by
    intro impl
    funext t
    refine StateT.ext fun st => ?_
    simp [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, logKeys, aux,
      QueryImpl.apply_compose, map_eq_bind_pure_comp]
  let bad : Finset K × τ → Prop := fun st => k ∈ st.1
  have hsupp : ∀ (impl : QueryImpl spec (OracleComp spec')) t st z,
      z ∈ support (((ro ∘ₛ impl).extendStateLeft aux t).run st) →
        z.2.1 = st.1 ∪ (key t).toFinset := by
    intro impl t st z hz
    simp only [QueryImpl.extendStateLeft_apply, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨p, -, rfl⟩ := hz
    rfl
  have hagree' : QueryImpl.AgreeUntilBad ((ro ∘ₛ impl₁).extendStateLeft aux)
      ((ro ∘ₛ impl₂).extendStateLeft aux) bad := by
    refine QueryImpl.AgreeUntilBad.of_run_eq_or_bad fun t st _ => ?_
    by_cases hk : key t = some k
    · refine .inr ⟨fun z hz => ?_, fun z hz => ?_⟩ <;>
        simp [bad, hsupp _ t st z hz, hk]
    · left
      simp only [QueryImpl.extendStateLeft_apply, QueryImpl.apply_compose, hagree t hk]
  have hpres : QueryImpl.PreservesInv ((ro ∘ₛ impl₁).extendStateLeft aux) bad :=
    fun t st hst z hz => by
      simp only [bad, hsupp _ t st z hz, Finset.mem_union]
      exact Or.inl hst
  have h := hagree'.prEvent_simulateQ_run_and_not_bad_le hpres oa (S, s) fun z => P z.1
  rw [StateT.run'_eq, simulateQ_mapStateTBase_run_eq_map_flattenStateT, hflat,
    ← QueryImpl.simulateQ_compose, StateT.run'_eq,
    ← extendStateLeft_run_proj_eq (ro ∘ₛ impl₂) aux oa s S]
  simpa [Functor.map_map, Function.comp_def, bad] using h

/-- Recording the keys of the queries leaves the answers of a handler unchanged. -/
theorem fst_map_run_simulateQ_logKeys
    (impl : QueryImpl spec (OracleComp spec')) (key : spec.Domain → Option K) {α : Type}
    (oa : OracleComp spec α) (s : Finset K) :
    Prod.fst <$> (simulateQ (logKeys impl key) oa).run s = simulateQ impl oa := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    simp [simulateQ_bind, StateT.run_bind, logKeys, map_bind, ih]

/-- A run of at most `q` keyed queries records at most `q` new keys. -/
theorem card_le_of_mem_support_run_logKeys
    (impl : QueryImpl spec (OracleComp spec')) {key : spec.Domain → Option K}
    {p : spec.Domain → Prop} [DecidablePred p] (hkey : ∀ t, ¬ p t → key t = none) {α : Type}
    {oa : OracleComp spec α} {q : ℕ} (hq : IsQueryBoundP oa p q) (s : Finset K)
    {z : α × Finset K} (hz : z ∈ support ((simulateQ (logKeys impl key) oa).run s)) :
    z.2.card ≤ s.card + q := by
  induction oa using OracleComp.inductionOn generalizing s q with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Nat.le_add_right _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    simp only [simulateQ_bind, simulateQ_query, StateT.run_bind, logKeys] at hz
    simp at hz
    obtain ⟨u, -, hz⟩ := hz
    have h := ih u (hq.2 u) _ hz
    by_cases ht : p t
    · have hq0 : 0 < q := hq.1.resolve_left (not_not.mpr ht)
      rw [ite_eq_left ht] at h
      have h1 : (key t).toFinset.card ≤ 1 := by cases key t <;> simp
      have := Finset.card_union_le s (key t).toFinset
      omega
    · rwa [ite_eq_right ht, hkey t ht, Option.toFinset_none, Finset.union_empty] at h

/-- The handler that passes each sampling query on, with no state. -/
def liftUnif : QueryImpl unifSpec (StateT Unit ProbComp) :=
  fun n => StateT.lift (unifSpec.query n)

/-- Passing each sampling query on, with no state, leaves a program unchanged. -/
theorem run'_simulateQ_liftUnif {α : Type} (x : ProbComp α) (u : Unit) :
    (simulateQ liftUnif x).run' u = x := by
  induction x using OracleComp.inductionOn generalizing u with
  | pure a => simp
  | query_bind t k ih =>
    simp only [liftUnif, StateT.run'_eq, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      StateT.run_lift, bind_assoc, pure_bind, map_bind] at *
    exact bind_congr fun a => ih a u

/-- Let two handlers into probabilistic programs agree away from key `k`.

An event of the first run, with `k` never recorded, has at most its mass in the second run. -/
theorem prEvent_run_logKeys_le {impl₁ impl₂ : QueryImpl spec ProbComp}
    {key : spec.Domain → Option K} {k : K} (hagree : ∀ t, key t ≠ some k → impl₁ t = impl₂ t)
    {α : Type} (oa : OracleComp spec α) (S : Finset K) (P : α → Prop) :
    Pr{let z ← (simulateQ (logKeys impl₁ key) oa).run S}[P z.1 ∧ k ∉ z.2]
      ≤ Pr{let z ← simulateQ impl₂ oa}[P z] := by
  have h := prEvent_logKeys_le liftUnif hagree oa S () P
  rwa [run'_simulateQ_liftUnif, run'_simulateQ_liftUnif] at h

end LogKeys

end EthLib.Cryptography
