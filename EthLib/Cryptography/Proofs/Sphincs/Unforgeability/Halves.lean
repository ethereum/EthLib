module

public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Proofs: a random oracle asked half by half

A uniform answer of `R₂ ≃ R × R` is two independent uniform halves.

So a random oracle with answers in `R₂` can be replaced by one with answers in `R`.

Each old point becomes two new points: the point with half 0 and the point with half 1.

A query of the old oracle asks both halves, in order, and joins them.

This holds in the ideal game of VCVio's hidden-seed games.

It holds for the public oracle and the derivation table at once.

The two games then give the same output in distribution.

The halves of the old caches are the new caches.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability

open OracleSpec OracleComp

variable {A X R₂ R : Type}

/-- The world of halves: every public point and every derivation has two halves in `R`. -/
abbrev HalfWorld (A X R : Type) :=
  (A × Fin 2 →ₒ R).withDerivations (X × Fin 2) R

/-- Answer a query by asking its two halves, half 0 first, and joining them. -/
def halvesImpl (e : R₂ ≃ R × R) :
    QueryImpl ((A →ₒ R₂).withDerivations X R₂) (OracleComp (HalfWorld A X R))
  | .inl (.inl n) => (HalfWorld A X R).query (.inl (.inl n))
  | .inl (.inr a) => do
      let u ← (HalfWorld A X R).query (.inl (.inr (a, 0)))
      let v ← (HalfWorld A X R).query (.inl (.inr (a, 1)))
      return e.symm (u, v)
  | .inr x => do
      let u ← (HalfWorld A X R).query (.inr (x, 0))
      let v ← (HalfWorld A X R).query (.inr (x, 1))
      return e.symm (u, v)

/-- The halves of a cache: half `b` of a cached answer, at the point with half `b`. -/
def halfCache {B : Type} (e : R₂ ≃ R × R) (C : (B →ₒ R₂).QueryCache) :
    (B × Fin 2 →ₒ R).QueryCache :=
  .ofFn fun p => (C p.1).map fun w => if p.2 = 0 then (e w).1 else (e w).2

/-- The halves of the empty cache are empty. -/
@[simp] theorem halfCache_empty {B : Type} (e : R₂ ≃ R × R) :
    halfCache e (∅ : (B →ₒ R₂).QueryCache) = ∅ :=
  rfl

/-- At a cached point, the two halves are cached, and they join back to the answer. -/
theorem halfCache_apply_some {B : Type} (e : R₂ ≃ R × R) {C : (B →ₒ R₂).QueryCache} {b : B}
    {w : R₂} (h : C b = some w) :
    halfCache e C (b, 0) = some (e w).1 ∧ halfCache e C (b, 1) = some (e w).2 := by
  simp [halfCache, QueryCache.ofFn_apply, h]

/-- At a point not cached, neither half is cached. -/
theorem halfCache_apply_none {B : Type} (e : R₂ ≃ R × R) {C : (B →ₒ R₂).QueryCache} {b : B}
    (h : C b = none) (i : Fin 2) : halfCache e C (b, i) = none := by
  simp [halfCache, QueryCache.ofFn_apply, h]

/-- Caching the two halves of a point is caching the joined answer, then halving. -/
theorem halfCache_cacheQuery {B : Type} [DecidableEq B] (e : R₂ ≃ R × R)
    (C : (B →ₒ R₂).QueryCache) (b : B) (u v : R) :
    ((halfCache e C).cacheQuery (b, 0) u).cacheQuery (b, 1) v =
      halfCache e (C.cacheQuery b (e.symm (u, v))) := by
  refine QueryCache.ext fun ⟨b', i⟩ => ?_
  by_cases hb : b' = b
  · subst hb
    fin_cases i
    · simp [halfCache, QueryCache.ofFn_apply]
    · simp [halfCache, QueryCache.ofFn_apply]
  · have h0 : ((b', i) : B × Fin 2) ≠ (b, 0) := fun h => hb (Prod.ext_iff.1 h).1
    have h1 : ((b', i) : B × Fin 2) ≠ (b, 1) := fun h => hb (Prod.ext_iff.1 h).1
    change ((halfCache e C).cacheQuery (b, 0) u).cacheQuery (b, 1) v (b', i) = _
    rw [QueryCache.cacheQuery_of_ne _ _ h1, QueryCache.cacheQuery_of_ne _ _ h0]
    simp only [halfCache, QueryCache.ofFn_apply, QueryCache.cacheQuery_of_ne _ _ hb]

/-- The halves of a state of the ideal game: the halves of its public cache and of its table. -/
def halfState (e : R₂ ≃ R × R) (st : SecretEncoding.SplitCache (A →ₒ R₂) X R₂) :
    SecretEncoding.SplitCache (A × Fin 2 →ₒ R) (X × Fin 2) R :=
  (halfCache e st.1, halfCache e st.2)

/-- The halves of the empty state are empty. -/
@[simp] theorem halfState_empty (e : R₂ ≃ R × R) :
    halfState e ((∅, ∅) : SecretEncoding.SplitCache (A →ₒ R₂) X R₂) = (∅, ∅) :=
  rfl

variable [DecidableEq A] [DecidableEq X] [SampleableType R₂] [SampleableType R]

/-- Two uniform halves, joined, are a uniform answer. -/
theorem uniform_halves_evalDistEq (e : R₂ ≃ R × R) {β : Type} (f : R₂ → ProbComp β) :
    (do let u ← $ᵗ R; let v ← $ᵗ R; f (e.symm (u, v))) =ᵈ ($ᵗ R₂ >>= f) := by
  have h : (e.symm <$> ($ᵗ (R × R))) =ᵈ ($ᵗ R₂) :=
    SampleableType.map_uniformSample_evalDistEq_of_bijective e.symm.bijective
  have h' := EvalDistEq.bind_congr h (f := f) (g := f) fun _ => EvalDistEq.rfl
  rw [bind_map_left, SampleableType.uniformSample_prod_eq_bind] at h'
  simpa only [bind_assoc, pure_bind] using h'

/-- A run of the ideal game, from the halves of a state, with every query asked half by half.

In distribution, it gives the output of the run from the state itself.

Its final state is the halves of that run's final state. -/
theorem run_simulateQ_halvesImpl_evalDistEq (e : R₂ ≃ R × R) {α : Type}
    (oa : OracleComp ((A →ₒ R₂).withDerivations X R₂) α)
    (st : SecretEncoding.SplitCache (A →ₒ R₂) X R₂) :
    (simulateQ (SecretEncoding.idealImpl (A × Fin 2 →ₒ R) (X × Fin 2) R)
        (simulateQ (halvesImpl e) oa)).run (halfState e st) =ᵈ
      Prod.map id (halfState e) <$>
        (simulateQ (SecretEncoding.idealImpl (A →ₒ R₂) X R₂) oa).run st := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure x => simp [halfState]
  | query_bind t k ih =>
    obtain ⟨C, T⟩ := st
    rcases t with (n | a) | x
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, halvesImpl]
      simp only [SecretEncoding.idealImpl, StateT.run_mk, bind_map_left, map_bind]
      exact EvalDistEq.bind_congr EvalDistEq.rfl fun u => ih u (C, T)
    · cases hC : C a with
      | some w =>
        obtain ⟨h0, h1⟩ := halfCache_apply_some e hC
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, halvesImpl,
          bind_assoc, pure_bind, SecretEncoding.idealImpl, StateT.run_mk,
          randomOracle.run_eq, halfState, h0, h1, hC, map_pure, bind_map_left, pure_bind,
          Prod.mk.eta, Equiv.symm_apply_apply]
        exact ih w (C, T)
      | none =>
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, halvesImpl,
          bind_assoc, pure_bind, SecretEncoding.idealImpl, StateT.run_mk,
          randomOracle.run_eq, halfState, halfCache_apply_none e hC, hC, map_bind,
          bind_map_left, pure_bind]
        simp only [QueryCache.cacheQuery_of_ne _ _ (show ((a, 1) : A × Fin 2) ≠ (a, 0) by
            simp), halfCache_apply_none e hC, halfCache_cacheQuery, bind_assoc, pure_bind]
        refine EvalDistEq.trans ?_ (uniform_halves_evalDistEq e _)
        refine EvalDistEq.bind_congr EvalDistEq.rfl fun u =>
          EvalDistEq.bind_congr EvalDistEq.rfl fun v => ?_
        exact ih _ (C.cacheQuery a (e.symm (u, v)), T)
    · cases hT : T x with
      | some w =>
        obtain ⟨h0, h1⟩ := halfCache_apply_some e hT
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, halvesImpl,
          bind_assoc, pure_bind, SecretEncoding.idealImpl, StateT.run_mk,
          randomOracle.run_eq, halfState, h0, h1, hT, map_pure, bind_map_left, pure_bind,
          Prod.mk.eta, Equiv.symm_apply_apply]
        exact ih w (C, T)
      | none =>
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, halvesImpl,
          bind_assoc, pure_bind, SecretEncoding.idealImpl, StateT.run_mk,
          randomOracle.run_eq, halfState, halfCache_apply_none e hT, hT, map_bind,
          bind_map_left, pure_bind]
        simp only [QueryCache.cacheQuery_of_ne _ _ (show ((x, 1) : X × Fin 2) ≠ (x, 0) by
            simp), halfCache_apply_none e hT, halfCache_cacheQuery, bind_assoc, pure_bind]
        refine EvalDistEq.trans ?_ (uniform_halves_evalDistEq e _)
        refine EvalDistEq.bind_congr EvalDistEq.rfl fun u =>
          EvalDistEq.bind_congr EvalDistEq.rfl fun v => ?_
        exact ih _ (C, T.cacheQuery x (e.symm (u, v)))

/-- **Asking half by half.**

An event of the output of the ideal game, from the empty state, keeps its probability.

This holds when every query is asked half by half. -/
theorem prEvent_idealImpl_halvesImpl (e : R₂ ≃ R × R) {α : Type}
    (oa : OracleComp ((A →ₒ R₂).withDerivations X R₂) α) (P : α → Prop) :
    Pr{let z ← (simulateQ (SecretEncoding.idealImpl (A × Fin 2 →ₒ R) (X × Fin 2) R)
        (simulateQ (halvesImpl e) oa)).run (∅, ∅)}[P z.1] =
      Pr{let z ← (simulateQ (SecretEncoding.idealImpl (A →ₒ R₂) X R₂) oa).run (∅, ∅)}[P z.1] := by
  have h := (run_simulateQ_halvesImpl_evalDistEq e oa (∅, ∅)).prEvent_eq fun z => P z.1
  rw [halfState_empty] at h
  rw [h, prEvent_map]
  rfl

end EthLib.Cryptography.Sphincs.Unforgeability
