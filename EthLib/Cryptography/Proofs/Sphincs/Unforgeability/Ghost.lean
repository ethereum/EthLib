module

public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Proofs: queries whose answers are thrown away

A program may ask the random oracle at a point and throw the answer away.

Such a query still fills the cache, so a later query at that point reads the same answer.

That answer was uniform and nobody saw it, so a fresh answer has the same law.

So the query can be dropped: the outputs keep their law.

The final caches keep their law too, once the points where such queries may happen are erased.

This holds in the ideal game of VCVio's hidden-seed games, for every public oracle.

A thrown-away query is a query of its own kind, a ghost query, at a point of a set `p`.

One run asks the oracle at each ghost query, the other skips it.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability

open OracleSpec OracleComp

variable {ι : Type} {pub : OracleSpec ι} {X R : Type} (p : ι → Prop)

/-- The world with derivations, and ghost queries at the points of `p`, answered by nothing. -/
abbrev GhostWorld (pub : OracleSpec ι) (X R : Type) (p : ι → Prop) :=
  pub.withDerivations X R + ({t // p t} →ₒ Unit)

/-- Ask the oracle at each ghost query, and throw the answer away. -/
def askGhost : QueryImpl (GhostWorld pub X R p) (OracleComp (pub.withDerivations X R))
  | .inl t => (pub.withDerivations X R).query t
  | .inr t => do
      let _ ← (pub.withDerivations X R).query (.inl (.inr t.1))
      return ()

/-- Skip each ghost query. -/
def skipGhost : QueryImpl (GhostWorld pub X R p) (OracleComp (pub.withDerivations X R))
  | .inl t => (pub.withDerivations X R).query t
  | .inr _ => pure ()

open Classical in
/-- A state of the ideal game with its public cache erased at the points of `p`. -/
noncomputable def eraseGhosts (st : SecretEncoding.SplitCache pub X R) :
    SecretEncoding.SplitCache pub X R :=
  (.ofFn fun t => if p t then none else st.1 t, st.2)

/-- A point of `p` cached in the public cache is erased with the others. -/
theorem eraseGhosts_cacheQuery [DecidableEq ι] {t : ι} (ht : p t) (C : pub.QueryCache)
    (T : (X →ₒ R).QueryCache) (u : pub.Range t) :
    eraseGhosts p (C.cacheQuery t u, T) = eraseGhosts p (C, T) := by
  refine Prod.ext (QueryCache.ext fun t' => ?_) rfl
  by_cases h : t' = t
  · subst h
    simp [eraseGhosts, QueryCache.ofFn_apply, ht]
  · simp [eraseGhosts, QueryCache.ofFn_apply, QueryCache.cacheQuery_of_ne _ _ h]

variable [DecidableEq ι] [DecidableEq X] [∀ t, SampleableType (pub.Range t)] [SampleableType R]

local notation "I" => SecretEncoding.idealImpl pub X R

/-- The ideal game answers a sampling query and keeps its state. -/
theorem idealImpl_run_unif (n : ℕ) (st : SecretEncoding.SplitCache pub X R) :
    (I (.inl (.inl n))).run st = (fun v => (v, st)) <$> (unifSpec.query n : ProbComp _) :=
  rfl

/-- The ideal game reads a cached public answer. -/
theorem idealImpl_run_pub_some' {C : pub.QueryCache} {T : (X →ₒ R).QueryCache} {t : ι}
    {v : pub.Range t} (h : C t = some v) :
    (I (.inl (.inr t))).run (C, T) = pure (v, (C, T)) :=
  SecretEncoding.idealImpl_run_pub_some (st := (C, T)) h

/-- The ideal game draws and caches an uncached public answer. -/
theorem idealImpl_run_pub_none' {C : pub.QueryCache} {T : (X →ₒ R).QueryCache} {t : ι}
    (h : C t = none) :
    (I (.inl (.inr t))).run (C, T) = (fun u => (u, (C.cacheQuery t u, T))) <$> ($ᵗ pub.Range t) :=
  SecretEncoding.idealImpl_run_pub_none (st := (C, T)) h

/-- The ideal game reads a drawn derivation. -/
theorem idealImpl_run_derive_some' {C : pub.QueryCache} {T : (X →ₒ R).QueryCache} {x : X} {v : R}
    (h : T x = some v) : (I (.inr x)).run (C, T) = pure (v, (C, T)) :=
  SecretEncoding.idealImpl_run_derive_some (st := (C, T)) h

/-- The ideal game draws and stores an undrawn derivation. -/
theorem idealImpl_run_derive_none' {C : pub.QueryCache} {T : (X →ₒ R).QueryCache} {x : X}
    (h : T x = none) :
    (I (.inr x)).run (C, T) = (fun u => (u, (C, T.cacheQuery x u))) <$> ($ᵗ R) :=
  SecretEncoding.idealImpl_run_derive_none (st := (C, T)) h

/-- **An unseen answer at a ghost point.**

Caching a uniform answer at an uncached point of `p` before a run changes nothing.

The output and the erased final state keep their law. -/
theorem run_cacheQuery_ghost_evalDistEq {α : Type} (ob : OracleComp (pub.withDerivations X R) α)
    {t : ι} (ht : p t) (C : pub.QueryCache) (T : (X →ₒ R).QueryCache) (hC : C t = none) :
    (do
      let u ← $ᵗ pub.Range t
      Prod.map id (eraseGhosts p) <$> (simulateQ I ob).run (C.cacheQuery t u, T)) =ᵈ
      Prod.map id (eraseGhosts p) <$> (simulateQ I ob).run (C, T) := by
  induction ob using OracleComp.inductionOn generalizing C T with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map, id_eq,
      eraseGhosts_cacheQuery p ht]
    exact EvalDistEq.bind_const _ _
  | query_bind q k ih =>
    rcases q with (n | t') | x
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      simp only [idealImpl_run_unif, bind_map_left]
      exact (EvalDistEq.bind_bind_swap _ _ _).trans
        (EvalDistEq.bind_right _ fun v => ih v C T hC)
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      by_cases htt : t' = t
      · subst htt
        simp only [idealImpl_run_pub_some' (QueryCache.cacheQuery_self C t' _),
          idealImpl_run_pub_none' hC, pure_bind, bind_map_left]
        exact EvalDistEq.rfl
      · cases hC' : C t' with
        | some w =>
          have hw : ∀ u, (C.cacheQuery t u) t' = some w := fun _ =>
            (QueryCache.cacheQuery_of_ne _ _ htt).trans hC'
          simp only [idealImpl_run_pub_some' (hw _), idealImpl_run_pub_some' hC', pure_bind]
          exact ih w C T hC
        | none =>
          simp only [idealImpl_run_pub_none' ((QueryCache.cacheQuery_of_ne _ _ htt).trans hC'),
            idealImpl_run_pub_none' hC', bind_map_left]
          refine (EvalDistEq.bind_bind_swap _ _ _).trans
            (EvalDistEq.bind_right _ fun v => ?_)
          simp only [QueryCache.cacheQuery_comm _ (Ne.symm htt)]
          exact ih v (C.cacheQuery t' v) T
            ((QueryCache.cacheQuery_of_ne _ _ (Ne.symm htt)).trans hC)
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      cases hT : T x with
      | some w =>
        simp only [idealImpl_run_derive_some' hT, pure_bind]
        exact ih w C T hC
      | none =>
        simp only [idealImpl_run_derive_none' hT, bind_map_left]
        exact (EvalDistEq.bind_bind_swap _ _ _).trans
          (EvalDistEq.bind_right _ fun v => ih v C (T.cacheQuery x v) hC)

/-- **Dropping the ghost queries.**

Asking the oracle at each ghost query, or skipping it, gives the same law.

This is the law of the output and of the final state, erased at the points of `p`. -/
theorem run_askGhost_evalDistEq_skipGhost {α : Type} (oa : OracleComp (GhostWorld pub X R p) α)
    (st : SecretEncoding.SplitCache pub X R) :
    Prod.map id (eraseGhosts p) <$> (simulateQ I (simulateQ (askGhost p) oa)).run st =ᵈ
      Prod.map id (eraseGhosts p) <$> (simulateQ I (simulateQ (skipGhost p) oa)).run st := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure x => exact EvalDistEq.rfl
  | query_bind q k ih =>
    rcases q with q | g
    · simp only [simulateQ_bind, simulateQ_spec_query, askGhost, skipGhost, StateT.run_bind,
        map_bind]
      exact EvalDistEq.bind_right _ fun z => ih z.1 z.2
    · obtain ⟨C, T⟩ := st
      simp only [simulateQ_bind, simulateQ_spec_query, askGhost, skipGhost, bind_assoc,
        pure_bind, StateT.run_bind, map_bind]
      cases hC : C g.1 with
      | some w =>
        simp only [idealImpl_run_pub_some' hC, pure_bind]
        exact ih () (C, T)
      | none =>
        simp only [idealImpl_run_pub_none' hC, bind_map_left]
        exact (run_cacheQuery_ghost_evalDistEq p _ g.2 C T hC).trans (ih () (C, T))

/-- **Dropping the ghost queries, for an event of the output.**

From the empty state, asking or skipping each ghost query gives the event the same chance. -/
theorem prEvent_askGhost_eq_skipGhost {α : Type} (oa : OracleComp (GhostWorld pub X R p) α)
    (P : α → Prop) :
    Pr{let z ← (simulateQ I (simulateQ (askGhost p) oa)).run (∅, ∅)}[P z.1] =
      Pr{let z ← (simulateQ I (simulateQ (skipGhost p) oa)).run (∅, ∅)}[P z.1] := by
  have h := (run_askGhost_evalDistEq_skipGhost p oa (∅, ∅)).prEvent_eq fun z => P z.1
  simpa only [prEvent_map, Function.comp_def, Prod.map_fst, id_eq] using h

end EthLib.Cryptography.Sphincs.Unforgeability
