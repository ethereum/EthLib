module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.HiddenSeed
public import EthLib.Cryptography.Proofs.EvalDistEq
public import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

/-!
# Proofs: a table of derivations, drawn lazily or eagerly

In the ideal hidden-seed game, each derivation is drawn uniformly on its first query.

Drawing the whole table first and answering from it gives the same distribution.
-/

@[expose] public section

namespace EthLib.Cryptography

open OracleSpec OracleComp

variable {ι : Type} {pub : OracleSpec ι} [DecidableEq ι] [∀ t, SampleableType (pub.Range t)]
  {X R : Type} [DecidableEq X] [Finite X] [SampleableType R] [SampleableType (X → R)]

/-- Answer each derivation from a table, and pass every other query on. -/
def fixDerivations (f : X → R) :
    QueryImpl (pub.withDerivations X R) (OracleComp (unifSpec + pub))
  | .inl t => (unifSpec + pub).query t
  | .inr x => pure (f x)

/-- **Lazy to eager, for a table of derivations, from any partial table.**

The ideal game holds a partial table of derivations.

Drawing the rest of the table first, then fixing it, gives the same output and public cache. -/
theorem run_simulateQ_idealImpl_evalDistEq_tableExtending {α : Type}
    (oa : OracleComp (pub.withDerivations X R) α) (C : pub.QueryCache)
    (T : (X →ₒ R).QueryCache) :
    (fun z => (z.1, z.2.1)) <$> (simulateQ (SecretEncoding.idealImpl pub X R) oa).run (C, T) =ᵈ
      (do
        let f ← $ᵗ (X → R)
        (simulateQ pub.romImpl (simulateQ (fixDerivations (tableExtending T f)) oa)).run C) := by
  induction oa using OracleComp.inductionOn generalizing C T with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    exact (EvalDistEq.bind_const _ _).symm
  | query_bind t k ih =>
    rcases t with t | x
    · have hl : (simulateQ (SecretEncoding.idealImpl pub X R)
          ((liftM (OracleSpec.query (spec := pub.withDerivations X R) (.inl t)) :
            OracleComp _ _) >>= k)).run (C, T) =
          (pub.romImpl t).run C >>= fun a =>
            (simulateQ (SecretEncoding.idealImpl pub X R) (k a.1)).run (a.2, T) := by
        rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
          Sphincs.Unforgeability.idealImpl_run_inl, bind_map_left]
      have hr : ∀ f : X → R, (simulateQ pub.romImpl (simulateQ (fixDerivations f)
          ((liftM (OracleSpec.query (spec := pub.withDerivations X R) (.inl t)) :
            OracleComp _ _) >>= k))).run C =
          (pub.romImpl t).run C >>= fun a =>
            (simulateQ pub.romImpl (simulateQ (fixDerivations f) (k a.1))).run a.2 := fun f => by
        rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        simp [fixDerivations]
      rw [hl, map_bind]
      simp only [hr]
      exact (EvalDistEq.bind_right _ fun a : _ × _ => ih a.1 a.2 T).trans
        (EvalDistEq.bind_bind_swap _ _ _)
    · have hr : ∀ f : X → R, (simulateQ pub.romImpl (simulateQ (fixDerivations f)
          ((liftM (OracleSpec.query (spec := pub.withDerivations X R) (.inr x)) :
            OracleComp _ _) >>= k))).run C =
          (simulateQ pub.romImpl (simulateQ (fixDerivations f) (k (f x)))).run C := fun f => by
        simp [fixDerivations]
      cases hT : T x with
      | some u =>
        have hl : (simulateQ (SecretEncoding.idealImpl pub X R)
            ((liftM (OracleSpec.query (spec := pub.withDerivations X R) (.inr x)) :
              OracleComp _ _) >>= k)).run (C, T) =
            (simulateQ (SecretEncoding.idealImpl pub X R) (k u)).run (C, T) := by
          rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
            SecretEncoding.idealImpl_run_derive_some hT, pure_bind]
        rw [hl]
        simp only [hr, tableExtending, hT, Option.getD_some]
        exact ih u C T
      | none =>
        have hl : (simulateQ (SecretEncoding.idealImpl pub X R)
            ((liftM (OracleSpec.query (spec := pub.withDerivations X R) (.inr x)) :
              OracleComp _ _) >>= k)).run (C, T) =
            ($ᵗ R) >>= fun u => (simulateQ (SecretEncoding.idealImpl pub X R) (k u)).run
              (C, T.cacheQuery x u) := by
          rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
            SecretEncoding.idealImpl_run_derive_none hT, bind_map_left]
        rw [hl, map_bind]
        simp only [hr]
        refine (EvalDistEq.bind_right _ fun u => ih u C (T.cacheQuery x u)).trans ?_
        have hext : ∀ (u : R) (f : X → R), tableExtending (T.cacheQuery x u) f =
            tableExtending T (Function.update f x u) := fun u f => by
          rw [tableExtending_cacheQuery, tableExtending_update_of_none _ _ hT]
        have hx : ∀ (u : R) (f : X → R), tableExtending T (Function.update f x u) x = u :=
          fun u f => by simp [tableExtending, hT]
        simp only [hext]
        refine EvalDistEq.trans ?_ (evalDistEq_uniformSample_bind_update x fun g =>
          (simulateQ pub.romImpl (simulateQ (fixDerivations (tableExtending T g))
            (k (tableExtending T g x)))).run C)
        simp only [hx]
        exact EvalDistEq.rfl

/-- An event of the ideal game has the same probability when the whole table is drawn first. -/
theorem prEvent_idealImpl_eq_bind_fixDerivations {α : Type}
    (oa : OracleComp (pub.withDerivations X R) α) (P : α → Prop) :
    Pr{let z ← (simulateQ (SecretEncoding.idealImpl pub X R) oa).run (∅, ∅)}[P z.1] =
      Pr{
        let f ← $ᵗ (X → R)
        let z ← (simulateQ pub.romImpl (simulateQ (fixDerivations f) oa)).run ∅}[P z.1] := by
  have h := (run_simulateQ_idealImpl_evalDistEq_tableExtending oa ∅ ∅).prEvent_eq fun z => P z.1
  simp only [prEvent_map, tableExtending_empty] at h
  simpa only [prEvent_norm] using h

end EthLib.Cryptography
