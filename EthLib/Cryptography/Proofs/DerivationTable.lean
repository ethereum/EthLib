module

public import EthLib.Cryptography.Proofs.EvalDistEq
public import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Proofs: hidden seeds and a table of derivations, for any random oracle

A secret seed is hidden when every value derived from it is a hash of the seed.

VCVio's hidden-seed games treat such a derivation as a query of its own, a derivation query.

In the real game, a derivation is answered by the random oracle at the point that encodes it.

In the ideal game, it is answered by an independent table, and the seed appears nowhere.

This file adds three facts to them, for every public oracle.

- One hop: an event of the real game is at most the event in the ideal game, plus a term.
  The term is the number of queries at encodable points times the chance of the drawn seed.
- A seed fixed by every point that encodes it is hit with probability at most `1 / |S|`.
- Lazy to eager: drawing each derivation on its first query gives the distribution of drawing
  the whole table first.
-/

@[expose] public section

namespace EthLib.Cryptography

open OracleSpec OracleComp

section HiddenSeed

variable {ι : Type} {pub : OracleSpec ι} {R : Type}

/-- Let every encoded point fix its secret.

Then a point encodes a derivation under a uniform secret with probability at most `1 / |S|`. -/
theorem prEvent_mem_range_enc_le {S X : Type} [SampleableType S] (E : SecretEncoding pub S X R)
    (hfix : ∀ s s' x x', E.enc s x = E.enc s' x' → s = s') (t : ι) :
    Pr{let s ← $ᵗ S}[t ∈ Set.range (E.enc s)] ≤ (Nat.card S : ENNReal)⁻¹ := by
  by_cases ht : ∃ s₀ x₀, E.enc s₀ x₀ = t
  · obtain ⟨s₀, x₀, rfl⟩ := ht
    refine le_of_le_of_eq ?_ (SampleableType.prEvent_uniformSample_eq_singleton_natCard s₀)
    exact prEvent_mono _ _ _ fun s hs => by
      obtain ⟨x, hx⟩ := hs
      exact hfix s s₀ x x₀ hx
  · refine le_of_eq_of_le ?_ (zero_le (a := ((Nat.card S : ENNReal)⁻¹)))
    refine (prEvent_eq_zero_iff _ _).2 fun s _ hs => ?_
    obtain ⟨x, hx⟩ := hs
    exact ht ⟨s, x, hx⟩

variable [DecidableEq ι] [∀ t, SampleableType (pub.Range t)] [SampleableType R]

/-- The ideal game answers a sampling or public query as the random oracle does.

It keeps its derivation table. -/
theorem idealImpl_run_inl {X : Type} [DecidableEq X] (t : (unifSpec + pub).Domain)
    (C : pub.QueryCache) (T : (X →ₒ R).QueryCache) :
    (SecretEncoding.idealImpl pub X R (.inl t)).run (C, T) =
      (fun z => (z.1, (z.2, T))) <$> (pub.romImpl t).run C := by
  rcases t with n | t
  · simp [SecretEncoding.idealImpl, unifFwdImpl]
  · rfl

/-- **One hidden-seed hop.**

Run a program in the random oracle, with every derivation answered at its encoded point.

An event of its output is at most the same event in the ideal game, plus `q * ε`.

The program makes at most `q` queries at encodable points.

A point encodes a derivation under the drawn secret with probability at most `ε`. -/
theorem prEvent_romImpl_deriveImpl_le {S X : Type} [DecidableEq X] (E : SecretEncoding pub S X R)
    {ms : ProbComp S} {ε : ENNReal} (hε : ∀ t, Pr{let s ← ms}[t ∈ Set.range (E.enc s)] ≤ ε)
    {p : (pub.withDerivations X R).Domain → Prop} [DecidablePred p]
    (hp : ∀ s x, p (.inl (.inr (E.enc s x)))) {α : Type}
    {oa : OracleComp (pub.withDerivations X R) α} {q : ℕ} (h : IsQueryBoundP oa p q)
    (P : S → α → Prop) :
    Pr{
      let s ← ms
      let z ← (simulateQ pub.romImpl (simulateQ (E.deriveImpl s) oa)).run ∅}[P s z.1] ≤
      Pr{
        let s ← ms
        let z ← (simulateQ (SecretEncoding.idealImpl pub X R) oa).run (∅, ∅)}[P s z.1] +
        q * ε := by
  simp only [← QueryImpl.simulateQ_compose]
  exact E.prEvent_realImpl_le_add_mul hε hp h fun s z => P s z.1

end HiddenSeed

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
          idealImpl_run_inl, bind_map_left]
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
