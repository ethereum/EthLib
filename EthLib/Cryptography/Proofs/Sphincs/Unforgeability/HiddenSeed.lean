module

public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed
public import VCVio.CryptoFoundations.SignatureAlg.Transcript
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Proofs: hidden seeds, for any random oracle

A secret seed is hidden when every value derived from it is a hash of the seed.

VCVio's hidden-seed games treat such a derivation as a query of its own, a derivation query.

In the real game, a derivation is answered by the random oracle at the point that encodes it.

In the ideal game, it is answered by an independent table, and the seed appears nowhere.

This file adds three facts to them, for every public oracle.

- One hop: an event of the real game is at most the event in the ideal game, plus the number of
  adversary queries at encodable points times the chance that a point encodes the drawn seed.
- A seed fixed by every point that encodes it is hit with probability at most one over the
  number of seeds.
- Lazy to eager, for a single derivation: drawing it on its first query, or drawing it first and
  then fixing it, gives the same distribution.

The last fact chains two hops, when the secret of the second hop is the one derivation of the
first.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability

open OracleSpec OracleComp

variable {ι : Type} {pub : OracleSpec ι} {R : Type}

/-- Answer the one derivation with `u`, and pass every other query on. -/
def fixDerivation (u : R) :
    QueryImpl (pub.withDerivations Unit R) (OracleComp (unifSpec + pub))
  | .inl t => (unifSpec + pub).query t
  | .inr () => pure u

/-- A lifted program makes no derivation, so fixing the derivation gives the program back. -/
theorem fixDerivation_comp_withDerivationsLift (u : R) :
    fixDerivation (pub := pub) u ∘ₛ pub.withDerivationsLift Unit R =
      QueryImpl.id' (unifSpec + pub) := by
  funext t
  rcases t with n | t <;> rfl

/-- Lift an adversary into a world with derivations, then answer its queries with a handler that
undoes the lift.

The experiment is then the experiment of the mapped scheme against the adversary itself. -/
theorem simulateQ_unforgeableTranscriptExperiment_withDerivationsLift {X M PK SK SK' S : Type}
    (G : QueryImpl (pub.withDerivations X R) (OracleComp (unifSpec + pub)))
    (hG : G ∘ₛ pub.withDerivationsLift X R = QueryImpl.id' (unifSpec + pub))
    {B : SignatureAlg (OracleComp (unifSpec + pub)) M PK SK S}
    (A : SignatureAlg (OracleComp (pub.withDerivations X R)) M PK SK' S)
    (adv : SignatureAlg.UnforgeableAdversary B) :
    simulateQ G (SignatureAlg.unforgeableTranscriptExperiment
        (adv.mapOracles (pub.withDerivationsLift X R) (sigAlg' := A))) =
      SignatureAlg.unforgeableTranscriptExperiment (sigAlg := A.map (simulateQ' G))
        ⟨adv.main⟩ := by
  rw [SignatureAlg.simulateQ_unforgeableTranscriptExperiment,
    SignatureAlg.UnforgeableAdversary.mapOracles_mapOracles, hG]
  exact congrArg _ (congrArg SignatureAlg.UnforgeableAdversary.mk
    (SignatureAlg.UnforgeableAdversary.mapOracles_id'_main adv))

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

/-- Once the derivation is drawn as `u`, the ideal game runs as the random oracle with the
derivation fixed to `u`. -/
theorem run_simulateQ_idealImpl_of_eq_some {α : Type}
    (oa : OracleComp (pub.withDerivations Unit R) α) (u : R) (C : pub.QueryCache)
    (T : (Unit →ₒ R).QueryCache) (hT : T () = some u) :
    (fun z => (z.1, z.2.1)) <$> (simulateQ (SecretEncoding.idealImpl pub Unit R) oa).run (C, T) =
      (simulateQ pub.romImpl (simulateQ (fixDerivation u) oa)).run C := by
  induction oa using OracleComp.inductionOn generalizing C with
  | pure x => simp
  | query_bind t k ih =>
    rcases t with (n | t) | ⟨⟩
    · simp [SecretEncoding.idealImpl, fixDerivation, ih, unifFwdImpl]
    · simp [SecretEncoding.idealImpl, fixDerivation, ih]
    · simp [SecretEncoding.idealImpl, fixDerivation, ih, hT]

/-- **Lazy to eager, for one derivation.**

From an empty table, the ideal game draws the derivation on its first query.

Drawing it first, then fixing it, gives the same output and public cache in distribution. -/
theorem run_simulateQ_idealImpl_evalDistEq {α : Type}
    (oa : OracleComp (pub.withDerivations Unit R) α) (C : pub.QueryCache) :
    (fun z => (z.1, z.2.1)) <$> (simulateQ (SecretEncoding.idealImpl pub Unit R) oa).run (C, ∅) =ᵈ
      (do
        let u ← $ᵗ R
        (simulateQ pub.romImpl (simulateQ (fixDerivation u) oa)).run C) := by
  induction oa using OracleComp.inductionOn generalizing C with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    exact (EvalDistEq.bind_const _ _).symm
  | query_bind t k ih =>
    rcases t with t | ⟨⟩
    · have hl : (simulateQ (SecretEncoding.idealImpl pub Unit R)
          ((liftM (OracleSpec.query (spec := pub.withDerivations Unit R) (.inl t)) :
            OracleComp _ _) >>= k)).run (C, ∅) =
          (pub.romImpl t).run C >>= fun a =>
            (simulateQ (SecretEncoding.idealImpl pub Unit R) (k a.1)).run (a.2, ∅) := by
        rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, idealImpl_run_inl,
          bind_map_left]
      have hr : ∀ u : R, (simulateQ pub.romImpl (simulateQ (fixDerivation u)
          ((liftM (OracleSpec.query (spec := pub.withDerivations Unit R) (.inl t)) :
            OracleComp _ _) >>= k))).run C =
          (pub.romImpl t).run C >>= fun a =>
            (simulateQ pub.romImpl (simulateQ (fixDerivation u) (k a.1))).run a.2 := fun u => by
        rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        simp [fixDerivation]
      rw [hl, map_bind]
      simp only [hr]
      exact (EvalDistEq.bind_right _ fun a : _ × _ => ih a.1 a.2).trans
        (EvalDistEq.bind_bind_swap _ _ _)
    · rename_i x
      cases x
      have hl : (simulateQ (SecretEncoding.idealImpl pub Unit R)
          ((liftM (OracleSpec.query (spec := pub.withDerivations Unit R) (.inr ())) :
            OracleComp _ _) >>= k)).run (C, ∅) =
          ($ᵗ R) >>= fun u => (simulateQ (SecretEncoding.idealImpl pub Unit R) (k u)).run
            (C, (∅ : (Unit →ₒ R).QueryCache).cacheQuery () u) := by
        rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
          SecretEncoding.idealImpl_run_derive_none rfl, bind_map_left]
      rw [hl, map_bind]
      refine EvalDistEq.bind_right _ fun u => ?_
      rw [run_simulateQ_idealImpl_of_eq_some _ u _ _ (QueryCache.cacheQuery_self _ _ _)]
      simp [fixDerivation]

/-- An event of the output of the ideal game with one derivation has the same probability when
the derivation is drawn first and then fixed. -/
theorem prEvent_idealImpl_eq_bind_fixDerivation {α : Type}
    (oa : OracleComp (pub.withDerivations Unit R) α) (P : α → Prop) :
    Pr{let z ← (simulateQ (SecretEncoding.idealImpl pub Unit R) oa).run (∅, ∅)}[P z.1] =
      Pr{
        let u ← $ᵗ R
        let z ← (simulateQ pub.romImpl (simulateQ (fixDerivation u) oa)).run ∅}[P z.1] := by
  have h := (run_simulateQ_idealImpl_evalDistEq oa ∅).prEvent_eq fun z => P z.1
  simp only [prEvent_map] at h
  simpa only [prEvent_norm] using h

omit [DecidableEq ι] [∀ t, SampleableType (pub.Range t)] [SampleableType R] in
/-- Let every encoded point fix its secret.

Then a point encodes a derivation under a uniform secret with probability at most one over the
number of secrets. -/
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

end EthLib.Cryptography.Sphincs.Unforgeability
