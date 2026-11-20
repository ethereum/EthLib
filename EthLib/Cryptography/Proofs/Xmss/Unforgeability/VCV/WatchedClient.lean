module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SingleBuildSource
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SigningTargets

/-!
# Digest registrations in the strong-forgery experiment

The leanXMSS draft in "Security" gives the adversary a signing oracle.

Successful requests activate the two digests their signatures reveal.

Every request still contributes its raw reply to the experiment's signing log.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.Watch

open OracleComp OracleSpec PostSigning

/-- Forward one original coin or hash query into the experiment with digest registrations. -/
@[expose] def ordinary : QueryImpl World (OracleComp WatchQueries) :=
  fun t => query (spec := WatchQueries) (.inl t)

private theorem forget_ordinary {α : Type} (c : OracleComp World α) :
    simulateQ forget (simulateQ ordinary c) = c := by
  apply (QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := QueryImpl.id' World) ?_ c).trans
    (simulateQ_id' c)
  intro t
  simp [ordinary, forget, randomOracle.Targets.forget]

variable {σ : Type}

/-- Answer the original client after recording both selected trials of each successful signature. -/
@[expose] def watchedSigner (pass : QueryImpl World (OracleComp World)) (seed : OracleComp World σ)
    (derive : σ → SeedPrf (OracleComp World)) :
    QueryImpl (World + SigningSpec) (WriterT RawLog (OracleComp WatchQueries))
  | .inl q => liftM (simulateQ ordinary (pass q))
  | .inr r => WriterT.mk (do
    let s ← simulateQ ordinary seed
    let pp ← simulateQ ordinary (publicParamOf (derive s))
    let reply ← signingTargets (hashOf pass) (derive s) pp r.leafIndex r.message
    return (reply.toOption, [(r, reply)]))

private theorem forget_signer (pass : QueryImpl World (OracleComp World))
    (seed : OracleComp World σ)
    (derive : σ → SeedPrf (OracleComp World)) (t : (World + SigningSpec).Domain) :
    simulateQ forget (watchedSigner pass seed derive t).run =
      (signerOf pass seed derive t).run := by
  cases t with
  | inl q => simp [watchedSigner, signerOf, forget_ordinary]
  | inr r =>
    simp [watchedSigner, signerOf, failSignerOf, forget_ordinary, forget_signingTargets,
      Functor.map_map, map_bind]

private theorem forget_client {α : Type} (pass : QueryImpl World (OracleComp World))
    (seed : OracleComp World σ) (derive : σ → SeedPrf (OracleComp World))
    (client : OracleComp (World + SigningSpec) α) :
    simulateQ forget (simulateQ (watchedSigner pass seed derive) client).run =
      (simulateQ (signerOf pass seed derive) client).run := by
  induction client using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind', simulateQ_map,
      forget_signer, ih]

/-- Continue from the actual public key with the adaptive client and production verifier. -/
@[expose] def afterKey (pass : QueryImpl World (OracleComp World)) (seed : OracleComp World σ)
    (derive : σ → SeedPrf (OracleComp World)) (A : Adversary) (pk : PublicKey) :
    OracleComp WatchQueries Outcome := do
  let (candidate, log) ← (simulateQ (watchedSigner pass seed derive) (A.main pk)).run
  let accepted ← simulateQ ordinary
    (verifyWith (hashOf pass) pk candidate.message candidate.signature)
  return ⟨pk, candidate, log, accepted⟩

/-- Observe selected digests during key generation, signing requests and verification. -/
@[expose] def watchedSource (pass : QueryImpl World (OracleComp World)) (seed : OracleComp World σ)
    (derive : σ → SeedPrf (OracleComp World)) (A : Adversary) :
    OracleComp WatchQueries Outcome := do
  let s ← simulateQ ordinary seed
  let pk ← simulateQ ordinary (publicKeyOf (hashOf pass) (derive s))
  afterKey pass seed derive A pk

/-- Removing registrations preserves the complete free program for the adaptive client. -/
theorem forget_watchedSource (pass : QueryImpl World (OracleComp World)) (seed : OracleComp World σ)
    (derive : σ → SeedPrf (OracleComp World)) (A : Adversary) :
    simulateQ forget (watchedSource pass seed derive A) = sourceOf pass seed derive A := by
  simp only [watchedSource, afterKey, sourceOf, simulateQ_bind, simulateQ_pure,
    forget_ordinary, forget_client]

/-- Watch the digests of successful replies in the production stateless experiment. -/
@[expose] noncomputable def watchedObserve (A : Adversary) : OracleComp WatchQueries Outcome := do
  let s0 ← simulateQ ordinary (liftM XmssSecurity.sampleMasterSeed : OracleComp World _)
  let H := hashOf (QueryImpl.id' World)
  watchedSource (QueryImpl.id' World) (schemeSeed H (ofSeed s0)) (seedPrf H) A

/-- Removing notices before the original cost meter gives the exact raw observation. -/
theorem forget_watchedObserve (A : Adversary) :
    simulateQ forget (watchedObserve A) = observe A := by
  rw [observe_eq_source]
  simp only [watchedObserve, simulateQ_bind, forget_ordinary, forget_watchedSource]

open HashSig
open scoped ENNReal

/-- Begin watching after key generation with its actual parameter and complete hash cache. -/
@[expose] noncomputable def measuredSource (pass : QueryImpl World (OracleComp World))
    (seed : OracleComp World σ) (derive : σ → SeedPrf (OracleComp World)) (A : Adversary)
    (cache : HashSpec.QueryCache) : ProbComp (Outcome × WatchState) := do
  let z ← (simulateQ HashSpec.romImpl
    (seed >>= fun s => publicKeyOf (hashOf pass) (derive s))).run cache
  let pp := z.1.publicParam
  (simulateQ (randomOracle.Targets.impl (record pp) (messageKey pp) low)
    (afterKey pass seed derive A z.1)).run ⟨z.2, fun _ => none, 0, false⟩

/-- The adaptive watch bounds fresh registered matches at the parameter the actual key supplies. -/
theorem prEvent_measuredSource (pass : QueryImpl World (OracleComp World))
    (seed : OracleComp World σ) (derive : σ → SeedPrf (OracleComp World)) (A : Adversary)
    (cache : HashSpec.QueryCache) (q : Nat) :
    Pr{let z ← measuredSource pass seed derive A cache}[z.2.hit = true ∧ z.2.paid ≤ q] ≤
      (q : ℝ≥0∞) / 2 ^ 128 :=
  prEvent_bind_le_of_forall_le_of_support _ _ _ fun z _ =>
    prEvent_registered_match z.1.publicParam _ ⟨z.2, fun _ => none, 0, false⟩ rfl q

/-- The measured source gives exactly the ordinary outcome and final cache. -/
theorem measuredSource_erase (pass : QueryImpl World (OracleComp World))
    (seed : OracleComp World σ) (derive : σ → SeedPrf (OracleComp World)) (A : Adversary)
    (cache : HashSpec.QueryCache) :
    (fun z => (z.1, z.2.cache)) <$> measuredSource pass seed derive A cache =
      (simulateQ HashSpec.romImpl (sourceOf pass seed derive A)).run cache := by
  rw [← forget_watchedSource]
  simp only [measuredSource, watchedSource, map_bind, simulateQ_bind, StateT.run_bind,
    forget_ordinary, bind_assoc]
  refine bind_congr fun seeded => bind_congr fun keyed => ?_
  exact randomOracle.Targets.forget_run _ _ _ _ _

/-- Sample the original master seed and run the two-layer watch from the real empty cache. -/
@[expose] noncomputable def measuredObserve (A : Adversary) : ProbComp (Outcome × WatchState) := do
  let z ← (simulateQ HashSpec.romImpl
    (liftM XmssSecurity.sampleMasterSeed : OracleComp World _)).run ∅
  let H := hashOf (QueryImpl.id' World)
  measuredSource (QueryImpl.id' World) (schemeSeed H (ofSeed z.1)) (seedPrf H) A z.2

/-- Count fresh matches after genuine successful signing in the original seeded experiment. -/
theorem prEvent_measuredObserve (A : Adversary) (q : Nat) :
    Pr{let z ← measuredObserve A}[z.2.hit = true ∧ z.2.paid ≤ q] ≤ (q : ℝ≥0∞) / 2 ^ 128 :=
  prEvent_bind_le_of_forall_le_of_support _ _ _ fun _ _ => prEvent_measuredSource _ _ _ _ _ q

/-- The recorded key, candidate, signing log, verification result and hash cache are exact. -/
theorem measuredObserve_erase (A : Adversary) :
    (fun z => (z.1, z.2.cache)) <$> measuredObserve A =
      (simulateQ HashSpec.romImpl (observe A)).run ∅ := by
  rw [observe_eq_source]
  simp only [measuredObserve, map_bind, simulateQ_bind, StateT.run_bind, measuredSource_erase]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.Watch
