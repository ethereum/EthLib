module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedTranscript
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RepeatedSearch
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.GuardedRoot
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedCalls
import EthLib.Cryptography.Proofs.Xmss.MapMonad

/-!
# The signing transcript before a completed verification

The accepted path carries the actual raw signing log and the original public verifier.

Its public and private cut states are the outputs of that same adaptive prefix.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig Constants TwoLayerGraph Honest OracleComp OracleSpec
open CanonicalGraph.PairedQueries

private theorem logged_of_run {pp : PublicParam} {α : Type} {p : OracleComp SharedSpec α} {s a t}
    (ran : (a,t) ∈ support ((simulateQ (graph pp).deferredImpl p).run s)) :
    ∃ xs, Logged pp p s a xs t := by
  rw [← loggingOracle.fst_map_run_simulateQ p, simulateQ_map, StateT.run_map, support_map] at ran
  obtain ⟨⟨⟨v, xs⟩, u⟩, actual, eq⟩ := ran
  cases eq
  exact ⟨xs, actual⟩

private theorem verifier_image (key : PublicKey) (candidate : Forgery) :
    simulateQ (expand PairedHashWord.halves)
      (verifyWith mixedHash key candidate.message candidate.signature) =
      verifyWith Honest.hash key candidate.message candidate.signature := by
  rw [verifyWith_map_monad (simulateQ (expand PairedHashWord.halves)) (simulateQ_pure _)
    (simulateQ_bind _)]
  simp only [expand_hash]

attribute [local irreducible] simulateQ emitStructure Xmss.verifyWith selection mixedOracle
  graph guardedGraph

/-- Recover the client and verifier cuts from the completed capped path. -/
theorem mixed_verifier_cut (pp : PublicParam) (A : Adversary) (left : Nat) (r : ResidualCache pp)
    (s : DeferredState) (obs : Outcome) (out : ResidualCache pp) (t : DeferredState)
    (actual : (some (obs,out),t) ∈ support ((simulateQ (graph pp).deferredImpl
      (guardedGraph left ((mixedGame pp A).run r))).run s)) :
    obs.key.publicParam = pp ∧ ∃ (atClient atVerifier : DeferredState) (xs : SharedSpec.QueryLog),
      (obs.key.root,atClient) ∈ support ((simulateQ (graph pp).deferredImpl (topRoot pp)).run s) ∧
      Logged pp ((expandLocal pp (simulateQ (mixedOracle pp) (A.main obs.key)).run).run r)
        atClient ((obs.candidate,obs.log),out) xs atVerifier ∧
      LogWithin (releasedCells pp atVerifier.1 obs.log) xs ∧
      (obs.verified,t) ∈ support ((simulateQ (graph pp).deferredImpl
        (verifyWith Honest.hash obs.key obs.candidate.message obs.candidate.signature)).run
          atVerifier) := by
  rw [guardedGraph, ← QueryImpl.simulateQ_compose] at actual
  rw [show ((graph pp).deferredImpl).compose (expand PairedHashWord.halves)
    = deferredMixed pp from by rw [deferredMixed]] at actual
  have uncapped : MixedRun (deferredMixed pp) (mixedGame pp A) r s obs out t :=
    WeightedCap.mem_support_of_capCompOpt_some (deferredMixed pp) _ _ _ _ _ _ actual
  unfold mixedGame at uncapped
  obtain ⟨root, next, atClient, rootRun, tail⟩ := uncapped.bind
  obtain ⟨rfl, rootBody⟩ := rootRun.lifted
  obtain ⟨⟨candidate, raw⟩, afterClient, atVerifier, client, tail⟩ := tail.bind
  obtain ⟨valid, afterVerify, final, verified, done⟩ := tail.bind
  obtain ⟨rfl, rfl, rfl⟩ := done.pure_result
  obtain ⟨rfl, verifyBody⟩ := verified.lifted
  simp only [deferredMixed, QueryImpl.simulateQ_compose, verifier_image] at verifyBody
  change ((_,_),_) ∈ support ((simulateQ (deferredMixed pp) _).run _) at client
  rw [deferredMixed, QueryImpl.simulateQ_compose] at client rootBody
  rw [(root_structural pp .top LAYER_HEIGHT 0).1] at rootBody
  obtain ⟨xs, log⟩ := logged_of_run client
  exact ⟨rfl,atClient,atVerifier,xs,rootBody,log,mixed_client_reads pp _ _ log,verifyBody⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
