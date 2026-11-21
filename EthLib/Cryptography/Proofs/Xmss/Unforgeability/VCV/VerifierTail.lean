module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SingleBuildSource
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.VerificationTrials

/-!
# The verification tail of the production strong-forgery game

The leanXMSS draft, section "Security", verifies the candidate returned by the client.

The hidden graph schedule can replace key generation and signing.

The prefix must preserve the joint distribution of the client result and graph state.

The verifier then uses the same public hash and starts at the end of that particular pre.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient

open EthLib.Cryptography OracleSpec OracleComp HashSig TwoLayerGraph

/-- The candidate and raw replies before the final call to verification. -/
structure BeforeVerify where
  key : PublicKey
  candidate : Forgery
  log : RawLog

/-- Key generation and the actual option-valued client with its raw signing log. -/
@[expose] def beforeVerify {ι σ : Type} {spec : OracleSpec ι}
    (pass : QueryImpl World (OracleComp spec)) (seed : OracleComp spec σ)
    (derive : σ → SeedPrf (OracleComp spec)) (A : Adversary) : OracleComp spec BeforeVerify := do
  let s ← seed
  let pk ← publicKeyOf (hashOf pass) (derive s)
  let (candidate, log) ← (simulateQ (signerOf pass seed derive) (A.main pk)).run
  return ⟨pk, candidate, log⟩

/-- Verify exactly the candidate produced by the prefix and keep the same key and raw log. -/
@[expose] def verifyCandidate {ι : Type} {spec : OracleSpec ι}
    (H : ByteArray → OracleComp spec (Vector UInt8 32))
      (pre : BeforeVerify) : OracleComp spec Outcome := do
  let accepted ← verifyWith H pre.key pre.candidate.message pre.candidate.signature
  return ⟨pre.key, pre.candidate, pre.log, accepted⟩

theorem sourceOf_eq_beforeVerify {ι σ : Type} {spec : OracleSpec ι}
    (pass : QueryImpl World (OracleComp spec)) (seed : OracleComp spec σ)
    (derive : σ → SeedPrf (OracleComp spec)) (A : Adversary) :
    sourceOf pass seed derive A = beforeVerify pass seed derive A
      >>= verifyCandidate (hashOf pass) := by
  simp only [sourceOf, beforeVerify, verifyCandidate, bind_assoc, pure_bind]

/-- Forward private coins and read both halves of each full public hash at one physical address. -/
@[expose] def graphOracle : QueryImpl World (OracleComp Honest.SharedSpec)
  | .inl n => query (spec := Honest.SharedSpec) (.inl (.inl (.inl n)))
  | .inr b => do
    let lo ← query (spec := Honest.SharedSpec) (.inl (.inl (.inr (.inl b))))
    let hi ← query (spec := Honest.SharedSpec) (.inl (.inl (.inr (.inr b))))
    return PairedHashWord.halves.symm (lo, hi)

theorem graphOracle_hash : hashOf graphOracle = Honest.hash := by
  funext b
  simp [hashOf, graphOracle, Honest.hash, map_bind]

/-- A replacement prefix with the same joint eager endpoint preserves the whole source game. -/
theorem sourceOf_normalize {σ : Type} (pp : PublicParam) (seed : OracleComp Honest.SharedSpec σ)
    (derive : σ → SeedPrf (OracleComp Honest.SharedSpec)) (A : Adversary)
    (pre : OracleComp Honest.SharedSpec BeforeVerify) (initial : Honest.SharedState)
    (same : ((simulateQ (graph pp).eagerImpl (beforeVerify graphOracle seed derive A)).run initial)
      =ᵈ
      ((simulateQ (graph pp).eagerImpl pre).run initial)) :
    ((simulateQ (graph pp).eagerImpl (sourceOf graphOracle seed derive A)).run initial) =ᵈ
      ((simulateQ (graph pp).eagerImpl (pre >>= verifyCandidate Honest.hash)).run initial) := by
  rw [sourceOf_eq_beforeVerify, graphOracle_hash]
  simp only [simulateQ_bind, StateT.run_bind]
  exact same.bind_left _

/-- A supported normalized endpoint retains its actual pre-verifier state.

The verifier starts with the original public key, candidate and raw log of the same pre.
-/
theorem verifier_cut (pp : PublicParam) (pre : OracleComp Honest.SharedSpec BeforeVerify)
    (initial finish : Honest.SharedState × List Cell) (obs : Outcome)
    (run : (obs, finish) ∈ support ((simulateQ (graph pp).deferredImpl
      (pre >>= verifyCandidate Honest.hash)).run initial)) :
    ∃ mid : Honest.SharedState × List Cell,
      (⟨obs.key, obs.candidate, obs.log⟩,
        mid) ∈ support ((simulateQ (graph pp).deferredImpl pre).run initial) ∧
      (obs.verified, finish) ∈ support ((simulateQ (graph pp).deferredImpl
        (verifyWith Honest.hash obs.key obs.candidate.message obs.candidate.signature)).run
          mid) := by
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff, verifyCandidate, simulateQ_pure,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at run
  obtain ⟨⟨⟨pk, candidate, log⟩, mid⟩, pre, ⟨yes, post⟩, checked, pair⟩ := run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj pair
  exact ⟨mid, pre, checked⟩

/-- The actual normalized candidate materialized both trial words after the client stopped.

The top trial used the root of the supported bottom verification on the same execution.
-/
theorem accepted_verifier_trials (pre : OracleComp Honest.SharedSpec BeforeVerify)
    (initial finish : Honest.SharedState × List Cell) (obs : Outcome)
    (run : (obs, finish) ∈ support ((simulateQ (graph obs.key.publicParam).deferredImpl
      (pre >>= verifyCandidate Honest.hash)).run initial)) (accepted : obs.verified = true) :
    ∃ (mid : Honest.SharedState × List Cell) (b : Digest)
      (topStart : Honest.SharedState × List Cell),
      (⟨obs.key, obs.candidate, obs.log⟩, mid) ∈ support
        ((simulateQ (graph obs.key.publicParam).deferredImpl pre).run initial) ∧
      (some b, topStart) ∈ support ((simulateQ (graph obs.key.publicParam).deferredImpl
        (layerRoot Honest.hash obs.key.publicParam .bottom obs.candidate.signature.leafIndex.toNat
          (packBytes obs.candidate.message) obs.candidate.signature.bottom)).run mid) ∧
      VerifierProbe.ReadTrial obs.key.publicParam
        (VerifierProbe.messageInput obs.key.publicParam .bottom
        obs.candidate.signature.leafIndex.toNat
          (packBytes obs.candidate.message) obs.candidate.signature.bottom)
        mid finish.1 ∧
      VerifierProbe.ReadTrial obs.key.publicParam
        (VerifierProbe.messageInput obs.key.publicParam .top
        (bottomTree obs.candidate.signature.leafIndex)
          (packBytes b) obs.candidate.signature.top) topStart finish.1 := by
  obtain ⟨mid, prefixRun, verified⟩ := verifier_cut _ pre initial finish obs run
  rw [accepted] at verified
  obtain ⟨b, topStart, bottom, botTrial, topTrial⟩ :=
      VerifierProbe.accepted_trials _ _ _ mid finish verified
  exact ⟨mid, b, topStart, prefixRun, bottom, botTrial, topTrial⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient
