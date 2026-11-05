module

public import EthLib.Consensus.HonestBuilder
public import EthLib.Base.Proofs.MapM
public import EthLib.Cryptography.Proofs.Bls.SignaturesCorrect

/-!
# Proofs: the signatures of an honest builder

A bid is signed under the domain of the epoch of its slot, and checked under the current one.

The two domains agree when the bid is for a slot of the current epoch.

An envelope is signed and checked under the domain of the current epoch.

Under the pairing laws, a bid or an envelope signed with the key of its signer passes its check.

For a self-build, the signer of an envelope is the proposer of the latest block.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {state : BeaconState preset fork}

/-- The domain of the current epoch is the default domain of a state. -/
theorem getDomain_currentEpoch (config : Config) (domainType : DomainType) :
    getDomain config state domainType (some (getCurrentEpoch state)) =
      getDomain config state domainType :=
  rfl

/-- A bid for a slot of the current epoch is signed under the domain of its check. -/
theorem builderSigningRoot_bid {config : Config} {bid : ExecutionPayloadBid preset fork}
    (current : computeEpochAtSlot preset bid.slot = getCurrentEpoch state) :
    builderSigningRoot config state bid (some (computeEpochAtSlot preset bid.slot)) =
      builderSigningRoot config state bid := by
  rw [current]
  rfl

/-- A signature by a secret key, of a root that has a value, verifies under its public key.

It returns that root. -/
private theorem verify_of_signed (laws : PairingLaws) {key : Signatures.SecretKey}
    {rootResult : Except TransitionError Root} {signature : BLSSignature}
    (signedBy : (do
        let root ← rootResult.mapError BuilderSigningError.root
        (Signatures.sign key (packBytes root)).mapError .bls :
          Except BuilderSigningError BLSSignature) = .ok signature) :
    ∃ root, rootResult = .ok root ∧ Signatures.verify (packBytes (Signatures.skToPk key))
      (packBytes root) (packBytes signature) = true := by
  -- Split the bind with lemmas, so the kernel never evaluates the signature.
  obtain ⟨root, rooted, signs⟩ := bind_ok_iff.mp signedBy
  rw [mapError_ok_iff] at rooted signs
  obtain ⟨signature', signs', verifies⟩ := Signatures.verify_sign laws key (packBytes root)
  rw [signs', Except.ok.injEq] at signs
  subst signs
  exact ⟨root, rooted, verifies⟩

/-- A bid signed with the key of its builder passes the check of its signature.

The bid must be for a slot of the current epoch, and its builder must have the public key.

The statement holds under the laws of the pairing, as BLS correctness does. -/
theorem verifyExecutionPayloadBidSignature_of_sign (laws : PairingLaws) {config : Config}
    (gloas : .glamsterdam ≤ fork) {signed : SignedExecutionPayloadBid preset fork}
    {key : Signatures.SecretKey} {builder : Builder}
    (registered : getBuilder state gloas signed.message.builderIndex = .ok builder)
    (owned : builder.pubkey = Signatures.skToPk key)
    (current : computeEpochAtSlot preset signed.message.slot = getCurrentEpoch state)
    (signedBy : getExecutionPayloadBidSignature config state signed.message key =
      .ok signed.signature) :
    verifyExecutionPayloadBidSignature config .bls state gloas signed = .ok true := by
  unfold getExecutionPayloadBidSignature at signedBy
  rw [builderSigningRoot_bid current] at signedBy
  obtain ⟨root, rooted, verifies⟩ := verify_of_signed laws signedBy
  unfold verifyExecutionPayloadBidSignature
  rw [show liftAccessor (getBuilder state gloas signed.message.builderIndex) = .ok builder by
    rw [registered]; rfl, rooted]
  show Except.ok (Signatures.verify (packBytes builder.pubkey) (packBytes root)
    (packBytes signed.signature)) = .ok true
  rw [owned]
  exact congrArg Except.ok verifies

/-- For a self-build, the signer of an envelope is the proposer of the latest block. -/
theorem envelopeSignerKey_selfBuild (gloas : .glamsterdam ≤ fork) :
    envelopeSignerKey state gloas BUILDER_INDEX_SELF_BUILD =
      (fun validator => validator.pubkey) <$>
        liftAccessor (getValidator state state.latestBlockHeader.proposerIndex) := by
  simp only [envelopeSignerKey, ↓reduceIte]
  cases liftAccessor (getValidator state state.latestBlockHeader.proposerIndex) <;> rfl

/-- Otherwise the signer of an envelope is its builder. -/
theorem envelopeSignerKey_builder (gloas : .glamsterdam ≤ fork) {index : BuilderIndex}
    (notSelf : index ≠ BUILDER_INDEX_SELF_BUILD) :
    envelopeSignerKey state gloas index =
      (fun builder => builder.pubkey) <$> liftAccessor (getBuilder state gloas index) := by
  simp only [envelopeSignerKey, notSelf, ↓reduceIte]
  cases liftAccessor (getBuilder state gloas index) <;> rfl

/-- An envelope signed with the key of its signer passes the check of its signature.

The signer is the builder of the envelope, or the proposer of the latest block for a self-build.

The statement holds under the laws of the pairing, as BLS correctness does. -/
theorem verifyExecutionPayloadEnvelopeSignature_of_sign (laws : PairingLaws) {config : Config}
    (gloas : .glamsterdam ≤ fork) {signed : SignedExecutionPayloadEnvelope preset fork}
    {key : Signatures.SecretKey}
    (owned : envelopeSignerKey state gloas signed.message.builderIndex =
      .ok (Signatures.skToPk key))
    (signedBy : getExecutionPayloadEnvelopeSignature config state signed.message key =
      .ok signed.signature) :
    verifyExecutionPayloadEnvelopeSignature config .bls state gloas signed = .ok true := by
  unfold getExecutionPayloadEnvelopeSignature at signedBy
  obtain ⟨root, rooted, verifies⟩ := verify_of_signed laws signedBy
  unfold verifyExecutionPayloadEnvelopeSignature
  rw [owned, show builderSigningRoot config state signed.message = .ok root from rooted]
  show Except.ok (Signatures.verify (packBytes (Signatures.skToPk key)) (packBytes root)
    (packBytes signed.signature)) = .ok true
  exact congrArg Except.ok verifies

end EthLib.Consensus
