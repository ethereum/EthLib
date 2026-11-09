module

public import EthLib.Consensus.HonestBuilder
public import EthLib.Base.Proofs.MapM
public import EthLib.Consensus.Proofs.Containers.Block
public import EthLib.Consensus.Proofs.Transition.PayloadInputs
public import EthLib.Cryptography.Proofs.Bls.SignaturesCorrect

/-!
# Proofs: the bid, the envelope and the signatures of an honest builder

A bid is built exactly when its fields are those of its payload, its state and its inputs.

A self-built bid is from the reserved builder index, with no value and the signature at infinity.

It passes the checks of the builder of a bid, on every state.

An envelope is built exactly when it reveals its payload and requests, and names its block.

It must also name the parent of the block and the builder of the bid of the block.

From Gloas, take a block that passes its steps, with a bid that a builder built from a payload.

The block must also commit to the root of the state after it.

The vectors whose length the preset sets must have a positive length, for the root of the block.

The envelope of that payload then passes the checks of the block root and the parent root.

It also passes the checks of the builder, the mix, the gas limit and the block hash.

It passes the check of the root of the requests, and builds on the latest block hash.

The slot of the bid is the slot of that state.

A bid is signed under the domain of the epoch of its slot, and checked under the current one.

The two domains agree when the bid is for a slot of the current epoch.

An envelope is signed and checked under the domain of the current epoch.

A bid or an envelope signed with the key of its signer passes its check.

For a self-build, the signer of an envelope is the proposer of the latest block.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {state : BeaconState preset fork}

/-! ## The bid and the envelope -/

section Build

variable {payload : ExecutionPayload preset fork} {requests : ExecutionRequests preset fork}
  {blobKzgCommitments : BlobKZGCommitments preset fork} {feeRecipient : ExecutionAddress}
  {inclusionListBits : Since .hegota fork (InclusionListBits preset)}

/-- A bid is built exactly when its fields are those of its payload, its state and its inputs.

Its parent root is the root of the latest block header of the state.

Its root of the requests is the root of the requests of the payload.

Its parent hash, block hash, RANDAO mix and gas limit are those of the payload.

It asks for no payment on the execution layer, and its other fields are the inputs. -/
theorem getExecutionPayloadBid_eq_ok_iff {slot : Slot} {builderIndex : BuilderIndex}
    {value : Gwei} {bid : ExecutionPayloadBid preset fork} :
    getExecutionPayloadBid state payload requests blobKzgCommitments slot feeRecipient
        builderIndex value inclusionListBits = .ok bid ↔
      SszType.hashTreeRoot state.latestBlockHeader = .ok bid.parentBlockRoot ∧
      SszType.hashTreeRoot requests = .ok bid.executionRequestsRoot ∧
      bid.parentBlockHash = payload.parentHash ∧ bid.blockHash = payload.blockHash ∧
      bid.prevRandao = payload.prevRandao ∧ bid.gasLimit = payload.gasLimit ∧
      bid.feeRecipient = feeRecipient ∧ bid.builderIndex = builderIndex ∧ bid.slot = slot ∧
      bid.value = value ∧ bid.executionPayment = 0 ∧
      bid.blobKzgCommitments = blobKzgCommitments ∧ bid.inclusionListBits = inclusionListBits := by
  unfold getExecutionPayloadBid
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq]
  constructor
  · rintro ⟨_, rooted, _, requested, rfl⟩
    exact ⟨rooted, requested, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases bid
    rintro ⟨rooted, requested, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨_, rooted, _, requested, rfl⟩

/-- A self-built bid is the bid of the reserved builder index, for the slot of the state.

It has no value, and the signature at infinity. -/
theorem getSelfBuiltExecutionPayloadBid_eq_ok_iff
    {signed : SignedExecutionPayloadBid preset fork} :
    getSelfBuiltExecutionPayloadBid state payload requests blobKzgCommitments feeRecipient
        inclusionListBits = .ok signed ↔
      getExecutionPayloadBid state payload requests blobKzgCommitments state.slot feeRecipient
          BUILDER_INDEX_SELF_BUILD 0 inclusionListBits = .ok signed.message ∧
        signed.signature = Signatures.infinitySignature := by
  unfold getSelfBuiltExecutionPayloadBid
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq]
  constructor
  · rintro ⟨_, built, rfl⟩
    exact ⟨built, rfl⟩
  · cases signed
    rintro ⟨built, rfl⟩
    exact ⟨_, built, rfl⟩

/-- A self-built bid passes the checks of the builder of a bid, on every state. -/
theorem checkBidBuilder_of_getSelfBuiltExecutionPayloadBid {config : Config}
    {checks : SignatureChecks} {other : BeaconState preset fork} (gloas : .glamsterdam ≤ fork)
    {signed : SignedExecutionPayloadBid preset fork}
    (built : getSelfBuiltExecutionPayloadBid state payload requests blobKzgCommitments
      feeRecipient inclusionListBits = .ok signed) :
    checkBidBuilder config checks other gloas signed = .ok () := by
  obtain ⟨made, signature⟩ := getSelfBuiltExecutionPayloadBid_eq_ok_iff.mp built
  obtain ⟨-, -, -, -, -, -, -, builder, -, value, -⟩ := getExecutionPayloadBid_eq_ok_iff.mp made
  simp [checkBidBuilder, builder, value, signature, ensure]

/-- An envelope is built exactly when it reveals the payload and the requests.

It names the builder of the bid of the block, the root of the block and the parent of the block. -/
theorem getExecutionPayloadEnvelope_eq_ok_iff {block : BeaconBlock preset fork}
    {gloas : .glamsterdam ≤ fork} {envelope : ExecutionPayloadEnvelope preset fork} :
    getExecutionPayloadEnvelope block gloas payload requests = .ok envelope ↔
      SszType.hashTreeRoot block = .ok envelope.beaconBlockRoot ∧ envelope.payload = payload ∧
      envelope.executionRequests = requests ∧
      envelope.builderIndex = (block.body.signedExecutionPayloadBid gloas).message.builderIndex ∧
      envelope.parentBeaconBlockRoot = block.parentRoot := by
  unfold getExecutionPayloadEnvelope
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq]
  constructor
  · rintro ⟨_, rooted, rfl⟩
    exact ⟨rooted, rfl, rfl, rfl, rfl⟩
  · cases envelope
    rintro ⟨rooted, rfl, rfl, rfl, rfl⟩
    exact ⟨_, rooted, rfl⟩

variable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]

/-- The envelope of a payload passes most checks against the state after the block of its bid.

The block carries a bid that a builder built from the payload and its requests.

The block passes its steps, and commits to the root of the state after it.

The envelope then names that block, by the root that the check computes, and its parent.

It agrees with the bid that the state keeps on the builder, the mix, the gas limit and the hash.

It also agrees with that bid on the root of the requests.

The slot of the bid is the slot of the state, so a payload for that slot passes the slot check.

The payload also builds on the latest block hash of the state.

The lengths of the vectors that the preset sets must be positive, for the root of the block. -/
theorem getExecutionPayloadEnvelope_checks {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {pre post : BeaconState preset fork}
    (gloas : .glamsterdam ≤ fork) {block : BeaconBlock preset fork} {slot : Slot}
    {builderIndex : BuilderIndex} {value : Gwei}
    {envelope : ExecutionPayloadEnvelope preset fork}
    (built : getExecutionPayloadBid state payload requests blobKzgCommitments slot feeRecipient
      builderIndex value inclusionListBits =
        .ok (block.body.signedExecutionPayloadBid gloas).message)
    (processed : processBlock config checks engine pre block = .ok post)
    (committed : SszType.hashTreeRoot post = .ok block.stateRoot)
    (enveloped : getExecutionPayloadEnvelope block gloas payload requests = .ok envelope) :
    let bid := post.latestExecutionPayloadBid gloas
    (∃ stateRoot, SszType.hashTreeRoot post = .ok stateRoot ∧
      SszType.hashTreeRoot { post.latestBlockHeader with stateRoot } =
        .ok envelope.beaconBlockRoot) ∧
    envelope.parentBeaconBlockRoot = post.latestBlockHeader.parentRoot ∧
    envelope.builderIndex = bid.builderIndex ∧ envelope.payload.prevRandao = bid.prevRandao ∧
    envelope.payload.gasLimit = bid.gasLimit ∧ envelope.payload.blockHash = bid.blockHash ∧
    SszType.hashTreeRoot envelope.executionRequests = .ok bid.executionRequestsRoot ∧
    slot = post.slot ∧
    envelope.payload.parentHash = post.latestBlockHash gloas := by
  obtain ⟨blockRoot, rfl, rfl, builder, parentRoot⟩ :=
    getExecutionPayloadEnvelope_eq_ok_iff.mp enveloped
  obtain ⟨-, requestsRoot, parentHash, blockHash, randao, gasLimit, -, -, bidSlot, -⟩ :=
    getExecutionPayloadBid_eq_ok_iff.mp built
  have kept := latestExecutionPayloadBid_processBlock gloas processed
  obtain ⟨bodyRoot, bodyRooted, header⟩ := latestBlockHeader_processBlock gloas processed
  obtain ⟨_, _, withdrawn, _, _, _, _, _, bidOk, slotKept, -, -, -⟩ :=
    processBlock_steps gloas processed
  obtain ⟨-, -, checkedSlot, -⟩ :=
    checkExecutionPayloadBid_ok_iff.mp (processExecutionPayloadBid_ok bidOk).1
  simp only [kept, header]
  refine ⟨⟨block.stateRoot, committed, ?_⟩, parentRoot, builder, randao.symm, gasLimit.symm,
    blockHash.symm, requestsRoot, ?_, ?_⟩
  · rw [← blockRoot]
    exact BeaconBlock.hashTreeRoot_header bodyRooted
  · rw [← bidSlot, checkedSlot, slotKept]
    exact ((payloadInputs_processExecutionPayloadBid bidOk).slot).symm
  · rw [latestBlockHash_processBlock gloas processed, kept, parentHash]

end Build

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
private theorem verify_of_signed {key : Signatures.SecretKey}
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
  obtain ⟨signature', signs', verifies⟩ := Signatures.verify_sign key (packBytes root)
  rw [signs', Except.ok.injEq] at signs
  subst signs
  exact ⟨root, rooted, verifies⟩

/-- A bid signed with the key of its builder passes the check of its signature.

The bid must be for a slot of the current epoch, and its builder must have the public key. -/
theorem verifyExecutionPayloadBidSignature_of_sign {config : Config}
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
  obtain ⟨root, rooted, verifies⟩ := verify_of_signed signedBy
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

The signer is the builder of the envelope, or the proposer of the latest block for a self-build. -/
theorem verifyExecutionPayloadEnvelopeSignature_of_sign {config : Config}
    (gloas : .glamsterdam ≤ fork) {signed : SignedExecutionPayloadEnvelope preset fork}
    {key : Signatures.SecretKey}
    (owned : envelopeSignerKey state gloas signed.message.builderIndex =
      .ok (Signatures.skToPk key))
    (signedBy : getExecutionPayloadEnvelopeSignature config state signed.message key =
      .ok signed.signature) :
    verifyExecutionPayloadEnvelopeSignature config .bls state gloas signed = .ok true := by
  unfold getExecutionPayloadEnvelopeSignature at signedBy
  obtain ⟨root, rooted, verifies⟩ := verify_of_signed signedBy
  unfold verifyExecutionPayloadEnvelopeSignature
  rw [owned, show builderSigningRoot config state signed.message = .ok root from rooted]
  show Except.ok (Signatures.verify (packBytes (Signatures.skToPk key)) (packBytes root)
    (packBytes signed.signature)) = .ok true
  exact congrArg Except.ok verifies

end EthLib.Consensus
