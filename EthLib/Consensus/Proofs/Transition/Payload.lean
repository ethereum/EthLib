module

public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Consensus.Transition.Payload

/-!
# Proofs: the bid of a block

A bid passes its checks exactly when each check of the specification holds.

After a valid bid, the state keeps the bid.

A self-built bid has no value, and a bid with no value records no payment.

A bid with a value records one payment, at the position of its slot in the next epoch.

That payment pays the bid's value from its builder to the proposer of the slot.

An envelope passes its checks exactly when each check of the specification holds.

An execution layer that rejects every payload rejects every envelope.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork} {gloas : .glamsterdam ≤ fork}

/-- A valid bid passes its checks, records its payment, and is kept by the state. -/
theorem processExecutionPayloadBid_ok {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    checkExecutionPayloadBid config checks state gloas signed = .ok () ∧
      ∃ recorded, recordBidPayment state gloas signed.message = .ok recorded ∧
        after = { recorded with latestExecutionPayloadBid := fun _ => signed.message } := by
  obtain ⟨u, checked, rest⟩ := bind_ok_iff.mp computed
  obtain ⟨recorded, record, kept⟩ := bind_ok_iff.mp rest
  exact ⟨checked, recorded, record, (Except.ok.inj kept).symm⟩

/-- After a valid bid, the state keeps the bid. -/
theorem latestExecutionPayloadBid_processExecutionPayloadBid
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    after.latestExecutionPayloadBid gloas = signed.message := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayloadBid_ok computed
  rfl

/-- A bid passes its checks exactly when each of them holds.

Its builder passes its checks, and it commits to at most the blobs of a block.

It is for the slot of the state, after genesis.

It builds on the latest block hash, and its block hash differs from that parent hash.

It builds on the root of the block at the slot before, and on the RANDAO mix of the current epoch.
-/
theorem checkExecutionPayloadBid_ok_iff {signed : SignedExecutionPayloadBid preset fork} :
    checkExecutionPayloadBid config checks state gloas signed = .ok () ↔
      let bid := signed.message
      checkBidBuilder config checks state gloas signed = .ok () ∧
      bid.blobKzgCommitments.data.size ≤
        (config.getBlobParameters (getCurrentEpoch state)).maxBlobsPerBlock.toNat ∧
      bid.slot = state.slot ∧ GENESIS_SLOT < state.slot ∧
      bid.parentBlockHash = state.latestBlockHash gloas ∧ bid.blockHash ≠ bid.parentBlockHash ∧
      getBlockRootAtSlot state (state.slot - 1) = .ok bid.parentBlockRoot ∧
      getRandaoMix state (getCurrentEpoch state) = .ok bid.prevRandao := by
  unfold checkExecutionPayloadBid
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, exists_const]
  constructor
  · rintro ⟨⟨⟩, builder, blobs, slot, genesis, parentHash, blockHash, root, rootOk, rootEq, mix,
      mixOk, mixEq⟩
    exact ⟨builder, blobs, slot, genesis, parentHash, blockHash, rootEq ▸ rootOk, mixEq ▸ mixOk⟩
  · rintro ⟨builder, blobs, slot, genesis, parentHash, blockHash, rootOk, mixOk⟩
    exact ⟨(), builder, blobs, slot, genesis, parentHash, blockHash, _, rootOk, rfl, _, mixOk, rfl⟩

/-- A self-built bid that passes its checks has no value. -/
theorem value_eq_zero_of_selfBuild {signed : SignedExecutionPayloadBid preset fork}
    (checked : checkExecutionPayloadBid config checks state gloas signed = .ok ())
    (selfBuild : signed.message.builderIndex = BUILDER_INDEX_SELF_BUILD) :
    signed.message.value = 0 := by
  unfold checkExecutionPayloadBid at checked
  obtain ⟨u, first, _⟩ := bind_ok_iff.mp checked
  unfold checkBidBuilder at first
  simp only [selfBuild, ↓reduceIte, ensure_ok_iff] at first
  exact first.1

/-- A bid with no value records no payment. -/
theorem recordBidPayment_of_value_eq_zero {bid : ExecutionPayloadBid preset fork}
    (free : bid.value = 0) : recordBidPayment state gloas bid = .ok state := by
  unfold recordBidPayment
  simp only [free, UInt64.lt_irrefl, ↓reduceIte]
  rfl

/-- A valid self-built bid leaves the pending payments as they were. -/
theorem builderPendingPayments_processExecutionPayloadBid_selfBuild
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after)
    (selfBuild : signed.message.builderIndex = BUILDER_INDEX_SELF_BUILD) :
    after.builderPendingPayments gloas = state.builderPendingPayments gloas := by
  obtain ⟨checked, recorded, record, rfl⟩ := processExecutionPayloadBid_ok computed
  rw [recordBidPayment_of_value_eq_zero (value_eq_zero_of_selfBuild checked selfBuild),
    Except.ok.injEq] at record
  subst record
  rfl

/-- A bid with a value records one payment to the proposer of the slot.

The payment sits at the position of the bid's slot in the second epoch of the list.

Every other field of the state is unchanged. -/
theorem recordBidPayment_of_pos {bid : ExecutionPayloadBid preset fork}
    {recorded : BeaconState preset fork} (paid : 0 < bid.value)
    (record : recordBidPayment state gloas bid = .ok recorded) :
    ∃ proposer, ∃ position : Fin (2 * preset.SLOTS_PER_EPOCH.toNat),
      getBeaconProposerIndex state = .ok proposer ∧
      position.val = preset.SLOTS_PER_EPOCH.toNat +
        (bid.slot % preset.SLOTS_PER_EPOCH).toNat ∧
      recorded = { state with builderPendingPayments := fun _ =>
        (state.builderPendingPayments gloas).set position (bidPayment bid proposer) } := by
  unfold recordBidPayment at record
  simp only [paid, ↓reduceIte] at record
  obtain ⟨proposer, found, rest⟩ := bind_ok_iff.mp record
  obtain ⟨position, placed, kept⟩ := bind_ok_iff.mp rest
  rw [liftAccessor_ok] at found
  unfold bidPaymentPosition at placed
  split at placed
  · cases placed
  cases placed
  exact ⟨proposer, _, found, rfl, (Except.ok.inj kept).symm⟩

/-- A valid bid changes only the pending payments of builders, and becomes the latest bid. -/
theorem processExecutionPayloadBid_eq {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    ∃ payments, after = { state with
      builderPendingPayments := payments
      latestExecutionPayloadBid := fun _ => signed.message } := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok computed
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact ⟨_, rfl⟩
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at recordedOk
    subst recordedOk
    exact ⟨_, rfl⟩

/-- The payment of a bid pays its value, from its builder, to the address it names. -/
theorem bidPayment_withdrawal (bid : ExecutionPayloadBid preset fork) (proposer : ValidatorIndex) :
    (bidPayment bid proposer).withdrawal = ⟨bid.feeRecipient, bid.value, bid.builderIndex⟩ ∧
      (bidPayment bid proposer).weight = 0 ∧ (bidPayment bid proposer).proposerIndex = proposer :=
  ⟨rfl, rfl, rfl⟩

/-- An envelope passes its checks exactly when each of them holds.

Its signer signed it, and it names the latest block of the state and that block's parent.

It agrees with the bid of that block on the builder, the RANDAO mix and the gas limit.

It also agrees on the block hash and the root of its requests.

Its payload is for the slot of the state, extends the latest block hash and has the slot's time.

Its withdrawals have the root of those that the state expects.

The bid commits to a bounded number of blobs, and the execution layer accepts the request. -/
theorem verifyExecutionPayloadEnvelope_ok_iff {engine : ExecutionEngine preset fork}
    {signed : SignedExecutionPayloadEnvelope preset fork} :
    verifyExecutionPayloadEnvelope config checks engine state gloas signed = .ok () ↔
      let envelope := signed.message
      let payload := envelope.payload
      let bid := state.latestExecutionPayloadBid gloas
      verifyExecutionPayloadEnvelopeSignature config checks state gloas signed = .ok true ∧
      (∃ stateRoot, Serialization.Ssz.SszType.hashTreeRoot state = .ok stateRoot ∧
        Serialization.Ssz.SszType.hashTreeRoot { state.latestBlockHeader with stateRoot } =
          .ok envelope.beaconBlockRoot) ∧
      envelope.parentBeaconBlockRoot = state.latestBlockHeader.parentRoot ∧
      envelope.builderIndex = bid.builderIndex ∧ payload.prevRandao = bid.prevRandao ∧
      payload.gasLimit = bid.gasLimit ∧ payload.blockHash = bid.blockHash ∧
      Serialization.Ssz.SszType.hashTreeRoot envelope.executionRequests =
        .ok bid.executionRequestsRoot ∧
      payload.slotNumber gloas = state.slot ∧ payload.parentHash = state.latestBlockHash gloas ∧
      computeTimeAtSlot config state.genesisTime state.slot = .ok payload.timestamp ∧
      (∃ root, Serialization.Ssz.SszType.hashTreeRoot
          (payload.withdrawals (Nat.le_trans (by decide) gloas)) = .ok root ∧
        Serialization.Ssz.SszType.hashTreeRoot (state.payloadExpectedWithdrawals gloas) =
          .ok root) ∧
      ∃ bound, engine.verifyAndNotifyNewPayload
        (envelope.newPayloadRequest bid.blobKzgCommitments.data bound) = .ok true := by
  unfold verifyExecutionPayloadEnvelope
  simp only [bind_ok_iff, ensure_ok_iff, liftSsz_ok, liftAccessor_ok, liftArith, mapError_ok_iff,
    exists_const]
  constructor
  · rintro ⟨_, signature, rfl, stateRoot, stateRootOk, _, blockRootOk, rfl, parent, builder,
      randao, gas, hash, _, requestsOk, rfl, slot, parentHash, _, timeOk, rfl, _, withdrawalsOk,
      _, expectedOk, rfl, accepted⟩
    refine ⟨signature, ⟨stateRoot, stateRootOk, blockRootOk⟩, parent, builder, randao, gas, hash,
      requestsOk, slot, parentHash, timeOk, ⟨_, withdrawalsOk, expectedOk⟩, ?_⟩
    split at accepted
    · next bound =>
      simp only [bind_ok_iff, liftSsz_ok, ensure_ok_iff] at accepted
      obtain ⟨_, valid, rfl⟩ := accepted
      exact ⟨bound, valid⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at accepted
  · rintro ⟨signature, ⟨stateRoot, stateRootOk, blockRootOk⟩, parent, builder, randao, gas, hash,
      requestsOk, slot, parentHash, timeOk, ⟨_, withdrawalsOk, expectedOk⟩, bound, accepted⟩
    refine ⟨true, signature, rfl, stateRoot, stateRootOk, _, blockRootOk, rfl, parent, builder,
      randao, gas, hash, _, requestsOk, rfl, slot, parentHash, _, timeOk, rfl, _, withdrawalsOk,
      _, expectedOk, rfl, ?_⟩
    simp [bound, accepted, bind, Except.bind, liftSsz, Except.mapError, ensure]

/-- An execution layer that rejects every payload rejects every envelope. -/
theorem verifyExecutionPayloadEnvelope_constant_false
    {signed : SignedExecutionPayloadEnvelope preset fork} :
    verifyExecutionPayloadEnvelope config checks (.constant false) state gloas signed ≠ .ok () := by
  intro verified
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, _, accepted⟩ :=
    verifyExecutionPayloadEnvelope_ok_iff.mp verified
  simp [ExecutionEngine.constant] at accepted

end EthLib.Consensus
