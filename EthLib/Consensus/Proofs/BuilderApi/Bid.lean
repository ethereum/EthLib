module

public import EthLib.Consensus.BuilderApi.Bid
public import EthLib.Consensus.Proofs.Containers.Execution

/-!
# Proofs: a builder serves a request, and a proposer accepts a bid, exactly when the rules hold

A builder serves a request exactly when its four rules hold.

So it serves only the key of the proposer of the slot of its state.

A request that it does not serve gets 400.

Every payload has a bid, and that bid carries the header of the payload.

A proposer accepts a bid exactly when its three rules hold.

So a bid whose signature verifies is accepted when its payload extends the state.

The payload must also pay the fee recipient that the proposer registered.
-/

@[expose] public section

namespace EthLib.Consensus.BuilderApi

open Base Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- A builder serves a request exactly when the four rules hold. -/
theorem isEligibleForBid_ok_true_iff {state : BeaconState preset fork}
    {range : HasBuilderApi fork} {registry : Registry} {slot : Slot} {parentHash : Hash32}
    {pubkey : BLSPubkey} :
    isEligibleForBid state range registry slot parentHash pubkey = .ok true ↔
      slot = state.slot ∧ (registry.find? pubkey).isSome ∧
      (∃ index proposer, getBeaconProposerIndex state = .ok index ∧
        getValidator state index = .ok proposer ∧ proposer.pubkey = pubkey) ∧
      parentHash = (state.latestExecutionPayloadHeader range).blockHash := by
  unfold isEligibleForBid
  by_cases hs : slot = state.slot
  · cases hr : registry.find? pubkey <;>
    cases hi : getBeaconProposerIndex state <;>
    (try rename_i index; cases hv : getValidator state index) <;>
    (try rename_i proposer; by_cases hk : pubkey = proposer.pubkey) <;>
    simp [*, bind, Except.bind, pure, Except.pure] <;>
    exact fun same => absurd same.symm hk
  · simp only [ne_eq, hs, not_false_eq_true, ↓reduceIte]
    simp [pure, Except.pure]

/-- A request that a builder serves names the key of the proposer of the slot of its state. -/
theorem isEligibleForBid_proposer {state : BeaconState preset fork}
    {range : HasBuilderApi fork} {registry : Registry} {slot : Slot} {parentHash : Hash32}
    {pubkey : BLSPubkey}
    (served : isEligibleForBid state range registry slot parentHash pubkey = .ok true) :
    ∃ index proposer, getBeaconProposerIndex state = .ok index ∧
      getValidator state index = .ok proposer ∧ proposer.pubkey = pubkey :=
  (isEligibleForBid_ok_true_iff.1 served).2.2.1

/-- A request that a builder does not serve gets 400, whether or not it has a bid. -/
theorem getHeaderStatus_of_not_eligible {state : BeaconState preset fork}
    {range : HasBuilderApi fork} {registry : Registry} {slot : Slot} {parentHash : Hash32}
    {pubkey : BLSPubkey} (offered : Bool)
    (refused : isEligibleForBid state range registry slot parentHash pubkey = .ok false) :
    getHeaderStatus state range registry slot parentHash pubkey offered = 400 := by
  simp [getHeaderStatus, refused]

/-- A request for another slot than that of the builder's state gets 400. -/
theorem getHeaderStatus_wrong_slot {state : BeaconState preset fork}
    {range : HasBuilderApi fork} {registry : Registry} {slot : Slot} {parentHash : Hash32}
    {pubkey : BLSPubkey} (offered : Bool) (other : slot ≠ state.slot) :
    getHeaderStatus state range registry slot parentHash pubkey offered = 400 := by
  have refused : isEligibleForBid state range registry slot parentHash pubkey = .ok false := by
    simp [isEligibleForBid, other, pure, Except.pure]
  exact getHeaderStatus_of_not_eligible offered refused

/-- The bid on a payload carries the header of the payload. -/
theorem getBid_header (payload : ExecutionPayload preset fork) (value : U256) (pubkey : BLSPubkey)
    (blobKzgCommitments : Since .dencun fork (BlobKZGCommitments preset fork))
    (executionRequests : Since .pectra fork (ExecutionRequests preset fork)) :
    BuilderBid.header <$> getBid payload value pubkey blobKzgCommitments executionRequests =
      payload.header := by
  obtain ⟨header, made⟩ := ExecutionPayload.header_total payload
  simp [getBid, made, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

/-- Every payload has a bid. -/
theorem getBid_total (payload : ExecutionPayload preset fork) (value : U256) (pubkey : BLSPubkey)
    (blobKzgCommitments : Since .dencun fork (BlobKZGCommitments preset fork))
    (executionRequests : Since .pectra fork (ExecutionRequests preset fork)) :
    ∃ bid, getBid payload value pubkey blobKzgCommitments executionRequests = .ok bid := by
  obtain ⟨header, made⟩ := ExecutionPayload.header_total payload
  exact ⟨_, by simp [getBid, made, bind, Except.bind, pure, Except.pure]; rfl⟩

/-- A proposer accepts a bid exactly when the three rules hold. -/
theorem processBid_ok_iff {config : Config} {checks : SignatureChecks}
    {state : BeaconState preset fork} {range : HasBuilderApi fork}
    {signed : SignedBuilderBid preset fork} {feeRecipient : ExecutionAddress} :
    processBid config checks state range signed feeRecipient = .ok () ↔
      signed.message.header.parentHash = (state.latestExecutionPayloadHeader range).blockHash ∧
      signed.message.header.feeRecipient = feeRecipient ∧
      verifyBuilderBidSignature config checks signed = .ok true := by
  unfold processBid
  by_cases hp : signed.message.header.parentHash =
      (state.latestExecutionPayloadHeader range).blockHash <;>
  by_cases hf : signed.message.header.feeRecipient = feeRecipient <;>
  cases hv : verifyBuilderBidSignature config checks signed <;>
  (try rename_i b; cases b) <;>
  simp [*, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure]

/-- A bid on a payload that extends the state and pays the fee recipient is accepted.

This holds when the signature of the bid verifies. -/
theorem processBid_getBid {config : Config} {checks : SignatureChecks}
    {state : BeaconState preset fork} {range : HasBuilderApi fork}
    {payload : ExecutionPayload preset fork} {value : U256} {pubkey : BLSPubkey}
    {blobKzgCommitments : Since .dencun fork (BlobKZGCommitments preset fork)}
    {executionRequests : Since .pectra fork (ExecutionRequests preset fork)}
    {bid : BuilderBid preset fork} {signature : BLSSignature} {feeRecipient : ExecutionAddress}
    (made : getBid payload value pubkey blobKzgCommitments executionRequests = .ok bid)
    (onParent : payload.parentHash = (state.latestExecutionPayloadHeader range).blockHash)
    (pays : payload.feeRecipient = feeRecipient)
    (signs : verifyBuilderBidSignature config checks ⟨bid, signature⟩ = .ok true) :
    processBid config checks state range ⟨bid, signature⟩ feeRecipient = .ok () := by
  obtain ⟨header, built⟩ := ExecutionPayload.header_total payload
  have bidOf : bid = ⟨header, blobKzgCommitments, executionRequests, value, pubkey⟩ := by
    simp [getBid, built, bind, Except.bind, pure, Except.pure] at made
    exact made.symm
  subst bidOf
  obtain ⟨parent, recipient⟩ := ExecutionPayload.header_parentHash_feeRecipient built
  exact processBid_ok_iff.2 ⟨parent.trans onParent, recipient.trans pays, signs⟩

end EthLib.Consensus.BuilderApi
