module

public import EthLib.Consensus.Transition.Operations

/-!
# `Consensus.Transition.ParentPayload`

From Gloas: the payload of the parent block, which the next block applies.

A block of Gloas carries no payload.

Its builder reveals the payload later, in an envelope, and the next block takes its effects.

That next block names the hash of the parent payload that it builds on, in its own bid.

If that hash is the hash of the parent bid, the parent payload was revealed, and the parent is full.

Otherwise the parent is empty, and its payload has no effect.

A full parent applies its payload, in this order:

* the payment of its builder is settled;
* the requests of its payload run, at the slot of the new block;
* its slot is marked as having a payload, and its hash becomes the latest block hash.

The block carries the requests of the parent payload, which must match the root in the parent bid.

[EIP-7732] moves the payload out of the block.

[EIP-8282] adds the requests of builders.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
[EIP-8282]: https://eips.ethereum.org/EIPS/eip-8282#consensus-layer-processing
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz.SszType

variable {preset : Preset} {fork : Base.Fork}

/-- From Gloas: whether the requests of a payload hold no request of any type. -/
def ExecutionRequests.isEmpty (requests : ExecutionRequests preset fork)
    (gloas : .glamsterdam ≤ fork) : Bool :=
  requests.deposits.data.isEmpty && requests.withdrawals.data.isEmpty &&
    requests.consolidations.data.isEmpty && (requests.builderDeposits gloas).data.isEmpty &&
    (requests.builderExits gloas).data.isEmpty

/-- From Gloas: the position of the pending payment of the block at a slot, if it has one.

A block of the current epoch has its payment in the second half of the pending payments.

A block of the previous epoch has it in the first half.

The position is read against the epoch of the state.

An older block's payment has left the pending payments.

A block of a later epoch has no position yet. -/
def slotPaymentPosition (state : BeaconState preset fork) (slot : Slot) : Option UInt64 :=
  let epoch := computeEpochAtSlot preset slot
  let position := slot % preset.SLOTS_PER_EPOCH
  if epoch = getCurrentEpoch state then some (preset.SLOTS_PER_EPOCH + position)
  else if epoch = getPreviousEpoch state then some position
  else none

/-- From Gloas: the position of the pending payment of the parent's builder, if it has one. -/
def parentPaymentPosition (state : BeaconState preset fork) : Option UInt64 :=
  slotPaymentPosition state state.latestBlockHeader.slot

/-- From Gloas: the state after the payment of the builder of the parent payload.

A pending payment of the parent is settled.

If the parent has none and its bid has a value, that value joins the builder withdrawals. -/
def settleParentPayment (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) :
    Except TransitionError (BeaconState preset fork) :=
  match parentPaymentPosition state with
  | some position => liftAccessor (settleBuilderPayment state gloas position)
  | none =>
    let parentBid := state.latestExecutionPayloadBid gloas
    if 0 < parentBid.value then
      let withdrawal : BuilderPendingWithdrawal :=
        ⟨parentBid.feeRecipient, parentBid.value, parentBid.builderIndex⟩
      let withdrawals := (state.builderPendingWithdrawals gloas).data.push withdrawal
      .ok { state with builderPendingWithdrawals := fun _ => ⟨withdrawals⟩ }
    else .ok state

/-- From Gloas: the state after the requests of the parent payload.

The deposit requests run first, then the withdrawal and consolidation requests.

The deposit and exit requests of builders follow. -/
def processParentRequests (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (requests : ExecutionRequests preset fork) :
    Except TransitionError (BeaconState preset fork) := do
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) gloas
  let state ← requests.deposits.data.foldlM (processDepositRequest · electra ·) state
  let state ← requests.withdrawals.data.foldlM (processWithdrawalRequest config · electra ·) state
  let state ←
    requests.consolidations.data.foldlM (processConsolidationRequest config · electra ·) state
  let state ← (requests.builderDeposits gloas).data.foldlM
    (processBuilderDepositRequest config checks · gloas ·) state
  (requests.builderExits gloas).data.foldlM (processBuilderExitRequest config · gloas ·) state

/-- From Gloas: the state after the payload of a full parent, given its requests.

Each list of requests other than deposits must hold no more than its most per payload.

The payment of the builder is settled before the requests run.

So a builder whose payment is still pending cannot exit by a request of the same payload.

The slot of the parent is then marked as having a payload.

The hash of the parent bid becomes the latest block hash. -/
def applyParentExecutionPayload (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (requests : ExecutionRequests preset fork) :
    Except TransitionError (BeaconState preset fork) := do
  let parentBid := state.latestExecutionPayloadBid gloas
  let parentSlot := state.latestBlockHeader.slot
  checkCount requests.withdrawals.data.size preset.MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD
  checkCount requests.consolidations.data.size preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD
  checkCount (requests.builderDeposits gloas).data.size
    preset.MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD
  checkCount (requests.builderExits gloas).data.size preset.MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD
  let state ← settleParentPayment state gloas
  let state ← processParentRequests config checks state gloas requests
  let bits ← liftAccessor
    (writeCircular (state.executionPayloadAvailability gloas).bits parentSlot true)
  return { state with
    executionPayloadAvailability := fun _ => ⟨bits⟩
    latestBlockHash := fun _ => parentBid.blockHash }

/-- From Gloas: the state after the parent payload, as a block finds it.

The parent is full if the bid of the block builds on the hash of the parent bid.

An empty parent leaves the state as it is, and the block must then carry no request.

For a full parent, the root of the requests of the block must be the root in the parent bid.

The payload of the parent then applies with these requests. -/
def processParentExecutionPayload (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (body : BeaconBlockBody preset fork) : Except TransitionError (BeaconState preset fork) := do
  let bid := (body.signedExecutionPayloadBid gloas).message
  let parentBid := state.latestExecutionPayloadBid gloas
  let requests := body.parentExecutionRequests gloas
  if bid.parentBlockHash ≠ parentBid.blockHash then
    ensure (requests.isEmpty gloas) .parentRequestsNotEmpty
    return state
  let root ← liftSsz (hashTreeRoot requests)
  ensure (root = parentBid.executionRequestsRoot) .wrongParentRequestsRoot
  applyParentExecutionPayload config checks state gloas requests

end EthLib.Consensus
