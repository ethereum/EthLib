module

public import EthLib.Consensus.Proofs.Builders
public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Consensus.Transition.ParentPayload

/-!
# Proofs: the parent payload

An empty parent leaves the state as it is when the block carries no request.

It rejects a block that carries a request.

A full parent records its block hash, and marks its slot as having a payload.

The payment of its builder empties at most one pending payment.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork} {gloas : .glamsterdam ≤ fork}

/-- An empty parent leaves the state as it is when the block carries no request. -/
theorem processParentExecutionPayload_of_empty {body : BeaconBlockBody preset fork}
    (empty : (body.signedExecutionPayloadBid gloas).message.parentBlockHash ≠
      (state.latestExecutionPayloadBid gloas).blockHash)
    (noRequest : (body.parentExecutionRequests gloas).isEmpty gloas = true) :
    processParentExecutionPayload config checks state gloas body = .ok state := by
  simp [processParentExecutionPayload, empty, noRequest, ensure, bind, Except.bind, pure,
    Except.pure]

/-- An empty parent rejects a block that carries a request. -/
theorem processParentExecutionPayload_of_empty_requests {body : BeaconBlockBody preset fork}
    (empty : (body.signedExecutionPayloadBid gloas).message.parentBlockHash ≠
      (state.latestExecutionPayloadBid gloas).blockHash)
    (requests : (body.parentExecutionRequests gloas).isEmpty gloas = false) :
    processParentExecutionPayload config checks state gloas body =
      .error .parentRequestsNotEmpty := by
  simp [processParentExecutionPayload, empty, requests, ensure, bind, Except.bind]

/-- A full parent makes the hash of its bid the latest block hash. -/
theorem applyParentExecutionPayload_latestBlockHash {requests : ExecutionRequests preset fork}
    (computed : applyParentExecutionPayload config checks state gloas requests = .ok after) :
    after.latestBlockHash gloas = (state.latestExecutionPayloadBid gloas).blockHash := by
  simp only [applyParentExecutionPayload, bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  rfl

/-- A full parent marks its slot as having a payload.

The bit of its slot, modulo the length of the record, is set. -/
theorem applyParentExecutionPayload_available {requests : ExecutionRequests preset fork}
    (computed : applyParentExecutionPayload config checks state gloas requests = .ok after) :
    (after.executionPayloadAvailability gloas).bits[
      (state.latestBlockHeader.slot % preset.SLOTS_PER_HISTORICAL_ROOT).toNat]? = some true := by
  simp only [applyParentExecutionPayload, bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  rename_i written
  exact getElem?_writeCircular (liftAccessor_ok.mp written)

/-- The payment of the parent's builder changes no pending payment but the one it settles.

That one is at the position of the parent's slot, when the parent is of this epoch or the last. -/
theorem settleParentPayment_payments
    (computed : settleParentPayment state gloas = .ok after) (index : Nat)
    (inRange : index < 2 * preset.SLOTS_PER_EPOCH.toNat)
    (other : (parentPaymentPosition state).map UInt64.toNat ≠ some index) :
    (after.builderPendingPayments gloas)[index] = (state.builderPendingPayments gloas)[index] := by
  unfold settleParentPayment at computed
  split at computed
  · rename_i position settled
    obtain ⟨_, payments, _⟩ := settleBuilderPayment_spec (liftAccessor_ok.mp computed)
    rw [settled] at other
    simp only [Option.map_some, ne_eq, Option.some.injEq] at other
    simp only [payments]
    exact Serialization.Ssz.RootedVector.getElem_set_ne _ _ _ _ other
  · dsimp only at computed
    split at computed <;> cases computed <;> rfl

end EthLib.Consensus
