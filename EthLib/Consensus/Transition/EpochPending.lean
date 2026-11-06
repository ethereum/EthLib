module

public import EthLib.Consensus.Transition.Operations

/-!
# `Consensus.Transition.EpochPending`

From Electra: the pending deposits that an epoch applies, as [EIP-7251] specifies.

Deposits from blocks and from requests wait in one queue, in order.

At the end of an epoch the queue is read from its front, and stops at the first deposit that:

* comes as a request while deposits of the old mechanism remain, in Electra only;
* entered the queue after the start of the finalized epoch;
* would pass the most deposits per epoch; or
* would pass the churn of deposits, which then carries over to the next epoch.

Before Gloas the churn of deposits is the churn that activations and exits share.

From Gloas it is the churn of activations alone, as [EIP-8061] specifies.

A deposit to a withdrawn validator is credited outside the churn.

A deposit to a validator that exits waits at the end of the queue.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
[EIP-8061]: https://eips.ethereum.org/EIPS/eip-8061#deposit-processing
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork}

/-- From Electra: where a pass over the pending deposits stopped. -/
structure PendingDepositsPass (preset : Preset) (fork : Base.Fork) where
  /-- The state with the deposits credited so far. -/
  state : BeaconState preset fork
  /-- The deposits that the pass did not reach, in order. -/
  rest : List PendingDeposit
  /-- The deposits to validators that exit, in order, which wait at the end of the queue. -/
  postponed : Array PendingDeposit
  /-- The amount that the deposits credited in the churn took. -/
  processed : Gwei
  /-- Whether the pass stopped at a deposit beyond the churn. -/
  churnReached : Bool

/-- From Electra: whether a validator with a key exits, and whether it is withdrawn.

A key that no validator has is neither. -/
def depositTargetStatus (state : BeaconState preset fork) (nextEpoch : Epoch)
    (pubkey : BLSPubkey) : Bool × Bool :=
  match state.validators.data.find? (·.pubkey == pubkey) with
  | some validator =>
    (validator.exitEpoch < FAR_FUTURE_EPOCH, validator.withdrawableEpoch < nextEpoch)
  | none => (false, false)

/-- From Electra: one pass over the pending deposits, from the front.

The pass stops at a deposit that the stop condition holds for, and after the most per epoch.

It also stops at a deposit beyond the churn that is available.

The deposits not reached and those postponed never outnumber the deposits read. -/
def passPendingDeposits (config : Config) (checks : SignatureChecks)
    (stop : PendingDeposit → Bool) (nextEpoch : Epoch) (available : Gwei)
    (state : BeaconState preset fork) (processed : Gwei) (count : Nat)
    (postponed : Array PendingDeposit) :
    (deposits : List PendingDeposit) →
      Except TransitionError { pass : PendingDepositsPass preset fork //
        pass.rest.length + pass.postponed.size ≤ deposits.length + postponed.size }
  | [] => return ⟨⟨state, [], postponed, processed, false⟩, by simp⟩
  | deposit :: rest => do
    if stop deposit || preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat ≤ count then
      return ⟨⟨state, deposit :: rest, postponed, processed, false⟩, Nat.le_refl _⟩
    let (exited, withdrawn) := depositTargetStatus state nextEpoch deposit.pubkey
    if withdrawn then
      let state ← applyPendingDeposit config checks state deposit
      let pass ← passPendingDeposits config checks stop nextEpoch available state processed
        (count + 1) postponed rest
      return ⟨pass.1, by have := pass.2; simp only [List.length_cons]; omega⟩
    else if exited then
      let pass ← passPendingDeposits config checks stop nextEpoch available state processed
        (count + 1) (postponed.push deposit) rest
      return ⟨pass.1, by have := pass.2; simp only [Array.size_push] at this; simp; omega⟩
    else
      let total ← liftAccessor (liftArith (addChecked processed deposit.amount))
      if available < total then
        return ⟨⟨state, deposit :: rest, postponed, processed, true⟩, Nat.le_refl _⟩
      let state ← applyPendingDeposit config checks state deposit
      let pass ← passPendingDeposits config checks stop nextEpoch available state total
        (count + 1) postponed rest
      return ⟨pass.1, by have := pass.2; simp only [List.length_cons]; omega⟩

/-- In Electra: whether deposits of the old mechanism remain before the first request.

From Fulu there are none. -/
def bridgeDepositsPending (state : BeaconState preset fork) : Bool :=
  if electra : .pectra ≤ fork ∧ fork < .fusaka then
    have before : fork < .hegota := Nat.lt_trans electra.2 (by decide)
    state.eth1DepositIndex before < state.depositRequestsStartIndex ⟨electra.1, before⟩
  else false

/-- From Electra: whether a pending deposit waits for a later epoch.

It waits if it entered the queue after a slot, the first slot of the finalized epoch.

In Electra a request also waits while deposits of the old mechanism remain. -/
def depositWaits (state : BeaconState preset fork) (finalizedSlot : Slot)
    (deposit : PendingDeposit) : Bool :=
  (bridgeDepositsPending state && GENESIS_SLOT < deposit.slot) || finalizedSlot < deposit.slot

/-- From Electra: the state after the pending deposits of an epoch.

The churn available is the churn left from the last epoch and the churn of deposits.

A request waits while deposits of the old mechanism remain, in Electra only.

The queue keeps the deposits not reached, then the postponed ones.

If the pass stopped at the churn, the churn not used carries over, and else none does.

A 64-bit overflow is an error. -/
def processPendingDeposits (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (electra : .pectra ≤ fork) :
    Except TransitionError (BeaconState preset fork) := do
  let nextEpoch ← liftAccessor (liftArith (addChecked (getCurrentEpoch state) 1))
  let churn ← liftAccessor (depositChurnLimit config state)
  let available ←
    liftAccessor (liftArith (addChecked (state.depositBalanceToConsume electra) churn))
  let finalizedSlot ← liftAccessor
    (liftArith (computeStartSlotAtEpoch preset state.finalizedCheckpoint.epoch))
  let queue := state.pendingDeposits electra
  let pass ← passPendingDeposits config checks (depositWaits state finalizedSlot) nextEpoch
    available state 0 0 #[] queue.data.toList
  let pending : PendingDeposits preset fork :=
    ⟨pass.1.rest.toArray ++ pass.1.postponed, fun before => by
      have fits : pass.1.rest.length + pass.1.postponed.size ≤ queue.data.size := by
        simpa using pass.2
      have bound := queue.bound before
      rw [Array.size_append, List.size_toArray]
      omega⟩
  let carried ← if pass.1.churnReached then
      liftAccessor (liftArith (subChecked available pass.1.processed))
    else pure 0
  return { pass.1.state with
    pendingDeposits := fun _ => pending
    depositBalanceToConsume := fun _ => carried }

end EthLib.Consensus
