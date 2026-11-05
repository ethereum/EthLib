module

public import EthLib.Consensus.Builders

/-!
# `Consensus.Transition.BuilderPayments`

From Gloas: the epoch step that pays the bids of the previous epoch, or cancels them.

The state keeps the payments of the bids of two epochs: the previous one, then the current one.

At the end of an epoch, some payments of the previous epoch join the queue of withdrawals.

Those are the payments whose block gathered enough attesting balance.

The quorum is six tenths of the active balance of one slot.

The payments of the current epoch then move to the first half, and the second half empties.

[EIP-7732] adds the payments.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork}

/-- The withdrawals of the payments of the first epoch that reach a quorum, in their order. -/
def releasedPayments (payments : List BuilderPendingPayment) (perEpoch : Nat) (quorum : Gwei) :
    List BuilderPendingWithdrawal :=
  ((payments.take perEpoch).filter (quorum ≤ ·.weight)).map (·.withdrawal)

/-- The payments moved by one epoch: the second half becomes the first, and the second is empty.
-/
def shiftPayments (payments : BuilderPendingPayments preset) : BuilderPendingPayments preset :=
  Vector.ofFn fun (position : Fin _) =>
    if early : position.val < preset.SLOTS_PER_EPOCH.toNat then
      payments[position.val + preset.SLOTS_PER_EPOCH.toNat]'(by omega)
    else BuilderPendingPayment.empty

/-- The state after the payments of the previous epoch are settled at the end of an epoch.

Those that reach the quorum join the withdrawals, and the current epoch's payments move down. -/
def processBuilderPendingPayments (state : BeaconState preset fork)
    (gloas : .glamsterdam ≤ fork) : Except AccessorError (BeaconState preset fork) := do
  let quorum ← getBuilderPaymentQuorumThreshold state
  let payments := state.builderPendingPayments gloas
  let released := releasedPayments payments.toList preset.SLOTS_PER_EPOCH.toNat quorum
  let withdrawals := (state.builderPendingWithdrawals gloas).data ++ released.toArray
  return { state with
    builderPendingWithdrawals := fun _ => ⟨withdrawals⟩
    builderPendingPayments := fun _ => shiftPayments payments }

end EthLib.Consensus
