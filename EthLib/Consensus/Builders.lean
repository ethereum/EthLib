module

public import EthLib.Consensus.Mutators

/-!
# `Consensus.Builders`

From Gloas: builder indices, and the rules that read or change the builders of a beacon state.

A withdrawal names a validator or a builder through one index field.

An index with the builder flag set names the builder at the index without the flag.

A builder is active once its deposit is finalized, until it starts to exit.

A builder can cover a bid when its balance pays the bid, its pending payments and a minimum deposit.

A settled payment of a bid joins the queue of builder withdrawals.

A read past the end of a list, or a 64-bit overflow, is an error.

The state has builders only from Gloas, so each rule that reads them takes a proof of the fork.

[EIP-7732] adds the builders, their index flag and their payments.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

/-- Whether an index names a builder: the builder flag is set. -/
def isBuilderIndex (index : ValidatorIndex) : Bool :=
  index &&& BUILDER_INDEX_FLAG != 0

/-- The index that names a builder in a withdrawal: the builder index with the flag set. -/
def convertBuilderIndexToValidatorIndex (index : BuilderIndex) : ValidatorIndex :=
  index ||| BUILDER_INDEX_FLAG

/-- The builder index of an index that names a builder: the index with the flag cleared. -/
def convertValidatorIndexToBuilderIndex (index : ValidatorIndex) : BuilderIndex :=
  index &&& ~~~BUILDER_INDEX_FLAG

/-- Whether withdrawal credentials are those of a builder: their first byte is the builder prefix.
-/
def isBuilderWithdrawalCredential (credentials : Bytes32) : Bool :=
  credentials[0] == BUILDER_WITHDRAWAL_PREFIX[0]

/-- The sum of the amounts that some withdrawals owe a builder, on natural numbers. -/
def owedBy (index : BuilderIndex) (withdrawals : List BuilderPendingWithdrawal) : Nat :=
  (withdrawals.map fun withdrawal =>
    if withdrawal.builderIndex = index then withdrawal.amount.toNat else 0).sum

variable {preset : Preset} {fork : Base.Fork}

/-- The state with the builder at an index of the registry replaced. -/
def BeaconState.putBuilder (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (index : Nat) (inside : index < (state.builders gloas).data.size) (builder : Builder) :
    BeaconState preset fork :=
  { state with builders := fun _ => ⟨(state.builders gloas).data.set index builder inside⟩ }

/-- From Gloas: the state with a builder of the registry replaced.

An index past the registry is an error. -/
def BeaconState.setBuilder (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (index : BuilderIndex) (builder : Builder) : Except AccessorError (BeaconState preset fork) :=
  if inside : index.toNat < (state.builders gloas).data.size then
    .ok (state.putBuilder gloas index.toNat inside builder)
  else .error (.builderIndexOutOfRange index)

/-- A builder of the registry. -/
def getBuilder (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (index : BuilderIndex) : Except AccessorError Builder :=
  match (state.builders gloas).data[index.toNat]? with
  | some builder => .ok builder
  | none => .error (.builderIndexOutOfRange index)

/-- Whether a builder is active.

Its deposit epoch is before the finalized epoch, and it has not started to exit. -/
def isActiveBuilder (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (index : BuilderIndex) : Except AccessorError Bool := do
  let builder ← getBuilder state gloas index
  return builder.depositEpoch < state.finalizedCheckpoint.epoch &&
    builder.withdrawableEpoch == FAR_FUTURE_EPOCH

/-- The sum, on natural numbers, of what a builder owes: its queued withdrawals and its payments.
-/
def pendingBuilderTotal (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (index : BuilderIndex) : Nat :=
  owedBy index (state.builderPendingWithdrawals gloas).data.toList +
    owedBy index ((state.builderPendingPayments gloas).toList.map (·.withdrawal))

/-- The balance that a builder still owes: its queued withdrawals and the payments of its bids.

A sum of 2^64 or more is an error, as in 64-bit arithmetic. -/
def getPendingBalanceToWithdrawForBuilder (state : BeaconState preset fork)
    (gloas : .glamsterdam ≤ fork) (index : BuilderIndex) : Except AccessorError Gwei := do
  let total := pendingBuilderTotal state gloas index
  if 2 ^ 64 ≤ total then throw .balanceOverflow
  return total.toUInt64

/-- Whether a builder can pay a bid of an amount.

Its balance must hold the amount, what it owes, and the minimum deposit. -/
def canBuilderCoverBid (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (index : BuilderIndex) (bidAmount : Gwei) : Except AccessorError Bool := do
  let builder ← getBuilder state gloas index
  let pending ← getPendingBalanceToWithdrawForBuilder state gloas index
  let minBalance ← liftArith (addChecked preset.MIN_DEPOSIT_AMOUNT pending)
  if builder.balance < minBalance then return false
  return bidAmount ≤ builder.balance - minBalance

/-- The attesting balance that releases the payment of a bid.

It is a fixed share, six tenths, of the active balance of one slot. -/
def getBuilderPaymentQuorumThreshold (state : BeaconState preset fork) :
    Except AccessorError Gwei := do
  let perSlot := (← getTotalActiveBalance state) / preset.SLOTS_PER_EPOCH
  let quorum ← liftArith (mulChecked perSlot BUILDER_PAYMENT_THRESHOLD_NUMERATOR)
  return quorum / BUILDER_PAYMENT_THRESHOLD_DENOMINATOR

/-- The state in which a builder starts to exit.

It may withdraw a fixed delay after the current epoch.

The rule sets that epoch even if the builder has already started to exit. -/
def initiateBuilderExit (config : Config) (state : BeaconState preset fork)
    (gloas : .glamsterdam ≤ fork) (index : BuilderIndex) :
    Except AccessorError (BeaconState preset fork) := do
  let builder ← getBuilder state gloas index
  let withdrawableEpoch ←
    liftArith (addChecked (getCurrentEpoch state) config.MIN_BUILDER_WITHDRAWABILITY_DELAY)
  state.setBuilder gloas index { builder with withdrawableEpoch }

/-- The state after the payment at a position of the pending payments is settled.

A payment of a positive amount joins the queue of builder withdrawals.

The position then holds the payment of no bid. -/
def settleBuilderPayment (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (paymentIndex : UInt64) : Except AccessorError (BeaconState preset fork) :=
  let payments := state.builderPendingPayments gloas
  if inRange : paymentIndex.toNat < 2 * preset.SLOTS_PER_EPOCH.toNat then
    let payment := payments[paymentIndex.toNat]
    let withdrawals := (state.builderPendingWithdrawals gloas).data
    let withdrawals :=
      if 0 < payment.withdrawal.amount then withdrawals.push payment.withdrawal else withdrawals
    .ok { state with
      builderPendingWithdrawals := fun _ => ⟨withdrawals⟩
      builderPendingPayments := fun _ => payments.set paymentIndex.toNat .empty }
  else .error (.paymentIndexOutOfRange paymentIndex)

end EthLib.Consensus
