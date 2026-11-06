module

public import EthLib.Consensus.Accessors

/-!
# `Consensus.Churn`

From Electra: the balance that may enter or leave the active validators in one epoch.

That balance is the churn of an epoch.

It derives from the total active balance, and is rounded down to a whole increment.

Exits and consolidations each wait in a queue.

A queue keeps its earliest open epoch and the churn that this epoch still has.

An amount that does not fit there takes as many later epochs as it needs, and leaves at the last.

In Electra, activations and exits share one part of the churn, as [EIP-7251] specifies.

Consolidations take the rest of the churn.

From Gloas, activations, exits and consolidations have separate churns, as [EIP-8061] specifies.

Each of them is a share of the total active balance.

EIP-8061 is in Last Call.

The churn of an epoch is a natural number of Gwei, so a churn of zero gives no later epoch.

An amount that needs a later epoch then fails, since the number of epochs divides by zero.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
[EIP-8061]: https://eips.ethereum.org/EIPS/eip-8061#churn-computations
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork}

/-- An amount rounded down to a whole number of effective balance increments. -/
def roundToIncrement (preset : Preset) (amount : Gwei) : Gwei :=
  amount - amount % preset.EFFECTIVE_BALANCE_INCREMENT

/-- From Electra: the churn of the current epoch, before its split.

It is a share of the total active balance, and at least a minimum. -/
def getBalanceChurnLimit (config : Config) (state : BeaconState preset fork) :
    Except AccessorError Gwei := do
  return roundToIncrement preset
    (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
      ((← getTotalActiveBalance state) / config.CHURN_LIMIT_QUOTIENT))

/-- From Electra: the part of the churn that activations and exits share, up to a maximum. -/
def getActivationExitChurnLimit (config : Config) (state : BeaconState preset fork) :
    Except AccessorError Gwei := do
  return min config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT (← getBalanceChurnLimit config state)

/-- From Gloas: the churn of exits.

It is a share of the total active balance, and at least a minimum. -/
def getExitChurnLimit (config : Config) (state : BeaconState preset fork) :
    Except AccessorError Gwei := do
  return roundToIncrement preset
    (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
      ((← getTotalActiveBalance state) / config.CHURN_LIMIT_QUOTIENT_GLOAS))

/-- From Gloas: the churn of activations, which is the churn of exits up to a maximum. -/
def getActivationChurnLimit (config : Config) (state : BeaconState preset fork) :
    Except AccessorError Gwei := do
  return min config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS (← getExitChurnLimit config state)

/-- From Electra: the churn of consolidations.

In Electra it is the part of the churn that activations and exits do not take.

From Gloas it is its own share of the total active balance. -/
def getConsolidationChurnLimit (config : Config) (state : BeaconState preset fork) :
    Except AccessorError Gwei := do
  if .glamsterdam ≤ fork then
    return roundToIncrement preset
      ((← getTotalActiveBalance state) / config.CONSOLIDATION_CHURN_LIMIT_QUOTIENT)
  else
    -- The second churn is the first one up to a maximum, so the difference does not wrap.
    return (← getBalanceChurnLimit config state) - (← getActivationExitChurnLimit config state)

/-- From Electra: the churn of exits, which Gloas separates from that of activations. -/
def exitChurnLimit (config : Config) (state : BeaconState preset fork) :
    Except AccessorError Gwei :=
  if .glamsterdam ≤ fork then getExitChurnLimit config state
  else getActivationExitChurnLimit config state

/-- From Electra: the churn of pending deposits.

Before Gloas it is the churn that activations and exits share.

From Gloas it is the churn of activations alone. -/
def depositChurnLimit (config : Config) (state : BeaconState preset fork) :
    Except AccessorError Gwei :=
  if .glamsterdam ≤ fork then getActivationChurnLimit config state
  else getActivationExitChurnLimit config state

/-- The place of an amount in a queue, and the churn left in its epoch.

The queue holds its earliest open epoch and the churn left in it.

An exit or a consolidation leaves no earlier than a first epoch.

If that first epoch is past the earliest open one, the queue opens it with a full churn.

An amount that does not fit there takes the fewest later epochs whose churn covers the rest.

An epoch, a product or a sum of churn that reaches `2^64` is an error.

So is a churn of zero for an amount that needs a later epoch. -/
def churnQueue (earliestEpoch firstEpoch perEpochChurn churnLeft amount : UInt64) :
    Except ArithError (Epoch × Gwei) := do
  let epoch := max earliestEpoch firstEpoch
  let available := if earliestEpoch < epoch then perEpochChurn else churnLeft
  if amount ≤ available then return (epoch, available - amount)
  else
    -- The quotient is below the rest, so adding one does not wrap.
    let additional := (← divChecked (amount - available - 1) perEpochChurn) + 1
    let epoch ← addChecked epoch additional
    let available ← addChecked available (← mulChecked additional perEpochChurn)
    -- The added epochs cover the rest, so the difference does not wrap.
    return (epoch, available - amount)

/-- From Electra: the epoch at which an exit of a balance leaves.

The state comes back with the churn of the exit spent. -/
def computeExitEpochAndUpdateChurn (config : Config) (state : BeaconState preset fork)
    (electra : .pectra ≤ fork) (exitBalance : Gwei) :
    Except AccessorError (BeaconState preset fork × Epoch) := do
  let firstEpoch ← liftArith (computeActivationExitEpoch preset (getCurrentEpoch state))
  let perEpochChurn ← exitChurnLimit config state
  let (epoch, left) ← liftArith (churnQueue (state.earliestExitEpoch electra) firstEpoch
    perEpochChurn (state.exitBalanceToConsume electra) exitBalance)
  return ({ state with exitBalanceToConsume := fun _ => left, earliestExitEpoch := fun _ => epoch },
    epoch)

/-- From Electra: the epoch at which a consolidation of a balance takes effect.

The state comes back with the churn of the consolidation spent. -/
def computeConsolidationEpochAndUpdateChurn (config : Config) (state : BeaconState preset fork)
    (electra : .pectra ≤ fork) (consolidationBalance : Gwei) :
    Except AccessorError (BeaconState preset fork × Epoch) := do
  let firstEpoch ← liftArith (computeActivationExitEpoch preset (getCurrentEpoch state))
  let perEpochChurn ← getConsolidationChurnLimit config state
  let (epoch, left) ← liftArith (churnQueue (state.earliestConsolidationEpoch electra) firstEpoch
    perEpochChurn (state.consolidationBalanceToConsume electra) consolidationBalance)
  return ({ state with
    consolidationBalanceToConsume := fun _ => left, earliestConsolidationEpoch := fun _ => epoch },
    epoch)

end EthLib.Consensus
