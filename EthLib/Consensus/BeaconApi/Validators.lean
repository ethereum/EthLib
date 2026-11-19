module

public import EthLib.Consensus.Accessors
public import EthLib.Consensus.Builders

/-!
# `Consensus.BeaconApi.Validators`

The statuses that the Beacon API gives to a validator and to a builder.

A validator has one of nine statuses, in four coarse groups: pending, active, exited, withdrawal.

The group follows the activation, exit and withdrawable epochs of the validator.

In a group, the status follows the eligibility epoch, the exit epoch, the slashing or the balance.

A builder is exited once its withdrawable epoch is set, and otherwise active or pending.

It is active once its deposit is before the finalized epoch.

The [API types] name both statuses; SOUNDNESS.md records where their conditions come from.

SOUNDNESS.md records the points that the source leaves open.

[API types]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/types/api.yaml
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base

variable {preset : Preset} {fork : Fork}

/-- The four groups of validator statuses. -/
inductive CoarseStatus where
  /-- Not yet active. -/
  | pending
  /-- Active. -/
  | active
  /-- Exited, and not yet withdrawable. -/
  | exited
  /-- Withdrawable. -/
  | withdrawal
  deriving DecidableEq, Repr

/-- The status of a validator. -/
inductive ValidatorStatus where
  /-- Pending, and not yet eligible for activation. -/
  | pendingInitialized
  /-- Pending, and eligible for activation. -/
  | pendingQueued
  /-- Active, with no exit. -/
  | activeOngoing
  /-- Active, with an exit, and not slashed. -/
  | activeExiting
  /-- Active, with an exit, and slashed. -/
  | activeSlashed
  /-- Exited, and not slashed. -/
  | exitedUnslashed
  /-- Exited, and slashed. -/
  | exitedSlashed
  /-- Withdrawable, with a balance left. -/
  | withdrawalPossible
  /-- Withdrawable, with no balance left. -/
  | withdrawalDone
  deriving DecidableEq, Repr

namespace CoarseStatus

/-- The name of a group, as the API writes it. -/
def name : CoarseStatus → String
  | .pending => "pending"
  | .active => "active"
  | .exited => "exited"
  | .withdrawal => "withdrawal"

end CoarseStatus

namespace ValidatorStatus

/-- The group of a status. -/
def coarse : ValidatorStatus → CoarseStatus
  | .pendingInitialized | .pendingQueued => .pending
  | .activeOngoing | .activeExiting | .activeSlashed => .active
  | .exitedUnslashed | .exitedSlashed => .exited
  | .withdrawalPossible | .withdrawalDone => .withdrawal

/-- The name of a status, as the API writes it. -/
def name : ValidatorStatus → String
  | .pendingInitialized => "pending_initialized"
  | .pendingQueued => "pending_queued"
  | .activeOngoing => "active_ongoing"
  | .activeExiting => "active_exiting"
  | .activeSlashed => "active_slashed"
  | .exitedUnslashed => "exited_unslashed"
  | .exitedSlashed => "exited_slashed"
  | .withdrawalPossible => "withdrawal_possible"
  | .withdrawalDone => "withdrawal_done"

/-- The condition of the source for a status, on a validator, its balance and an epoch.

Each condition is the condition of its group, with the condition inside the group. -/
def Holds (status : ValidatorStatus) (validator : Validator) (balance : Gwei) (epoch : Epoch) :
    Prop :=
  match status with
  | .pendingInitialized =>
    epoch < validator.activationEpoch ∧
      validator.activationEligibilityEpoch = FAR_FUTURE_EPOCH
  | .pendingQueued =>
    epoch < validator.activationEpoch ∧
      validator.activationEligibilityEpoch < FAR_FUTURE_EPOCH
  | .activeOngoing =>
    validator.activationEpoch ≤ epoch ∧ epoch < validator.exitEpoch ∧
      validator.exitEpoch = FAR_FUTURE_EPOCH
  | .activeExiting =>
    validator.activationEpoch ≤ epoch ∧ epoch < validator.exitEpoch ∧
      validator.exitEpoch < FAR_FUTURE_EPOCH ∧ validator.slashed = false
  | .activeSlashed =>
    validator.activationEpoch ≤ epoch ∧ epoch < validator.exitEpoch ∧
      validator.exitEpoch < FAR_FUTURE_EPOCH ∧ validator.slashed = true
  | .exitedUnslashed =>
    validator.exitEpoch ≤ epoch ∧ epoch < validator.withdrawableEpoch ∧
      validator.slashed = false
  | .exitedSlashed =>
    validator.exitEpoch ≤ epoch ∧ epoch < validator.withdrawableEpoch ∧
      validator.slashed = true
  | .withdrawalPossible => validator.withdrawableEpoch ≤ epoch ∧ balance ≠ 0
  | .withdrawalDone => validator.withdrawableEpoch ≤ epoch ∧ balance = 0

end ValidatorStatus

/-- The status of a validator with a balance at an epoch.

The group is the first that applies, in the order pending, active, exited, withdrawal. -/
def validatorStatus (validator : Validator) (balance : Gwei) (epoch : Epoch) : ValidatorStatus :=
  if epoch < validator.activationEpoch then
    if validator.activationEligibilityEpoch = FAR_FUTURE_EPOCH then .pendingInitialized
    else .pendingQueued
  else if epoch < validator.exitEpoch then
    if validator.exitEpoch = FAR_FUTURE_EPOCH then .activeOngoing
    else if validator.slashed then .activeSlashed
    else .activeExiting
  else if epoch < validator.withdrawableEpoch then
    if validator.slashed then .exitedSlashed else .exitedUnslashed
  else if balance = 0 then .withdrawalDone
  else .withdrawalPossible

/-- The status of a builder. -/
inductive BuilderStatus where
  /-- Not exited, and not yet active. -/
  | pending
  /-- Active. -/
  | active
  /-- Exited: its withdrawable epoch is set. -/
  | exited
  deriving DecidableEq, Repr

namespace BuilderStatus

/-- The name of a builder status, as the API writes it. -/
def name : BuilderStatus → String
  | .pending => "pending"
  | .active => "active"
  | .exited => "exited"

/-- The condition of the source for a builder status, on a builder and the finalized epoch.

A builder is active when its deposit is before the finalized epoch and it has not started to exit.
-/
def Holds (status : BuilderStatus) (builder : Builder) (finalizedEpoch : Epoch) : Prop :=
  match status with
  | .pending =>
    builder.withdrawableEpoch = FAR_FUTURE_EPOCH ∧
      ¬(builder.depositEpoch < finalizedEpoch ∧ builder.withdrawableEpoch = FAR_FUTURE_EPOCH)
  | .active =>
    builder.depositEpoch < finalizedEpoch ∧ builder.withdrawableEpoch = FAR_FUTURE_EPOCH
  | .exited => builder.withdrawableEpoch ≠ FAR_FUTURE_EPOCH

end BuilderStatus

/-- From Gloas: the status of the builder at an index of a state, or an error for no builder. -/
def builderStatus (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (index : BuilderIndex) : Except AccessorError BuilderStatus := do
  let builder ← getBuilder state gloas index
  if builder.withdrawableEpoch ≠ FAR_FUTURE_EPOCH then return .exited
  if ← isActiveBuilder state gloas index then return .active
  return .pending

end EthLib.Consensus.BeaconApi
