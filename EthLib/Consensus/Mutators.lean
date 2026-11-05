module

public import EthLib.Consensus.Accessors

/-!
# `Consensus.Mutators`

Functions that change the balances and the validators of a beacon state.

A balance grows by a reward, and shrinks by a penalty down to zero at most.

A validator that exits joins the exit queue, which lets a limited number leave each epoch.

A slashed validator exits, loses part of its balance, and pays a reward to whoever reported it.

A read past the end of a list, or a 64-bit overflow, is an error.

Electra counts the exit queue in balance, and Gloas also cancels the builder payments of a slashed
proposer.

Those rules are not yet in EthLib, so these functions fail there instead of applying older rules.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-- The state with the balance at an index replaced. -/
def BeaconState.setBalance (state : BeaconState preset fork) (index : Nat) (balance : Gwei) :
    BeaconState preset fork :=
  { state with balances := ⟨state.balances.data.set! index balance, by
      simpa using state.balances.bound⟩ }

/-- The state with the validator at an index replaced. -/
def BeaconState.setValidator (state : BeaconState preset fork) (index : Nat)
    (validator : Validator) : BeaconState preset fork :=
  { state with validators := ⟨state.validators.data.set! index validator, by
      simpa using state.validators.bound⟩ }

/-- The balance of a validator. -/
def getBalance (state : BeaconState preset fork) (index : ValidatorIndex) :
    Except AccessorError Gwei :=
  match state.balances.data[index.toNat]? with
  | some balance => .ok balance
  | none => .error (.indexOutOfRange index)

/-- A validator of the registry. -/
def getValidator (state : BeaconState preset fork) (index : ValidatorIndex) :
    Except AccessorError Validator :=
  match state.validators.data[index.toNat]? with
  | some validator => .ok validator
  | none => .error (.indexOutOfRange index)

/-- The state with a balance raised by an amount. -/
def increaseBalance (state : BeaconState preset fork) (index : ValidatorIndex) (delta : Gwei) :
    Except AccessorError (BeaconState preset fork) := do
  let balance ← liftArith (addChecked (← getBalance state index) delta)
  return state.setBalance index.toNat balance

/-- The state with a balance lowered by an amount, or set to zero if the amount is larger. -/
def decreaseBalance (state : BeaconState preset fork) (index : ValidatorIndex) (delta : Gwei) :
    Except AccessorError (BeaconState preset fork) := do
  return state.setBalance index.toNat (saturatingSub (← getBalance state index) delta)

/-- The epoch at which a validator that starts to exit now leaves, before Electra.

It is the latest exit epoch of the registry, and at least the first epoch an exit may take.

If that epoch already holds as many exits as the churn limit, the validator leaves one epoch later.
-/
def exitQueueEpoch (config : Config) (state : BeaconState preset fork) :
    Except AccessorError Epoch := do
  let validators := state.validators.data.toList
  let earliest ← liftArith (computeActivationExitEpoch preset (getCurrentEpoch state))
  let latest := (validators.filter (·.exitEpoch != FAR_FUTURE_EPOCH)).foldl
    (fun latest validator => max latest validator.exitEpoch) earliest
  let churn := (validators.filter (·.exitEpoch == latest)).length
  if (getValidatorChurnLimit config state).toNat ≤ churn then liftArith (addChecked latest 1)
  else return latest

/-- The state in which a validator starts to exit, unless it has already started.

It leaves at the epoch of the exit queue, and may withdraw a fixed delay after that.

Electra counts the exit queue in balance, as [EIP-7251] specifies, which EthLib does not yet have.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#specification
-/
def initiateValidatorExit (config : Config) (state : BeaconState preset fork)
    (index : ValidatorIndex) : Except AccessorError (BeaconState preset fork) := do
  let validator ← getValidator state index
  if validator.exitEpoch != FAR_FUTURE_EPOCH then return state
  if .pectra ≤ fork then throw (.forkNotYetSpecified fork)
  let exitEpoch ← exitQueueEpoch config state
  let withdrawableEpoch ←
    liftArith (addChecked exitEpoch config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY)
  return state.setValidator index.toNat { validator with exitEpoch, withdrawableEpoch }

/-- The share of the whistleblower reward that goes to the proposer.

Before Altair it is the reward over a fixed quotient, and from Altair a fixed weight of it. -/
def proposerShare (preset : Preset) (fork : Base.Fork) (whistleblowerReward : Gwei) :
    Except AccessorError Gwei :=
  if .altair ≤ fork then
    return (← liftArith (mulChecked whistleblowerReward PROPOSER_WEIGHT)) / WEIGHT_DENOMINATOR
  else return whistleblowerReward / preset.PROPOSER_REWARD_QUOTIENT

/-- The state after a validator is slashed.

The validator exits, cannot withdraw before a fixed number of epochs, and pays a first penalty.

Its effective balance joins the slashed balance of the epoch, which sets a later penalty.

The proposer and the whistleblower share a reward, and the proposer is the whistleblower by default.

From Electra, the slashing of a validator that has not started to exit fails through its exit.

Gloas also cancels the builder payments of the validator, which EthLib does not yet have. -/
def slashValidator (config : Config) (state : BeaconState preset fork)
    (slashedIndex : ValidatorIndex) (whistleblowerIndex : Option ValidatorIndex := none) :
    Except AccessorError (BeaconState preset fork) := do
  if .glamsterdam ≤ fork then throw (.forkNotYetSpecified fork)
  let epoch := getCurrentEpoch state
  let state ← initiateValidatorExit config state slashedIndex
  let validator ← getValidator state slashedIndex
  let withdrawableEpoch := max validator.withdrawableEpoch
    (← liftArith (addChecked epoch preset.EPOCHS_PER_SLASHINGS_VECTOR))
  let state := state.setValidator slashedIndex.toNat
    { validator with slashed := true, withdrawableEpoch }
  let slashed ← readCircular state.slashings epoch
  let slashed ← liftArith (addChecked slashed validator.effectiveBalance)
  let state := { state with
    slashings := state.slashings.set! (epoch % preset.EPOCHS_PER_SLASHINGS_VECTOR).toNat slashed }
  let parameters := parameters preset fork
  let state ← decreaseBalance state slashedIndex
    (validator.effectiveBalance / parameters.MIN_SLASHING_PENALTY_QUOTIENT)
  let proposerIndex ← getBeaconProposerIndex state
  let whistleblowerIndex := whistleblowerIndex.getD proposerIndex
  let whistleblowerReward := validator.effectiveBalance / parameters.WHISTLEBLOWER_REWARD_QUOTIENT
  let proposerReward ← proposerShare preset fork whistleblowerReward
  let state ← increaseBalance state proposerIndex proposerReward
  increaseBalance state whistleblowerIndex (whistleblowerReward - proposerReward)

end EthLib.Consensus
