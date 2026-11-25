module

public import EthLib.Consensus.Proofs.BeaconApi.Registries
public import EthLib.Consensus.Proofs.BeaconApi.Validators
public import EthLib.Consensus.Proofs.Transition.ActivationExitOrder

/-!
# Proofs: one status per validator of a state that a run from genesis reaches

On such a state every validator activates no later than it exits.

It also exits no later than it can withdraw.

So the status of each validator is the only one whose condition holds.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- On a state of a run from a genesis, each validator of the state has exactly one status.

It holds at every epoch and for every balance.

The genesis is built from deposits. -/
theorem validatorStatus_unique_of_run {g x : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (run : Run config checks g x) {validator : Validator}
    (member : validator ∈ x.state.validators.data) (balance : Gwei) (epoch : Epoch)
    (status : ValidatorStatus) :
    status.Holds validator balance epoch ↔ validatorStatus validator balance epoch = status :=
  validatorStatus_unique (run.activationExitOrder genesis validator member)
    (run.exitWithdrawableOrder genesis validator member) status

/-- On a state of a run from a genesis, an entry of the validators answer has one status.

It is the only status whose condition holds at the current epoch.

The genesis is built from deposits. -/
theorem stateValidators_status_unique_of_run {g x : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (run : Run config checks g x) {ids : List ValidatorId}
    {filter : StatusFilter} {entry : ValidatorResponse}
    (answered : entry ∈ stateValidators x.state ids filter) (status : ValidatorStatus) :
    status.Holds entry.validator entry.balance (getCurrentEpoch x.state) ↔
      entry.status = status := by
  obtain ⟨-, found, -, current, -⟩ := stateValidators_mem.mp answered
  rw [current]
  exact validatorStatus_unique_of_run genesis run (Array.mem_of_getElem? found) _ _ status

end EthLib.Consensus.BeaconApi
