module

public import EthLib.Consensus.BeaconApi.Validators
public import EthLib.Consensus.BeaconApi.Spelling
public import EthLib.Consensus.Exports.Transition

/-!
# `Exports.BeaconApiValidators`

C-ABI exports of the statuses that the Beacon API gives to a validator and to a builder.

Each status is its name in the API, with the name of its group for a validator.

A validator whose JSON does not decode has the code of its decoding error.

An unknown name or fork, or a state that does not decode, has code 0.

A fork before Gloas, or an index with no builder, has code 0.
-/

@[expose] public section

namespace EthLib.Consensus.Exports

open Lean Base Serialization.Ssz
open EthLib.Exports (Result PyValue pyExport)
open Serialization.Ssz.Exports (runSsz)

/-- The status of a validator with a balance at an epoch, with the name of its group. -/
def apiValidatorStatusOf (args : PyValue × UInt64 × UInt64) : Result (String × String) := do
  let (validator, balance, epoch) := args
  let validator ← runSsz "document rejected" (BeaconApi.ofApiJson Validator validator.toJson)
  let status := BeaconApi.validatorStatus validator balance epoch
  return (status.name, status.coarse.name)

/-- The status of a validator with a balance at an epoch, and the name of its group.

The arguments are the validator as the JSON of the API, its balance and the epoch. -/
@[export eth_consensus_api_validator_status]
def apiValidatorStatusExport (args : PyValue) : Result PyValue :=
  pyExport apiValidatorStatusOf args

/-- The status of the builder at an index of a state. -/
def apiBuilderStatusOf (args : String × String × ByteArray × UInt64) : Result String := do
  let (name, fork, state, index) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let state ← decodeInput (BeaconState preset fork) state
  if gloas : .glamsterdam ≤ fork then
    match BeaconApi.builderStatus state gloas index with
    | .ok status => return status.name
    | .error fault => throw (0, s!"no builder status: {reprStr fault}")
  else throw (0, s!"no builder before gloas, at {fork.name}")

/-- The status of the builder at an index of a state, as its name.

The arguments are the name, the fork, the SSZ bytes of the state and the index. -/
@[export eth_consensus_api_builder_status]
def apiBuilderStatusExport (args : PyValue) : Result PyValue := pyExport apiBuilderStatusOf args

end EthLib.Consensus.Exports
