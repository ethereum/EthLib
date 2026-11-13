module

public import EthLib.Consensus.BeaconApi.Config
public import EthLib.Consensus.Exports.Genesis
public import EthLib.Consensus.Exports.Ssz

/-!
# `Exports.BeaconApiConfig`

C-ABI exports of the answers of the Beacon API that describe the chain.

They give the spec map, the fork schedule, the deposit contract and the genesis.

Each answer is the data of the response, as JSON that the API writes, in Python values.

A `str` names the preset and the configuration, which share that name.

A `dict` may replace values of the configuration, under the names of the configuration file.

An unknown name, or an input that does not decode, has code 0.
-/

@[expose] public section

namespace EthLib.Consensus.Exports

open Lean Base Serialization.Ssz
open EthLib.Exports (Result PyValue pyExport)
open Serialization.Ssz.Exports (runSsz)

/-- The spec map of a preset and a configuration, as a `dict`. -/
def apiSpecOf (args : String × Option PyValue) : Result PyValue := do
  let (name, replacements) := args
  let preset ← presetOf name
  let config ← configWithValue name replacements
  return PyValue.ofJson (Json.mkObj (BeaconApi.specMap config preset))

/-- The spec map of a preset and a configuration, as a `dict`.

The arguments are the name and a `dict` of replacements, or None.

A number is a `str` of decimal digits, and bytes are a `str` of `0x` and lowercase hex. -/
@[export eth_consensus_api_spec]
def apiSpecExport (args : PyValue) : Result PyValue := pyExport apiSpecOf args

/-- The fork schedule of a configuration, as a `list` of `dict`. -/
def apiForkScheduleOf (args : String × Option PyValue) : Result PyValue := do
  let (name, replacements) := args
  let config ← configWithValue name replacements
  let entries ← (BeaconApi.forkSchedule config).mapM fun entry =>
    runSsz "value rejected" (BeaconApi.toApiJson entry)
  return PyValue.ofJson (Json.arr entries.toArray)

/-- The fork schedule of a configuration, as a `list` of `dict`.

The arguments are the name and a `dict` of replacements, or None. -/
@[export eth_consensus_api_fork_schedule]
def apiForkScheduleExport (args : PyValue) : Result PyValue := pyExport apiForkScheduleOf args

/-- The deposit contract of a configuration, as a `dict`. -/
def apiDepositContractOf (args : String × Option PyValue) : Result PyValue := do
  let (name, replacements) := args
  let config ← configWithValue name replacements
  let document ← runSsz "value rejected" (BeaconApi.toApiJson (BeaconApi.depositContract config))
  return PyValue.ofJson document

/-- The deposit contract of a configuration, as a `dict`.

The arguments are the name and a `dict` of replacements, or None. -/
@[export eth_consensus_api_deposit_contract]
def apiDepositContractExport (args : PyValue) : Result PyValue :=
  pyExport apiDepositContractOf args

/-- The genesis that a genesis state and a configuration give, as a `dict`. -/
def apiGenesisOf (args : String × String × ByteArray × Option PyValue) : Result PyValue := do
  let (name, fork, state, replacements) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let state ← decodeInput (BeaconState preset fork) state
  let document ← runSsz "value rejected"
    (BeaconApi.toApiJson (BeaconApi.genesisInfo config state))
  return PyValue.ofJson document

/-- The genesis that a genesis state gives, as a `dict`.

The arguments are the name, the fork, the SSZ bytes of the state, and replacements or None.

The genesis version is the one of the configuration. -/
@[export eth_consensus_api_genesis]
def apiGenesisExport (args : PyValue) : Result PyValue := pyExport apiGenesisOf args

end EthLib.Consensus.Exports
