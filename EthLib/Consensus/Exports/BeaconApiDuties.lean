module

public import EthLib.Consensus.BeaconApi.Duties
public import EthLib.Consensus.Exports.BeaconApiStateQueries

/-!
# `Exports.BeaconApiDuties`

A C-ABI export of the duty answers of the Beacon API, computed from a state.

A request is named after its endpoint: `attester`, `proposer`, `proposer_v2`, `sync` or `ptc`.

The JSON answer is the response without the flag that comes from the store.

An error response of the API has its own code: 400 or 500.

An unknown name, kind or fork, or an input that does not decode, has code 0.
-/

@[expose] public section

namespace EthLib.Consensus.Exports

open Lean Base Serialization.Ssz
open EthLib.Exports (Result PyValue pyExport)

/-- The kind of duties that the name of an endpoint asks for. -/
def dutyKindOf (kind : String) : Result BeaconApi.DutyKind :=
  match kind with
  | "attester" => return .attester
  | "proposer" => return .proposerV1
  | "proposer_v2" => return .proposerV2
  | "sync" => return .sync
  | "ptc" => return .ptc
  | _ => throw (0, s!"no duties are named {kind}")

/-- The JSON response of a duties endpoint. -/
def apiDutiesOf (args : String × String × ByteArray × Option PyValue × String × UInt64 ×
    List UInt64 × Root) : Result PyValue := do
  let (name, fork, state, replacements, kind, epoch, indices, genesisRoot) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let state ← decodeInput (BeaconState preset fork) state
  let kind ← dutyKindOf kind
  let envelope ← apiError (BeaconApi.dutiesResponse config state kind epoch indices genesisRoot)
  return PyValue.ofJson envelope.toJson

/-- The JSON response of a duties endpoint, as a `dict`.

The arguments are the name, the fork, the SSZ bytes of the state and replacements or None.

Then come the kind of duties, the epoch, the validator indices and the genesis block root.

The proposer duties read no indices. -/
@[export eth_consensus_api_duties]
def apiDutiesExport (args : PyValue) : Result PyValue := pyExport apiDutiesOf args

end EthLib.Consensus.Exports
