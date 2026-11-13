module

public import EthLib.Consensus.BeaconApi.Committees
public import EthLib.Consensus.Exports.BeaconApiStateQueries

/-!
# `Exports.BeaconApiCommittees`

C-ABI exports of the answers of the Beacon API that list the committees of a state.

The JSON answer is the response without the two flags that come from the store.

An error response of the API has its own code: 400 or 500.

An unknown name or fork, or an input that does not decode, has code 0.
-/

@[expose] public section

namespace EthLib.Consensus.Exports

open Lean Base Serialization.Ssz
open EthLib.Exports (Result PyValue pyExport)

/-- The JSON response of the committees endpoint. -/
def apiCommitteesOf
    (args : String × String × ByteArray × Option UInt64 × Option UInt64 × Option UInt64) :
    Result PyValue := do
  let (name, fork, state, epoch, index, slot) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let state ← decodeInput (BeaconState preset fork) state
  let envelope ← apiError (BeaconApi.committeesResponse state epoch index slot)
  return PyValue.ofJson envelope.toJson

/-- The JSON response of the committees endpoint, as a `dict`.

The arguments are the name, the fork, the SSZ bytes of the state, then the epoch, index and slot.

Each of the last three is an `int` or None. -/
@[export eth_consensus_api_committees]
def apiCommitteesExport (args : PyValue) : Result PyValue := pyExport apiCommitteesOf args

/-- The JSON response of the sync committees endpoint. -/
def apiSyncCommitteesOf (args : String × String × ByteArray × Option UInt64) :
    Result PyValue := do
  let (name, fork, state, epoch) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let state ← decodeInput (BeaconState preset fork) state
  let envelope ← apiError (BeaconApi.syncCommitteesResponse state epoch)
  return PyValue.ofJson envelope.toJson

/-- The JSON response of the sync committees endpoint, as a `dict`.

The arguments are the name, the fork, the SSZ bytes of the state, and an epoch or None. -/
@[export eth_consensus_api_sync_committees]
def apiSyncCommitteesExport (args : PyValue) : Result PyValue := pyExport apiSyncCommitteesOf args

/-- The JSON response of the PTC endpoint. -/
def apiPtcOf (args : String × String × ByteArray × Option PyValue × Option UInt64) :
    Result PyValue := do
  let (name, fork, state, replacements, slot) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let state ← decodeInput (BeaconState preset fork) state
  let envelope ← apiError (BeaconApi.ptcResponse config state slot)
  return PyValue.ofJson envelope.toJson

/-- The JSON response of the PTC endpoint, as a `dict`.

The arguments are the name, the fork, the SSZ bytes of the state and replacements or None.

The last argument is a slot or None. -/
@[export eth_consensus_api_ptc]
def apiPtcExport (args : PyValue) : Result PyValue := pyExport apiPtcOf args

/-- The SSZ body of the PTC answer. -/
def apiPtcSszOf (args : String × String × ByteArray × Option PyValue × Option UInt64) :
    Result ByteArray := do
  let (name, fork, state, replacements, slot) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let state ← decodeInput (BeaconState preset fork) state
  apiError (BeaconApi.ptcSsz config state slot)

/-- The SSZ body of the PTC answer, as `bytes`.

The arguments are those of the JSON answer. -/
@[export eth_consensus_api_ptc_ssz]
def apiPtcSszExport (args : PyValue) : Result PyValue := pyExport apiPtcSszOf args

end EthLib.Consensus.Exports
