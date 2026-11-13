module

public import EthLib.Consensus.BeaconApi.Encoding
public import EthLib.Consensus.Exports.Ssz

/-!
# `Exports.BeaconApi`

C-ABI exports for the JSON of a container in the Beacon API.

The container is named as the consensus specifications name it, at a preset and a fork.

One export writes the JSON of the value that SSZ bytes encode, and the other reads it back.

The document travels as a Python value: objects, arrays, strings and booleans.

Bytes also read as hex, and an int as a bare number, which the reader accepts too.

A name with no container at the fork, or none specified there yet, has code 0.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz
open EthLib.Exports (Result PyValue pyExport)
open Serialization.Ssz.Exports (runSsz)

/-- The JSON of the API for the value that the bytes encode. -/
def apiJsonOf (args : String × String × String × ByteArray) : Result PyValue := do
  let (name, fork, type, data) := args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  let some container := containerOf preset fork type
    | throw (0, s!"no container {type} at {fork.name}")
  if !specifiedAt fork type then
    throw (0, s!"{type} not yet specified at {fork.name}")
  let value ← runSsz "input rejected" (SszType.deserialize container.type data)
  return PyValue.ofJson (← runSsz "value rejected" (BeaconApi.toApiJson value))

/-- The JSON of the API for the value that SSZ bytes encode.

The arguments are the name of the preset, the fork, the container and the bytes. -/
@[export eth_consensus_api_json]
def apiJsonExport (args : PyValue) : Result PyValue := pyExport apiJsonOf args

/-- The SSZ bytes of the value that a JSON document of the API holds. -/
def apiSszOf (args : String × String × String × PyValue) : Result ByteArray := do
  let (name, fork, type, document) := args
  let preset ← presetOf name
  let fork ← forkOf fork.toUTF8
  let some container := containerOf preset fork type
    | throw (0, s!"no container {type} at {fork.name}")
  if !specifiedAt fork type then
    throw (0, s!"{type} not yet specified at {fork.name}")
  let value ← runSsz "document rejected" (BeaconApi.ofApiJson container.type document.toJson)
  runSsz "value rejected" (SszType.serialize value)

/-- The SSZ bytes of the value that a JSON document of the API holds.

The arguments are the name of the preset, the fork, the container and the document.

Hex reads in either letter case, and a key that the container does not declare is refused. -/
@[export eth_consensus_api_ssz]
def apiSszExport (args : PyValue) : Result PyValue := pyExport apiSszOf args

end EthLib.Consensus.Exports
