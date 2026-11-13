module

public import EthLib.Consensus.BeaconApi.Blocks
public import EthLib.Consensus.Exports.BeaconApiStateQueries
public import EthLib.Consensus.Exports.Column

/-!
# `Exports.BeaconApiBlocks`

C-ABI exports of the answers of the Beacon API that read one signed block.

A query is named after its endpoint, such as `attestations` or `blinded_block`.

The JSON answer is the response without the two flags that come from the store.

An error response of the API has its own code: 400 or 500.

An unknown name, query or fork, or an input that does not decode, has code 0.
-/

@[expose] public section

namespace EthLib.Consensus.Exports

open Lean Base Serialization.Ssz Cryptography.Kzg
open EthLib.Exports (Result PyValue pyExport)

/-- The response to a query on a signed block. -/
def blockQuery {preset : Preset} {fork : Fork} (block : SignedBeaconBlock preset fork)
    (query : String) : Result BeaconApi.ApiEnvelope :=
  match query with
  | "block" => apiError (BeaconApi.blockResponse block)
  | "root" => apiError (BeaconApi.blockRootResponse block)
  | "attestations" => apiError (BeaconApi.blockAttestationsResponse block)
  | "blinded_block" => apiError (BeaconApi.blindedBlockResponse block)
  | _ => throw (0, s!"no block query is named {query}")

/-- The JSON response to a query on a signed block. -/
def apiBlockQueryOf (args : String × String × ByteArray × String) : Result PyValue := do
  let (name, fork, block, query) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let block ← decodeInput (SignedBeaconBlock preset fork) block
  let envelope ← blockQuery block query
  return PyValue.ofJson envelope.toJson

/-- The JSON response to a query on a signed block, as a `dict`.

The arguments are the name, the fork, the SSZ bytes of the signed block and the query.

The queries are the block, its root, its attestations and its blinded form. -/
@[export eth_consensus_api_block_query]
def apiBlockQueryExport (args : PyValue) : Result PyValue := pyExport apiBlockQueryOf args

/-- The JSON response of the blobs endpoint. -/
def apiBlobsOf
    (args : String × String × ByteArray × List Blob × Option (List VersionedHash)) :
    Result PyValue := do
  let (name, fork, block, blobs, hashes) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let block ← decodeInput (SignedBeaconBlock preset fork) block
  let envelope ← apiError (BeaconApi.blobsResponse block blobs hashes)
  return PyValue.ofJson envelope.toJson

/-- The JSON response of the blobs endpoint, as a `dict`.

The arguments are the name, the fork, the SSZ bytes of the signed block and its blobs.

The last argument is the requested versioned hashes, or None for every blob. -/
@[export eth_consensus_api_blobs]
def apiBlobsExport (args : PyValue) : Result PyValue := pyExport apiBlobsOf args

/-- The SSZ body of the blobs answer. -/
def apiBlobsSszOf
    (args : String × String × ByteArray × List Blob × Option (List VersionedHash)) :
    Result ByteArray := do
  let (name, fork, block, blobs, hashes) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let block ← decodeInput (SignedBeaconBlock preset fork) block
  apiError (BeaconApi.blobsSsz block blobs hashes)

/-- The SSZ body of the blobs answer, as `bytes`.

The arguments are those of the JSON answer. -/
@[export eth_consensus_api_blobs_ssz]
def apiBlobsSszExport (args : PyValue) : Result PyValue := pyExport apiBlobsSszOf args

end EthLib.Consensus.Exports
