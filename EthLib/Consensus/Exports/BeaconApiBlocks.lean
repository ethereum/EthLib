module

public import EthLib.Consensus.BeaconApi.Blocks
public import EthLib.Consensus.Exports.BeaconApiIdentifiers
public import EthLib.Consensus.Exports.BeaconApiStateQueries
public import EthLib.Consensus.Exports.Column

/-!
# `Exports.BeaconApiBlocks`

C-ABI exports of the answers of the Beacon API that read signed blocks and their data.

The answers that read the fork choice take the store after the steps of a fork choice case.

A query is named after its endpoint, such as `attestations` or `blinded_block`.

The JSON answer is the response without the two flags that come from the store.

An error response of the API has its own code: 400, 404 or 500.

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

/-- The SSZ body of the answer to a query on a signed block. -/
def blockQuerySsz {preset : Preset} {fork : Fork} (block : SignedBeaconBlock preset fork)
    (query : String) : Result ByteArray :=
  match query with
  | "block" => apiError (BeaconApi.blockSsz block)
  | "blinded_block" => apiError (BeaconApi.blindedBlockSsz block)
  | _ => throw (0, s!"no block query with an SSZ body is named {query}")

/-- The SSZ body of the answer to a query, from the preset, the fork and the SSZ of the block. -/
def apiBlockQuerySszOf (args : String × String × ByteArray × String) : Result ByteArray := do
  let (name, fork, block, query) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let block ← decodeInput (SignedBeaconBlock preset fork) block
  blockQuerySsz block query

/-- The SSZ body of the answer to a query on a signed block, as `bytes`.

The arguments are those of the JSON answer.

The queries with an SSZ body are the block and its blinded form. -/
@[export eth_consensus_api_block_query_ssz]
def apiBlockQuerySszExport (args : PyValue) : Result PyValue := pyExport apiBlockQuerySszOf args

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

/-- The JSON response of the header endpoint for a signed block. -/
def apiHeaderOf (args : StoreCaseArgs ByteArray) : Result PyValue := do
  let (name, fork, anchorState, anchorBlock, steps, verify, block) := args
  let ⟨preset, fork, config, store⟩ ←
    storeOfCase (name, fork, anchorState, anchorBlock, steps, verify)
  let block ← decodeInput (SignedBeaconBlock preset fork) block
  let envelope ← apiError (BeaconApi.headerResponse config store block)
  return PyValue.ofJson envelope.toJson

/-- The JSON response of the header endpoint for a signed block, as a `dict`.

The first arguments build the store as a fork choice case does.

The last argument is the SSZ bytes of the signed block. -/
@[export eth_consensus_api_header]
def apiHeaderExport (args : PyValue) : Result PyValue := pyExport apiHeaderOf args

/-- The JSON response of the headers endpoint. -/
def apiHeadersOf (args : StoreCaseArgs (List ByteArray × Option UInt64 × Option Root)) :
    Result PyValue := do
  let (name, fork, anchorState, anchorBlock, steps, verify, headers, slot, parentRoot) := args
  let ⟨_, _, config, store⟩ ← storeOfCase (name, fork, anchorState, anchorBlock, steps, verify)
  let headers ← headers.mapM (decodeInput SignedBeaconBlockHeader)
  let envelope ← apiError (BeaconApi.headersResponse config store headers slot parentRoot)
  return PyValue.ofJson envelope.toJson

/-- The JSON response of the headers endpoint, as a `dict`.

The first arguments build the store as a fork choice case does.

Then come the SSZ bytes of the signed headers that the node holds, the slot and the parent root. -/
@[export eth_consensus_api_headers]
def apiHeadersExport (args : PyValue) : Result PyValue := pyExport apiHeadersOf args

/-- The JSON response of the columns endpoint. -/
def apiColumnsOf (args : String × String × List ByteArray × Option (List UInt64)) :
    Result PyValue := do
  let (name, fork, sidecars, indices) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let sidecars ← sidecars.mapM (decodeInput (DataColumnSidecar preset fork))
  let envelope ← apiError (BeaconApi.columnsResponse sidecars indices)
  return PyValue.ofJson envelope.toJson

/-- The JSON response of the columns endpoint, as a `dict`.

The first arguments are the preset, the fork and the SSZ bytes of each sidecar that the node holds.

The last argument is the requested indices, or None for every sidecar. -/
@[export eth_consensus_api_columns]
def apiColumnsExport (args : PyValue) : Result PyValue := pyExport apiColumnsOf args

/-- The SSZ body of the columns answer. -/
def apiColumnsSszOf (args : String × String × List ByteArray × Option (List UInt64)) :
    Result ByteArray := do
  let (name, fork, sidecars, indices) := args
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let sidecars ← sidecars.mapM (decodeInput (DataColumnSidecar preset fork))
  apiError (BeaconApi.columnsSsz sidecars indices)

/-- The SSZ body of the columns answer, as `bytes`.

The arguments are those of the JSON answer. -/
@[export eth_consensus_api_columns_ssz]
def apiColumnsSszExport (args : PyValue) : Result PyValue := pyExport apiColumnsSszOf args

/-- The JSON response of the envelope endpoint. -/
def apiPayloadEnvelopeOf (args : StoreCaseArgs (Root × ByteArray)) : Result PyValue := do
  let (name, fork, anchorState, anchorBlock, steps, verify, root, signed) := args
  let ⟨preset, fork, _, store⟩ ←
    storeOfCase (name, fork, anchorState, anchorBlock, steps, verify)
  let signed ← decodeInput (SignedExecutionPayloadEnvelope preset fork) signed
  let envelope ← apiError (BeaconApi.payloadEnvelopeResponse store root signed)
  return PyValue.ofJson envelope.toJson

/-- The JSON response of the envelope endpoint, as a `dict`.

The first arguments build the store as a fork choice case does.

Then come the root of the block and the SSZ bytes of the signed envelope. -/
@[export eth_consensus_api_payload_envelope]
def apiPayloadEnvelopeExport (args : PyValue) : Result PyValue := pyExport apiPayloadEnvelopeOf args

/-- The SSZ body of the envelope answer. -/
def apiPayloadEnvelopeSszOf (args : StoreCaseArgs (Root × ByteArray)) : Result ByteArray := do
  let (name, fork, anchorState, anchorBlock, steps, verify, root, signed) := args
  let ⟨preset, fork, _, store⟩ ←
    storeOfCase (name, fork, anchorState, anchorBlock, steps, verify)
  let signed ← decodeInput (SignedExecutionPayloadEnvelope preset fork) signed
  apiError (BeaconApi.payloadEnvelopeSsz store root signed)

/-- The SSZ body of the envelope answer, as `bytes`.

The arguments are those of the JSON answer. -/
@[export eth_consensus_api_payload_envelope_ssz]
def apiPayloadEnvelopeSszExport (args : PyValue) : Result PyValue :=
  pyExport apiPayloadEnvelopeSszOf args

end EthLib.Consensus.Exports
