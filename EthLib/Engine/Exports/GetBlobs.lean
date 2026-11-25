module

public import EthLib.Base.Exports.PyValue
public import EthLib.Base.List
public import EthLib.Cryptography.Exports.Kzg
public import EthLib.Engine.Capabilities
public import EthLib.Engine.Exports.Errors
public import EthLib.Engine.GetBlobs

/-!
# `Exports.GetBlobs`

The C export of `engine_getBlobs`, versions 1 to 4.

The blob pool crosses as a list of entries, one per versioned hash.

Whether the pool serves, its request limit and the active fork of the node cross beside it.

An argument that Lean cannot read has code 0.

A second export reads the JSON result of any version, and writes it back.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result PyValue UnreadArgument pyExport rejectArgument toResult)
open EthLib.Base
open EthLib.Cryptography.Kzg
open EthLib.Cryptography.Kzg.Constants

/-- One entry of the pool: the hash, the blob, the blob proof and the cells with their proofs. -/
abbrev PoolEntry :=
  Bytes32 × Option Blob × Option KZGProof × Option (List (Option (Cell × KZGProof)))

/-- The hash and the pooled blob of an entry, whose list of cells must have one item per cell. -/
def pooledOf (entry : PoolEntry) : Result (VersionedHash × PooledBlob) := do
  -- An entry holds the hash, the blob or `None`, the blob proof or `None`, and the cells or `None`.
  let (hash, blob, proof, cells) := entry
  let cells ← match cells with
    -- `None` in place of the list means that the pool holds no cell.
    | none => pure (Vector.replicate CELLS_PER_EXT_BLOB none)
    -- The cells are a list of 128 items, each a cell and its proof, or `None`.
    | some cells => toResult none (exactArray CELLS_PER_EXT_BLOB cells.toArray fun count =>
      UnreadArgument.mk s!"pool: {count} cells, not {CELLS_PER_EXT_BLOB}")
  -- The 32 bytes of the hash are the versioned hash under which the pool holds the blob.
  return (⟨hash⟩, ⟨blob, proof, cells⟩)

/-- The version of a method name `engine_getBlobsV1` to `engine_getBlobsV4`. -/
def getBlobsVersion (method : String) : Option Nat := methodVersion "getBlobs" method

/-- The answer to an `engine_getBlobs` request, from a blob pool.

The arguments are the pool's entries, whether it serves, its limit, the fork and the request. -/
def getBlobsOf (args : List PoolEntry × Bool × Nat × String × PyValue) : Result PyValue := do
  let (entries, serving, maxRequest, forkName, request) := args
  -- A malformed pool has code 0.
  let entries ← entries.mapM pooledOf
  -- A pool holds each blob once, so two entries with one hash are malformed input.
  unless (Base.firstRepeated (entries.map (·.1.bytes))).isNone do
    rejectArgument none "pool: two entries with one versioned hash"
  -- The method is specified up to Glamsterdam, the fork of its version 4.
  --
  -- Another fork has code 0.
  let fork ← EthLib.Exports.forkUpTo .glamsterdam forkName.toUTF8
  -- The limit must be at least 128, or the export raises with code 0.
  if below : maxRequest < MIN_BLOBS_REQUEST_LIMIT then
    rejectArgument none s!"pool: a limit of {maxRequest}, below {MIN_BLOBS_REQUEST_LIMIT}"
  else
  let pool : BlobPool := {
    lookup := fun hash => (entries.find? (·.1 == hash)).map (·.2)
    serving, maxRequest, le_maxRequest := Nat.not_lt.1 below }
  -- The request is a JSON-RPC request object, with its method and its parameters.
  let request := request.toJson
  -- An unknown method has code 0.
  let some method := (request.getObjValAs? String "method").toOption
    | rejectArgument none "request: no method"
  let some version := getBlobsVersion method | rejectArgument none s!"no method {method}"
  -- A parameter error has the code of its Engine API error, without the sign: 32602.
  --
  -- The parameters are decoded first, before any check of the fork or of the request size.
  let (hashes, bits) ← toResult "engine error"
    (getBlobsParams version (request.getObjValD "params"))
  -- A request error has code 38004 or 38005.
  let answer : Json ← match version, bits with
    | 1, _ =>
      let blobs ← toResult "engine error" (getBlobsV1 pool fork hashes)
      pure (getBlobsV1Json blobs)
    | 2, _ =>
      let blobs ← toResult "engine error" (getBlobsV2 pool hashes)
      pure (getBlobsV2Json blobs)
    | 3, _ =>
      let blobs ← toResult "engine error" (getBlobsV3 pool hashes)
      pure (getBlobsV3Json blobs)
    | _, some bits =>
      let cells ← toResult "engine error" (getBlobsV4 pool hashes bits)
      pure (getBlobsV4Json cells)
    -- The parameters of version 4 always hold a bitarray, so this case never happens.
    | _, none => rejectArgument none "params: no bitarray"
  -- The result is the JSON answer, as a Python value.
  return .ofJson answer

/-- The answer to an `engine_getBlobs` request, from a blob pool.

The arguments are the pool's entries, whether it serves, its limit, the fork and the request.

Each entry is the versioned hash, the blob, the blob proof and the 128 cells with their proofs.

Any of the last three may be `None`, and so may each cell. -/
@[export eth_engine_get_blobs]
def getBlobsExport (args : PyValue) : Result PyValue :=
  pyExport getBlobsOf args

/-- A result of `engine_getBlobs`, read at the version of the method name and written back. -/
def readGetBlobsResultOf (args : String × PyValue) : Result PyValue := do
  let (method, result) := args
  let some version := getBlobsVersion method | rejectArgument none s!"no method {method}"
  let result := result.toJson
  let answer : Json ← match version with
    | 1 => getBlobsV1Json <$> toResult "engine error" (getBlobsV1OfJson result)
    | 2 => getBlobsV2Json <$> toResult "engine error" (getBlobsV2OfJson result)
    | 3 => getBlobsV3Json <$> toResult "engine error" (getBlobsV3OfJson result)
    | _ => getBlobsV4Json <$> toResult "engine error" (getBlobsV4OfJson result)
  return .ofJson answer

/-- The result of an `engine_getBlobs` method, read from its JSON and written back.

The arguments are the method name and the result, as `json.loads` gives it.

A result that does not decode is reported as invalid parameters, with code 32602.

An unknown method name has code 0. -/
@[export eth_engine_read_get_blobs_result]
def readGetBlobsResultExport (args : PyValue) : Result PyValue :=
  pyExport readGetBlobsResultOf args

end EthLib.Engine.Exports
