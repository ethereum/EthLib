module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Engine.Capabilities
public import EthLib.Engine.GetBlobs

/-!
# `Exports.GetBlobs`

The C export of `engine_getBlobs`, versions 1 to 4.

The blob pool crosses as a list of entries, one per versioned hash, with no hash twice.

An entry holds the hash, the blob or `None`, the blob proof or `None`, and the cells or `None`.

The cells are a list of 128 items, each a cell and its proof, or `None`.

`None` in place of the list means that the pool holds no cell.

Whether the pool serves, its request limit and the active fork of the node cross beside it.

The limit must be at least 128, and the fork at most Glamsterdam.

The request is a JSON-RPC request object, with its method and its parameters.

The result is the JSON answer, as a Python value.

A JSON-RPC error has the code of its Engine API error, without the sign: 32602, 38004 or 38005.

A malformed pool, limit or fork has code 0.

So do an unknown method and an argument that Lean cannot read.

A second export reads the JSON result of any version, and writes it back.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result PyValue pyExport)
open EthLib.Base
open EthLib.Cryptography.Kzg
open EthLib.Cryptography.Kzg.Constants

/-- One entry of the pool: the hash, the blob, the blob proof and the cells with their proofs. -/
abbrev PoolEntry :=
  Bytes32 × Option Blob × Option KZGProof × Option (List (Option (Cell × KZGProof)))

/-- The pooled blob of an entry, whose list of cells must have one item per cell. -/
def pooledOf (entry : PoolEntry) : Result (Bytes32 × PooledBlob) := do
  let (hash, blob, proof, cells) := entry
  let cells ← match cells with
    | none => pure (Vector.replicate CELLS_PER_EXT_BLOB none)
    | some cells =>
      if h : cells.length = CELLS_PER_EXT_BLOB then pure ⟨cells.toArray, by simpa using h⟩
      else throw (0, s!"pool: {cells.length} cells, not {CELLS_PER_EXT_BLOB}")
  return (hash, ⟨blob, proof, cells⟩)

/-- The version of a method name `engine_getBlobsV1` to `engine_getBlobsV4`. -/
def getBlobsVersion (method : String) : Option Nat := methodVersion "getBlobs" method

/-- The answer to an `engine_getBlobs` request, from a blob pool.

The arguments are the pool's entries, whether it serves, its limit, the fork and the request. -/
def getBlobsOf (args : List PoolEntry × Bool × Nat × String × PyValue) : Result PyValue := do
  let (entries, serving, maxRequest, forkName, request) := args
  let entries ← entries.mapM pooledOf
  -- A pool holds each blob once, so two entries with one hash are malformed input.
  unless (entries.map (·.1)).Nodup do throw (0, "pool: two entries with one versioned hash")
  -- The method is specified up to Glamsterdam, the fork of its version 4.
  let fork ← EthLib.Exports.forkUpTo .glamsterdam forkName.toUTF8
  if below : maxRequest < MIN_BLOBS_REQUEST_LIMIT then
    throw (0, s!"pool: a limit of {maxRequest}, below {MIN_BLOBS_REQUEST_LIMIT}")
  else
  let pool : BlobPool := {
    lookup := fun hash => (entries.find? (·.1 == hash)).map (·.2)
    serving, maxRequest, le_maxRequest := Nat.not_lt.1 below }
  let request := request.toJson
  let some method := (request.getObjValAs? String "method").toOption
    | throw (0, "request: no method")
  let some version := getBlobsVersion method | throw (0, s!"no method {method}")
  let engine {α : Type} (act : Except EngineError α) : Result α :=
    act.mapError fun e => (e.code, s!"engine error: {reprStr e}")
  let (hashes, bits) ← engine (getBlobsParams version (request.getObjValD "params"))
  let answer : Json ← match version, bits with
    | 1, _ =>
      let blobs ← engine (getBlobsV1 pool fork hashes)
      pure (getBlobsV1Json blobs)
    | 2, _ =>
      let blobs ← engine (getBlobsV2 pool hashes)
      pure (getBlobsV2Json blobs)
    | 3, _ =>
      let blobs ← engine (getBlobsV3 pool hashes)
      pure (getBlobsV3Json blobs)
    | _, some bits =>
      let cells ← engine (getBlobsV4 pool hashes bits)
      pure (getBlobsV4Json cells)
    -- The parameters of version 4 always hold a bitarray, so this case never happens.
    | _, none => throw (0, "params: no bitarray")
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
  let some version := getBlobsVersion method | throw (0, s!"no method {method}")
  let engine {α : Type} (act : Except EngineError α) : Result α :=
    act.mapError fun e => (e.code, s!"engine error: {reprStr e}")
  let result := result.toJson
  let answer : Json ← match version with
    | 1 => getBlobsV1Json <$> engine (getBlobsV1OfJson result)
    | 2 => getBlobsV2Json <$> engine (getBlobsV2OfJson result)
    | 3 => getBlobsV3Json <$> engine (getBlobsV3OfJson result)
    | _ => getBlobsV4Json <$> engine (getBlobsV4OfJson result)
  return .ofJson answer

/-- The result of an `engine_getBlobs` method, read from its JSON and written back.

The arguments are the method name and the result, as `json.loads` gives it.

A result that does not decode is reported as invalid parameters, with code 32602.

An unknown method name has code 0. -/
@[export eth_engine_read_get_blobs_result]
def readGetBlobsResultExport (args : PyValue) : Result PyValue :=
  pyExport readGetBlobsResultOf args

end EthLib.Engine.Exports
