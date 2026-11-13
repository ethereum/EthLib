module

public import EthLib.Cryptography.Kzg.Cells
public import EthLib.Engine.Json
public import EthLib.Serialization.Ssz.Codec.Deserialize

/-!
# `Engine.GetBlobs`

The method `engine_getBlobs`, versions 1 to 4, which reads blobs from the blob pool.

The consensus layer names blobs by their versioned hashes, and an answer keeps their order.

The pool is an input: what it holds for each hash, whether it serves, and its request limit.

The model trusts the pool: it files each blob under its own versioned hash.

Each proof and each cell that it holds also belongs to that blob.

The method checks none of this.

The limit is at least 128 hashes.

A longer request is too large, with JSON-RPC code `-38004`.

Version 1 answers a blob and its proof for each hash, and `null` for a blob it lacks.

A pool that does not serve answers `null` for every hash, as the source allows.

From Fusaka, version 1 is an unsupported fork, with code `-38005`.

The source sets no other fork rule, so EthLib answers every version at every other fork.

Version 2 answers each blob with one proof per cell of its extended blob.

It answers `null` alone when a blob or one of its cell proofs is missing.

A blob held with only its blob proof has no cell proofs, so it counts as missing.

Version 3 answers as version 2, with `null` only in place of each missing blob.

From version 2, a pool that does not serve answers `null` alone.

With cell sampling, a pool may hold only some cells of a blob.

Version 4 answers, for each blob of which the pool holds a cell, the selected cells.

Each cell comes with its proof, and a cell that the pool lacks is `null` with its proof.

A blob of which the pool holds no cell is `null`.

The source keeps `null` cells for an otherwise available blob.

EthLib reads available as holding a cell.

So a blob with only its blob proof is missing, as in version 2.

The cells are selected by a bitarray of 16 bytes, one bit for each of the 128 cells.

The Engine API gives no bit order, and EIP-8070 calls the bitarray a `uint128` with no byte order.

EthLib takes the order of an SSZ bitvector: cell `i` is bit `i mod 8` of byte `i / 8`.

The parameters are the array of versioned hashes, and from version 4 the bitarray.

Any other parameters are invalid, with code `-32602`.

The consensus layer also writes the parameters as JSON.

The source orders no two checks.

EthLib decodes the parameters first, then checks the fork of version 1, then the request size.

The answer is also written as JSON, and read back as a consensus node reads it.

A blob has 131072 bytes, and a proof 48 bytes.

The Engine API calls a cell a byte array and gives it no size.

EthLib takes the size of the cells of its KZG cell proofs, which is 2048 bytes.

The method specifications state these rules, at commit `3284ee8` of execution-apis:

- [`engine_getBlobsV1`][v1], and its update by Osaka in [`osaka.md`][v1-osaka]
- [`engine_getBlobsV2`][v2] and [`engine_getBlobsV3`][v3]
- [`engine_getBlobsV4`][v4], and the sampling of cells by the pool in [`amsterdam.md`][sampling]
- the bitarray of version 4 in [EIP-8070, "Engine API extensions"][eip8070]

[v1]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/cancun.md#engine_getblobsv1
[v1-osaka]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/osaka.md#cancun-api
[v2]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/osaka.md#engine_getblobsv2
[v3]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/osaka.md#engine_getblobsv3
[v4]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#engine_getblobsv4
[sampling]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#engine_forkchoiceupdatedv4
[eip8070]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-8070.md#engine-api-extensions
-/

@[expose] public section

namespace EthLib.Engine

open Lean (Json)
open EthLib.Base
open EthLib.Cryptography.Kzg
open EthLib.Cryptography.Kzg.Constants
open EthLib.Engine.Json
open EthLib.Serialization.JsonRpc
open EthLib.Execution.Rpc (withdrawal)

/-- The fewest versioned hashes that every pool must take in one request. -/
def MIN_BLOBS_REQUEST_LIMIT : Nat := 128

/-- The bytes of a bitarray with one bit per cell of an extended blob. -/
def CELL_BITARRAY_BYTES : Nat := CELLS_PER_EXT_BLOB / 8

/-- A bitarray with one bit per cell of an extended blob. -/
abbrev CellBitarray := Vector UInt8 CELL_BITARRAY_BYTES

/-- What the blob pool holds for one versioned hash. -/
structure PooledBlob where
  /-- The blob, if the pool holds all of it. -/
  blob : Option Blob
  /-- The proof of the whole blob, which a blob transaction carries in its first network form. -/
  blobProof : Option KZGProof
  /-- Each cell of the extended blob with its proof, where the pool holds it. -/
  cells : Vector (Option (Cell × KZGProof)) CELLS_PER_EXT_BLOB

/-- The blob pool of an execution layer, as the method reads it. -/
structure BlobPool where
  /-- What the pool holds for a versioned hash, if anything. -/
  lookup : Bytes32 → Option PooledBlob
  /-- Whether the pool serves its data at all; a syncing node may not. -/
  serving : Bool
  /-- The most versioned hashes that one request may name. -/
  maxRequest : Nat
  /-- The source requires that a pool take every request of up to 128 hashes. -/
  le_maxRequest : MIN_BLOBS_REQUEST_LIMIT ≤ maxRequest

/-- A blob and its proof, as version 1 answers them. -/
structure BlobAndProofV1 where
  /-- The blob. -/
  blob : Blob
  /-- The KZG proof of the whole blob. -/
  proof : KZGProof
  deriving DecidableEq

/-- A blob and the proofs of the cells of its extended blob, as versions 2 and 3 answer them. -/
structure BlobAndProofV2 where
  /-- The blob. -/
  blob : Blob
  /-- The KZG proof of each cell, in the order of the cells. -/
  proofs : Vector KZGProof CELLS_PER_EXT_BLOB
  deriving DecidableEq

/-- The selected cells of a blob, as version 4 answers them. -/
structure BlobCellsAndProofsV1 where
  /-- Each selected cell with its proof, in order, or `none` where the pool lacks it. -/
  cells : List (Option (Cell × KZGProof))
  deriving DecidableEq

namespace PooledBlob

/-- The blob and its blob proof, if the pool holds both. -/
def toV1 (p : PooledBlob) : Option BlobAndProofV1 := do
  return ⟨← p.blob, ← p.blobProof⟩

/-- The proof of each cell, if the pool holds every cell. -/
def cellProofs (p : PooledBlob) : Option (Vector KZGProof CELLS_PER_EXT_BLOB) :=
  if h : ∀ i : Fin CELLS_PER_EXT_BLOB, (p.cells[i]).isSome then
    some (Vector.ofFn fun i => ((p.cells[i]).get (h i)).2)
  else none

/-- The blob and the proof of each cell, if the pool holds all of them. -/
def toV2 (p : PooledBlob) : Option BlobAndProofV2 := do
  return ⟨← p.blob, ← p.cellProofs⟩

/-- Whether the pool holds one of the cells of the blob. -/
def holdsCell (p : PooledBlob) : Bool :=
  p.cells.toList.any Option.isSome

/-- The cell at each index, in order, with its proof, or `none` where the pool lacks it. -/
def cellsAt (p : PooledBlob) (indices : List (Fin CELLS_PER_EXT_BLOB)) :
    List (Option (Cell × KZGProof)) :=
  indices.map fun i => p.cells[i]

/-- The cells at the indices, if the pool holds one of the cells of the blob. -/
def toV4 (p : PooledBlob) (indices : List (Fin CELLS_PER_EXT_BLOB)) :
    Option BlobCellsAndProofsV1 :=
  if p.holdsCell then some ⟨p.cellsAt indices⟩ else none

end PooledBlob

/-- The cell indices that a bitarray sets, in increasing order, read as an SSZ bitvector. -/
def selectedCells (bits : CellBitarray) : List (Fin CELLS_PER_EXT_BLOB) :=
  let set := Serialization.Ssz.unpackBits bits.toArray CELLS_PER_EXT_BLOB
  (List.finRange CELLS_PER_EXT_BLOB).filter fun i => set[i.val]?.getD false

/-- The number of parameters of a version: the hashes, and from version 4 the bitarray. -/
def getBlobsParamCount (version : Nat) : Nat := if version ≥ 4 then 2 else 1

/-- The parameters of a version: the versioned hashes, and from version 4 the bitarray. -/
def getBlobsParams (version : Nat) (params : Json) :
    Decode (List Bytes32 × Option CellBitarray) := do
  let params ← paramsArray params
  let count := getBlobsParamCount version
  match params, decide (count = 2) with
  | [hashes], false => return (← array "hashes" (fixed "versioned hash" 32) hashes, none)
  | [hashes, bits], true =>
    return (← array "hashes" (fixed "versioned hash" 32) hashes,
      some (← fixed "indices_bitarray" CELL_BITARRAY_BYTES bits))
  | _, _ => invalid s!"params: got {params.length}, expected {count}"

/-- The parameters as JSON: the versioned hashes, then the bitarray when there is one. -/
def getBlobsParamsJson (hashes : List Bytes32) (bits : Option CellBitarray) : Json :=
  .arr (([listJson (dataJson ·.toList) hashes] ++ bits.toList.map (dataJson ·.toList)).toArray)

/-- Version 1 at the active fork of the node: a blob and its proof for each hash, or `null`.

From Fusaka the version is an unsupported fork. -/
def getBlobsV1 (pool : BlobPool) (fork : Fork) (hashes : List Bytes32) :
    Except EngineError (List (Option BlobAndProofV1)) := do
  if fork ≥ .fusaka then throw .unsupportedFork
  checkRequestSize pool.maxRequest hashes.length
  return hashes.map fun h => if pool.serving then (pool.lookup h).bind PooledBlob.toV1 else none

/-- Version 2: each blob with its cell proofs, or `null` alone if one is missing. -/
def getBlobsV2 (pool : BlobPool) (hashes : List Bytes32) :
    Except EngineError (Option (List BlobAndProofV2)) := do
  checkRequestSize pool.maxRequest hashes.length
  if pool.serving then return hashes.mapM fun h => (pool.lookup h).bind PooledBlob.toV2
  else return none

/-- Version 3: each blob with its cell proofs, with `null` in place of each missing blob. -/
def getBlobsV3 (pool : BlobPool) (hashes : List Bytes32) :
    Except EngineError (Option (List (Option BlobAndProofV2))) := do
  checkRequestSize pool.maxRequest hashes.length
  if pool.serving then return some (hashes.map fun h => (pool.lookup h).bind PooledBlob.toV2)
  else return none

/-- Version 4: for each blob of which the pool holds a cell, the selected cells.

A blob of which the pool holds no cell is `null`. -/
def getBlobsV4 (pool : BlobPool) (hashes : List Bytes32) (bits : CellBitarray) :
    Except EngineError (Option (List (Option BlobCellsAndProofsV1))) := do
  checkRequestSize pool.maxRequest hashes.length
  if pool.serving then
    return some (hashes.map fun h => (pool.lookup h).bind (·.toV4 (selectedCells bits)))
  else return none

/-! ## The answer as JSON -/

/-- A blob and its proof as JSON. -/
def blobAndProofV1Json (x : BlobAndProofV1) : Json :=
  Json.mkObj [("blob", dataJson x.blob.toList), ("proof", dataJson x.proof.toList)]

/-- A blob and the proofs of its cells as JSON. -/
def blobAndProofV2Json (x : BlobAndProofV2) : Json :=
  Json.mkObj [("blob", dataJson x.blob.toList),
    ("proofs", listJson (dataJson ·.toList) x.proofs.toList)]

/-- The selected cells of a blob as JSON: the cells, then their proofs, with `null` where absent.

The two arrays hold `null` at the same positions. -/
def blobCellsJson (x : BlobCellsAndProofsV1) : Json :=
  Json.mkObj [
    ("blob_cells", listJson (optionJson (dataJson ·.1.toList)) x.cells),
    ("proofs", listJson (optionJson (dataJson ·.2.toList)) x.cells)]

/-- A blob and its proof: exactly the two fields. -/
def blobAndProofV1OfJson (j : Json) : Read BlobAndProofV1 := do
  let fs ← fields "blobAndProof" j
  unless hasExactly fs ["blob", "proof"] do reject "blobAndProof: not the fields of version 1"
  return {
    blob := ← fixed "blob" BYTES_PER_BLOB (← field "blobAndProof" fs "blob")
    proof := ← fixed "proof" 48 (← field "blobAndProof" fs "proof") }

/-- A blob and the proofs of its cells: exactly the two fields, with one proof per cell. -/
def blobAndProofV2OfJson (j : Json) : Read BlobAndProofV2 := do
  let fs ← fields "blobAndProof" j
  unless hasExactly fs ["blob", "proofs"] do reject "blobAndProof: not the fields of version 2"
  let blob ← fixed "blob" BYTES_PER_BLOB (← field "blobAndProof" fs "blob")
  let proofs ← array "proofs" (fixed "proof" 48) (← field "blobAndProof" fs "proofs")
  if h : proofs.length = CELLS_PER_EXT_BLOB then
    return { blob, proofs := ⟨proofs.toArray, by simpa using h⟩ }
  else reject s!"proofs: {proofs.length}, not {CELLS_PER_EXT_BLOB}"

/-- A cell and its proof at one position, which must both be present or both be `null`. -/
def cellAndProof : Option Cell × Option KZGProof → Read (Option (Cell × KZGProof))
  | (some cell, some proof) => pure (some (cell, proof))
  | (none, none) => pure none
  | _ => reject "blobCells: a cell and its proof, one of them null"

/-- The selected cells of a blob: two arrays of one length, with `null` at the same positions.

The source asks a proof to be `null` where its cell is `null`, in step 4 of version 4.

EthLib also rejects a cell whose proof is `null`, since that cell cannot be checked. -/
def blobCellsOfJson (j : Json) : Read BlobCellsAndProofsV1 := do
  let fs ← fields "blobCells" j
  unless hasExactly fs ["blob_cells", "proofs"] do reject "blobCells: not the fields of version 1"
  let cells ← array "blob_cells" (nullable (fixed "cell" BYTES_PER_CELL))
    (← field "blobCells" fs "blob_cells")
  let proofs ← array "proofs" (nullable (fixed "proof" 48)) (← field "blobCells" fs "proofs")
  unless cells.length = proofs.length do reject "blobCells: arrays of two lengths"
  return ⟨← (cells.zip proofs).mapM cellAndProof⟩

/-- The answer of version 1 as JSON: a blob and its proof, or `null`, for each hash. -/
def getBlobsV1Json (blobs : List (Option BlobAndProofV1)) : Json :=
  listJson (optionJson blobAndProofV1Json) blobs

/-- The answer of version 2 as JSON: the blobs with their cell proofs, or `null` alone. -/
def getBlobsV2Json (blobs : Option (List BlobAndProofV2)) : Json :=
  optionJson (listJson blobAndProofV2Json) blobs

/-- The answer of version 3 as JSON: the blobs or `null` for each hash, or `null` alone. -/
def getBlobsV3Json (blobs : Option (List (Option BlobAndProofV2))) : Json :=
  optionJson (listJson (optionJson blobAndProofV2Json)) blobs

/-- The answer of version 4 as JSON: the cells or `null` for each hash, or `null` alone. -/
def getBlobsV4Json (blobs : Option (List (Option BlobCellsAndProofsV1))) : Json :=
  optionJson (listJson (optionJson blobCellsJson)) blobs

/-- The answer of version 1: an array whose entries are a blob and its proof, or `null`. -/
def getBlobsV1OfJson (j : Json) : Decode (List (Option BlobAndProofV1)) :=
  lift (array "result" (nullable blobAndProofV1OfJson) j)

/-- The answer of version 2: an array of blobs with their cell proofs, or `null` alone. -/
def getBlobsV2OfJson (j : Json) : Decode (Option (List BlobAndProofV2)) :=
  lift (nullable (array "result" blobAndProofV2OfJson) j)

/-- The answer of version 3: an array whose entries are blobs or `null`, or `null` alone. -/
def getBlobsV3OfJson (j : Json) : Decode (Option (List (Option BlobAndProofV2))) :=
  lift (nullable (array "result" (nullable blobAndProofV2OfJson)) j)

/-- The answer of version 4: an array whose entries are cells or `null`, or `null` alone. -/
def getBlobsV4OfJson (j : Json) : Decode (Option (List (Option BlobCellsAndProofsV1))) :=
  lift (nullable (array "result" (nullable blobCellsOfJson)) j)

end EthLib.Engine
