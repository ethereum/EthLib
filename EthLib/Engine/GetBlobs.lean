module

public import EthLib.Cryptography.Kzg.Cells
public import EthLib.Engine.Json
public import EthLib.Serialization.Ssz.Codec.Deserialize

/-!
# `Engine.GetBlobs`

The method `engine_getBlobs`, versions 1 to 4, which reads blobs from the blob pool.

A step comment names the version of the method, as in version 3, step 4.

Sources, at commit `1ca0818` of execution-apis: versions [1][v1], [2][v2], [3][v3] and [4][v4].

Version 1 has an [update by Osaka][v1-osaka], and the pool [samples cells][sampling] from Amsterdam.

Version 4 takes its bitarray from [EIP-8070][eip8070], section Engine API extensions.

[v1]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/cancun.md#engine_getblobsv1
[v1-osaka]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/osaka.md#cancun-api
[v2]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/osaka.md#engine_getblobsv2
[v3]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/osaka.md#engine_getblobsv3
[v4]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/amsterdam.md#engine_getblobsv4
[sampling]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/amsterdam.md#engine_forkchoiceupdatedv4
[eip8070]: https://github.com/ethereum/EIPs/blob/d27448e08f60513856bbe228ea7ce04f156209dc/EIPS/eip-8070.md#engine-api-extensions
-/

@[expose] public section

namespace EthLib.Engine

open Lean (Json)
open EthLib.Base
open EthLib.Cryptography.Kzg
open EthLib.Cryptography.Kzg.Constants
open EthLib.Engine.Json
open EthLib.Serialization.JsonRpc
open EthLib.Execution.Rpc (withdrawal versionedHash versionedHashJson)

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

/-- The blob pool of an execution layer, an input of the method. -/
structure BlobPool where
  -- The model trusts the pool: it files each blob under its own versioned hash.
  --
  -- Each proof and each cell that it holds also belongs to that blob.
  --
  -- The method checks none of this.
  /-- What the pool holds for a versioned hash, if anything. -/
  lookup : VersionedHash → Option PooledBlob
  /-- Whether the pool serves its data at all; a syncing node may not. -/
  serving : Bool
  /-- The most versioned hashes that one request may name. -/
  maxRequest : Nat
  -- Version 1, step 3, version 2, step 3, version 3, step 4, and version 4, step 5.
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
  -- Version 1, step 2: a missing blob is `null`.
  --
  -- EthLib also counts a blob without its blob proof as missing, since the answer needs both.
  return ⟨← p.blob, ← p.blobProof⟩

/-- The proof of each cell, if the pool holds every cell. -/
def cellProofs (p : PooledBlob) : Option (Vector KZGProof CELLS_PER_EXT_BLOB) :=
  -- `BlobAndProofV2`: exactly `CELLS_PER_EXT_BLOB = 128` cell proofs, so each cell is held.
  if h : ∀ i : Fin CELLS_PER_EXT_BLOB, (p.cells[i]).isSome then
    some (Vector.ofFn fun i => ((p.cells[i]).get (h i)).2)
  -- Version 2, step 2.2: a blob held with only its blob proof has no cell proofs.
  --
  -- So it counts as missing.
  else none

/-- The blob and the proof of each cell, if the pool holds all of them. -/
def toV2 (p : PooledBlob) : Option BlobAndProofV2 := do
  -- Version 2, step 2: a blob is missing when the pool lacks it or one of its cell proofs.
  return ⟨← p.blob, ← p.cellProofs⟩

/-- Whether the pool holds one of the cells of the blob. -/
def holdsCell (p : PooledBlob) : Bool :=
  -- With the cell sampling of Amsterdam, a pool may hold only some cells of a blob.
  p.cells.toList.any Option.isSome

/-- The cell at each index, in order, with its proof, or `none` where the pool lacks it. -/
def cellsAt (p : PooledBlob) (indices : List (Fin CELLS_PER_EXT_BLOB)) :
    List (Option (Cell × KZGProof)) :=
  -- Version 4, step 1: only the cells at the selected indices, each with its KZG proof.
  --
  -- Step 4: a cell that the pool lacks is `null`, and so is its proof.
  indices.map fun i => p.cells[i]

/-- The cells at the indices, if the pool holds one of the cells of the blob. -/
def toV4 (p : PooledBlob) (indices : List (Fin CELLS_PER_EXT_BLOB)) :
    Option BlobCellsAndProofsV1 :=
  -- Version 4, step 4 keeps `null` cells for an otherwise available blob.
  --
  -- The source does not define available.
  --
  -- EthLib reads available as holding a cell, and a blob of which the pool holds none is missing.
  --
  -- So a blob held with only its blob proof is missing, as in version 2.
  if p.holdsCell then some ⟨p.cellsAt indices⟩ else none

end PooledBlob

/-- The cell indices that a bitarray sets, in increasing order, read as an SSZ bitvector. -/
def selectedCells (bits : CellBitarray) : List (Fin CELLS_PER_EXT_BLOB) :=
  -- Version 4, request: a bitarray of 16 bytes, one bit for each of the 128 cells.
  --
  -- The Engine API gives no bit order, and EIP-8070 calls the bitarray a `uint128`.
  --
  -- EIP-8070 gives it no byte order either.
  --
  -- EthLib takes the order of an SSZ bitvector: cell `i` is bit `i mod 8` of byte `i / 8`.
  let set := Serialization.Ssz.unpackBits ⟨bits.toArray⟩ CELLS_PER_EXT_BLOB
  -- Version 4, step 1: the indices that the bitarray sets.
  --
  -- The source gives the cells no order, and EthLib takes increasing index.
  (List.finRange CELLS_PER_EXT_BLOB).filter fun i => set[i.val]?.getD false

/-- The number of parameters of a version: the hashes, and from version 4 the bitarray. -/
def getBlobsParamCount (version : Nat) : Nat :=
  -- Version 4 adds the bitarray as a second parameter.
  if version ≥ 4 then 2 else 1

/-- The parameters of a version: the versioned hashes, and from version 4 the bitarray. -/
def getBlobsParams (version : Nat) (params : Json) :
    Decode (List VersionedHash × Option CellBitarray) := do
  let params ← paramsArray params
  let count := getBlobsParamCount version
  match params, decide (count = 2) with
  -- Versions 1 to 3, request: one parameter, an `Array of DATA` of 32 bytes each.
  | [hashes], false => return (← array "hashes" (versionedHash "versioned hash") hashes, none)
  -- Version 4, request: that array, then the bitarray of cell indices, `DATA` of 16 bytes.
  | [hashes, bits], true =>
    return (← array "hashes" (versionedHash "versioned hash") hashes,
      some (← fixed "indices_bitarray" CELL_BITARRAY_BYTES bits))
  -- The source names no error for other parameters, and EthLib gives `-32602`, invalid params.
  | _, _ => invalid s!"params: got {params.length}, expected {count}"

/-- The parameters as JSON: the versioned hashes, then the bitarray when there is one. -/
def getBlobsParamsJson (hashes : List VersionedHash) (bits : Option CellBitarray) : Json :=
  -- The consensus layer also writes the parameters as JSON.
  --
  -- The request of the version: the array of versioned hashes, then from version 4 the bitarray.
  .arr (([listJson versionedHashJson hashes] ++ bits.toList.map (dataJson ·.toList)).toArray)

/-- Version 1 at the active fork of the node: a blob and its proof for each hash, or `null`.

From Fusaka the version is an unsupported fork. -/
def getBlobsV1 (pool : BlobPool) (fork : Fork) (hashes : List VersionedHash) :
    Except EngineError (List (Option BlobAndProofV1)) := do
  -- The source orders no two checks.
  --
  -- The parameters are decoded before this, then EthLib checks the fork, then the request size.
  --
  -- The update of Osaka: from Osaka, here Fusaka, the error is `-38005`, unsupported fork.
  --
  -- It is the only fork rule of the source, so EthLib answers every version at every other fork.
  if fork ≥ .fusaka then throw (.unsupportedFork (some fork))
  -- Version 1, step 3: more hashes than the pool takes is `-38004`, too large request.
  checkRequestSize pool.maxRequest hashes.length
  -- Steps 1 and 2: for each hash in order, its blob and proof, or `null` for a missing blob.
  --
  -- Step 4: a pool that does not serve may answer `null` for every hash, and EthLib does so.
  --
  -- Step 5: a pruned blob is missing.
  return hashes.map fun h => if pool.serving then (pool.lookup h).bind PooledBlob.toV1 else none

/-- Version 2: each blob with its cell proofs, or `null` alone if one is missing. -/
def getBlobsV2 (pool : BlobPool) (hashes : List VersionedHash) :
    Except EngineError (Option (List BlobAndProofV2)) := do
  -- Version 2, step 3: more hashes than the pool takes is `-38004`, too large request.
  checkRequestSize pool.maxRequest hashes.length
  -- Step 1: for each hash in order, its blob with its cell proofs.
  --
  -- Step 2: `null` alone when any blob is missing.
  --
  -- Step 5: a pruned blob is missing.
  if pool.serving then return hashes.mapM fun h => (pool.lookup h).bind PooledBlob.toV2
  -- Step 4: `null` when the pool does not serve.
  else return none

/-- Version 3: each blob with its cell proofs, with `null` in place of each missing blob. -/
def getBlobsV3 (pool : BlobPool) (hashes : List VersionedHash) :
    Except EngineError (Option (List (Option BlobAndProofV2))) := do
  -- Version 3, step 4: more hashes than the pool takes is `-38004`, too large request.
  checkRequestSize pool.maxRequest hashes.length
  -- Steps 1 and 2: for each hash in order, its blob with its cell proofs.
  --
  -- Step 3: `null` only at the position of each missing blob, missing as in version 2, step 2.
  --
  -- Step 6: a pruned blob is missing.
  if pool.serving then return some (hashes.map fun h => (pool.lookup h).bind PooledBlob.toV2)
  -- Step 5: `null` when the pool does not serve.
  else return none

/-- Version 4: for each blob of which the pool holds a cell, the selected cells.

A blob of which the pool holds no cell is `null`. -/
def getBlobsV4 (pool : BlobPool) (hashes : List VersionedHash) (bits : CellBitarray) :
    Except EngineError (Option (List (Option BlobCellsAndProofsV1))) := do
  -- Version 4, step 5: more hashes than the pool takes is `-38004`, too large request.
  checkRequestSize pool.maxRequest hashes.length
  if pool.serving then
    -- Steps 1 and 2: for each hash in order, the cells that one bitarray selects in every blob.
    --
    -- Step 3: `null` only at the position of each missing blob.
    --
    -- Step 7: a pruned blob is missing.
    return some (hashes.map fun h => (pool.lookup h).bind (·.toV4 (selectedCells bits)))
  -- Step 6: `null` when the pool does not serve.
  else return none

/-!
## The answer as JSON

The answer is also written as JSON, and read back as a consensus node reads it.
-/

/-- A blob and its proof as JSON. -/
def blobAndProofV1Json (x : BlobAndProofV1) : Json :=
  -- `BlobAndProofV1`: `blob` and `proof`, each `DATA`.
  Json.mkObj [("blob", dataJson x.blob.toList), ("proof", dataJson x.proof.toList)]

/-- A blob and the proofs of its cells as JSON. -/
def blobAndProofV2Json (x : BlobAndProofV2) : Json :=
  -- `BlobAndProofV2`: `blob`, `DATA`, and `proofs`, an `Array of DATA` in the order of the cells.
  Json.mkObj [("blob", dataJson x.blob.toList),
    ("proofs", listJson (dataJson ·.toList) x.proofs.toList)]

/-- The selected cells of a blob as JSON: the cells, then their proofs, with `null` where absent.

The two arrays hold `null` at the same positions. -/
def blobCellsJson (x : BlobCellsAndProofsV1) : Json :=
  -- `BlobCellsAndProofsV1`: the cells and the proofs, each an `Array of DATA|null`.
  --
  -- A proof is `null` where its cell is `null`, by step 4 of version 4.
  Json.mkObj [
    ("blob_cells", listJson (optionJson (dataJson ·.1.toList)) x.cells),
    ("proofs", listJson (optionJson (dataJson ·.2.toList)) x.cells)]

/-- A blob and its proof: exactly the two fields. -/
def blobAndProofV1OfJson (j : Json) : Read BlobAndProofV1 := do
  let fs ← fields "blobAndProof" j
  -- `BlobAndProofV1`: the fields `blob` and `proof`.
  --
  -- Not in the source: EthLib rejects any other member.
  unless hasExactly fs ["blob", "proof"] do reject "blobAndProof: not the fields of version 1"
  return {
    -- The blob is `FIELD_ELEMENTS_PER_BLOB * BYTES_PER_FIELD_ELEMENT = 4096 * 32 = 131072` bytes.
    blob := ← fixed "blob" BYTES_PER_BLOB (← field "blobAndProof" fs "blob")
    -- The proof is a `KZGProof` of 48 bytes.
    proof := ← fixed "proof" 48 (← field "blobAndProof" fs "proof") }

/-- A blob and the proofs of its cells: exactly the two fields, with one proof per cell. -/
def blobAndProofV2OfJson (j : Json) : Read BlobAndProofV2 := do
  let fs ← fields "blobAndProof" j
  -- `BlobAndProofV2`: the fields `blob` and `proofs`.
  --
  -- Not in the source: EthLib rejects any other member.
  unless hasExactly fs ["blob", "proofs"] do reject "blobAndProof: not the fields of version 2"
  -- The blob is `4096 * 32 = 131072` bytes.
  let blob ← fixed "blob" BYTES_PER_BLOB (← field "blobAndProof" fs "blob")
  -- Each proof is a `KZGProof` of 48 bytes.
  let proofs ← array "proofs" (fixed "proof" 48) (← field "blobAndProof" fs "proofs")
  -- `proofs` contains exactly `CELLS_PER_EXT_BLOB` cell proofs.
  let proofs ← exactArray CELLS_PER_EXT_BLOB proofs.toArray fun count =>
    s!"proofs: {count}, not {CELLS_PER_EXT_BLOB}"
  return { blob, proofs }

/-- A cell and its proof at one position, which must both be present or both be `null`. -/
def cellAndProof : Option Cell × Option KZGProof → Read (Option (Cell × KZGProof))
  | (some cell, some proof) => pure (some (cell, proof))
  -- Version 4, step 4: a missing cell is `null`, and its proof is `null` too.
  | (none, none) => pure none
  -- A `null` cell with a proof breaks step 4.
  --
  -- Not in the source: a cell with a `null` proof is rejected too, since it cannot be checked.
  | _ => reject "blobCells: a cell and its proof, one of them null"

/-- The selected cells of a blob: two arrays of one length, with `null` at the same positions. -/
def blobCellsOfJson (j : Json) : Read BlobCellsAndProofsV1 := do
  let fs ← fields "blobCells" j
  -- `BlobCellsAndProofsV1`: the fields of the cells and of the proofs.
  --
  -- Not in the source: EthLib rejects any other member.
  unless hasExactly fs ["blob_cells", "proofs"] do reject "blobCells: not the fields of version 1"
  -- The structure gives each cell 64 field elements of 32 bytes, that is 2048 bytes.
  --
  -- That is the size of the cells of the KZG cell proofs of EthLib.
  let cells ← array "blob_cells" (nullable (fixed "cell" BYTES_PER_CELL))
    (← field "blobCells" fs "blob_cells")
  -- Each proof is a `KZGProof` of 48 bytes, or `null`.
  let proofs ← array "proofs" (nullable (fixed "proof" 48)) (← field "blobCells" fs "proofs")
  -- Not in the source: the two arrays have one length.
  unless cells.length = proofs.length do reject "blobCells: arrays of two lengths"
  return ⟨← (cells.zip proofs).mapM cellAndProof⟩

/-- The answer of version 1 as JSON: a blob and its proof, or `null`, for each hash. -/
def getBlobsV1Json (blobs : List (Option BlobAndProofV1)) : Json :=
  -- Version 1, response: an `Array of BlobAndProofV1`, items of which may be `null`.
  listJson (optionJson blobAndProofV1Json) blobs

/-- The answer of version 2 as JSON: the blobs with their cell proofs, or `null` alone. -/
def getBlobsV2Json (blobs : Option (List BlobAndProofV2)) : Json :=
  -- Version 2, response: `(Array of BlobAndProofV2) | null`.
  optionJson (listJson blobAndProofV2Json) blobs

/-- The answer of version 3 as JSON: the blobs or `null` for each hash, or `null` alone. -/
def getBlobsV3Json (blobs : Option (List (Option BlobAndProofV2))) : Json :=
  -- Version 3, response: `(Array of BlobAndProofV2) | null`, with `null` at each missing blob.
  optionJson (listJson (optionJson blobAndProofV2Json)) blobs

/-- The answer of version 4 as JSON: the cells or `null` for each hash, or `null` alone. -/
def getBlobsV4Json (blobs : Option (List (Option BlobCellsAndProofsV1))) : Json :=
  -- Version 4, response: `(Array of BlobCellsAndProofsV1) | null`, `null` at each missing blob.
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
