module

public import EthLib.Consensus.Containers.Bid
public import EthLib.Consensus.DataAvailability.Blob
public import EthLib.Consensus.DataAvailability.Custody
public import EthLib.Consensus.ForkSchedule
public import EthLib.Consensus.Time
public import EthLib.Cryptography.Kzg.Recovery
public import EthLib.Serialization.Ssz.Type.Bounds

/-!
# `Consensus.DataAvailability.Column`

From Fulu, the blobs of a block travel as columns of cells instead of whole blobs.

Each blob is extended to twice its length and cut into 128 cells, one row of a matrix.

Column `i` holds cell `i` of every row, with the proof of each cell.

A node that holds half of the columns of a row can recover the whole row.

At Fulu, a column sidecar carries one column, the commitments of the block and its signed header.

A Merkle branch shows that the list of commitments is in the body that the header names.

Gloas moves the commitments into the bid of the builder, so a sidecar names its block by root.

From Gloas, the largest size of a serialized sidecar follows from the largest blob limit.

At Fulu, a node may also send part of a column: the cells that a bitmap marks, with their proofs.

A partial sidecar carries the header of its block only on the first push, as a list of at most one.

The header holds the commitments of the block, its signed header and the branch between them.

Gloas drops that header, and the group of a partial message also names the slot of its block.

[EIP-7594] specifies the matrix, the sidecars and their checks.

[EIP-7594]: https://eips.ethereum.org/EIPS/eip-7594#specification
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Cryptography.Kzg Serialization.Ssz
open DataAvailability (ColumnIndex)

/-- One column of the matrix of a block, with its proofs and what ties it to the block.

Gloas removes the commitments, the header and the branch, and adds the slot and the block root.

Gloas also makes the column and its proofs progressive lists, as [EIP-7688] specifies.

[EIP-7688]: https://eips.ethereum.org/EIPS/eip-7688#specification -/
structure DataColumnSidecar (preset : Preset) (fork : Fork) where
  /-- The index of the column. -/
  index : ColumnIndex
  /-- The cell of each blob in the column, in the order of the blobs. -/
  column : ForkList .glamsterdam fork Cell preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat
  /-- Before Gloas: the commitments to all the blobs of the block. -/
  kzgCommitments : Until .glamsterdam fork (BlobKZGCommitments preset fork)
  /-- The proof of each cell of the column. -/
  kzgProofs : ForkList .glamsterdam fork KZGProof preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat
  /-- Before Gloas: the header of the block, signed by its proposer. -/
  signedBlockHeader : Until .glamsterdam fork SignedBeaconBlockHeader
  /-- Before Gloas: the branch from the commitments up to the body root, nearest node first. -/
  kzgCommitmentsInclusionProof :
    Until .glamsterdam fork (Vector Bytes32 preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat)
  /-- From Gloas: the slot of the block. -/
  slot : Since .glamsterdam fork Slot
  /-- From Gloas: the root of the block. -/
  beaconBlockRoot : Since .glamsterdam fork Root

namespace DataColumnSidecar

/-- The names of the fields of a sidecar at a fork, in their order. -/
def names (fork : Fork) : List String :=
  ["index", "column"] ++ untilNames .glamsterdam fork ["kzg_commitments"] ++ ["kzg_proofs"] ++
    untilNames .glamsterdam fork ["signed_block_header", "kzg_commitments_inclusion_proof"] ++
    sinceNames .glamsterdam fork ["slot", "beacon_block_root"]

instance {preset : Preset} {fork : Fork} : SszType (DataColumnSidecar preset fork) :=
  .container (names fork)
    (fun s => (s.index, s.column, s.kzgCommitments, s.kzgProofs, s.signedBlockHeader,
      s.kzgCommitmentsInclusionProof, s.slot, s.beaconBlockRoot))
    (fun (index, column, kzgCommitments, kzgProofs, signedBlockHeader,
        kzgCommitmentsInclusionProof, slot, beaconBlockRoot) =>
      ⟨index, column, kzgCommitments, kzgProofs, signedBlockHeader, kzgCommitmentsInclusionProof,
        slot, beaconBlockRoot⟩)

end DataColumnSidecar

/-- One cell of the matrix, with its proof, its column and its row. -/
structure MatrixEntry where
  /-- The cell. -/
  cell : Cell
  /-- The proof that the cell matches the commitment of its row. -/
  kzgProof : KZGProof
  /-- The column of the cell, which is its index in the extended blob. -/
  columnIndex : ColumnIndex
  /-- The row of the cell, which is the index of its blob in the block. -/
  rowIndex : RowIndex
  deriving DecidableEq

instance : SszType MatrixEntry :=
  .container ["cell", "kzg_proof", "column_index", "row_index"]
    (fun e => (e.cell, e.kzgProof, e.columnIndex, e.rowIndex))
    (fun (cell, kzgProof, columnIndex, rowIndex) => ⟨cell, kzgProof, columnIndex, rowIndex⟩)

/-- A request for some columns of one block: the root of the block and the column indices. -/
structure DataColumnsByRootIdentifier (preset : Preset) where
  /-- The root of the block. -/
  blockRoot : Root
  /-- The indices of the columns. -/
  columns : SszList ColumnIndex preset.NUMBER_OF_COLUMNS.toNat
  deriving DecidableEq

instance {preset : Preset} : SszType (DataColumnsByRootIdentifier preset) :=
  .container ["block_root", "columns"] (fun i => (i.blockRoot, i.columns))
    (fun (blockRoot, columns) => ⟨blockRoot, columns⟩)

/-- The generalized index of the list of blob commitments, in the tree of a block body. -/
def blobKzgCommitmentsGindex (preset : Preset) (fork : Fork) : Except Err Nat :=
  -- The path through the body: its field of blob commitments.
  SszType.getGeneralizedIndex (BeaconBlockBody preset fork)
    [.position ((BeaconBlockBody.names fork).idxOf "blob_kzg_commitments")]

/-- From Gloas, a fork is not before Gloas. -/
theorem not_lt_glamsterdam {fork : Fork} (gloas : ¬fork < .glamsterdam) : .glamsterdam ≤ fork :=
  Nat.le_of_not_lt gloas

/-- Before Gloas, a fork is not from Gloas on. -/
theorem not_glamsterdam_le {fork : Fork} (beforeGloas : fork < .glamsterdam) :
    ¬.glamsterdam ≤ fork :=
  fun after => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le beforeGloas after)

/-- The commitments that the cells of a sidecar answer to. -/
def DataColumnSidecar.commitments {preset : Preset} {fork : Fork}
    (sidecar : DataColumnSidecar preset fork)
    (bidCommitments : Since .glamsterdam fork (BlobKZGCommitments preset fork)) :
    BlobKZGCommitments preset fork :=
  -- Before Gloas, those that the sidecar carries.
  if beforeGloas : fork < .glamsterdam then sidecar.kzgCommitments beforeGloas
  -- From Gloas, those of the bid of the block, as EIP-7732 specifies.
  else bidCommitments (not_lt_glamsterdam beforeGloas)

/-- From Gloas, the commitments in the bid of a block.

The sidecars that name the block by its root answer to them. -/
def BeaconBlock.bidCommitments {preset : Preset} {fork : Fork} (block : BeaconBlock preset fork) :
    Since .glamsterdam fork (BlobKZGCommitments preset fork) :=
  -- The commitments of the signed bid in the body.
  fun gloas => (block.body.signedExecutionPayloadBid gloas).message.blobKzgCommitments

/-- Whether a sidecar has a valid shape. -/
def verifyDataColumnSidecar (preset : Preset) (config : Config) {fork : Fork}
    (sidecar : DataColumnSidecar preset fork)
    (bidCommitments : Since .glamsterdam fork (BlobKZGCommitments preset fork)) : Bool :=
  -- Let `n` be the number of commitments that the cells answer to.
  let count := (sidecar.commitments bidCommitments).data.size
  -- Before Gloas, `n` is at most the blob limit at the epoch of the slot of the header.
  let withinLimit := if beforeGloas : fork < .glamsterdam then
    let epoch := computeEpochAtSlot preset (sidecar.signedBlockHeader beforeGloas).message.slot
    count ≤ (config.getBlobParameters epoch).maxBlobsPerBlock.toNat
  -- From Gloas there is no such bound.
  else true
  -- The index is below `NUMBER_OF_COLUMNS`, `n` is not 0, and the column has `n` cells.
  --
  -- The column also has as many proofs as cells.
  --
  -- From Gloas the rule asks for a nonempty column; with `n` cells it is the same as `n` not 0.
  sidecar.index < preset.NUMBER_OF_COLUMNS && count != 0 && withinLimit &&
    sidecar.column.data.size == count && sidecar.column.data.size == sidecar.kzgProofs.data.size

/-- Whether the cells of a sidecar match its commitments, by their proofs.

The batch check fails with an error on inputs it cannot read, such as unequal counts. -/
def verifyDataColumnSidecarKzgProofs {preset : Preset} {fork : Fork} (setup : TrustedSetup)
    (sidecar : DataColumnSidecar preset fork)
    (bidCommitments : Since .glamsterdam fork (BlobKZGCommitments preset fork)) :
    Except KzgError Bool :=
  -- Cell `j` of the column answers to commitment `j`, with proof `j`.
  --
  -- Every cell sits at the index of the column in the extended blob of its row.
  verifyCellKzgProofBatch setup ((sidecar.commitments bidCommitments).data.map (·.bytes))
    (Array.replicate sidecar.column.data.size sidecar.index.toNat) sidecar.column.data
    (sidecar.kzgProofs.data.map (·.bytes))

/-- From Gloas: the largest size of a serialized data column sidecar.

It is the size of a sidecar with a cell and a proof for each blob of the largest blob limit.

Heze keeps the sidecar of Gloas, so the size reads the layout of Gloas.

It is the largest 64-bit integer when the size does not fit. -/
def computeMaxDataColumnSidecarSize (preset : Preset) (config : Config) : UInt64 :=
  -- Let `m` be the largest blob limit, among that of Electra and those of the schedule.
  --
  -- The size is that of a sidecar with `m` cells and `m` proofs.
  --
  -- Only the cells and the proofs vary in size, so no sidecar is serialized.
  --
  -- The size adds their bytes to the fewest bytes of a sidecar, which gives the same number.
  --
  -- A size of `2^64` or more becomes `2^64 - 1`.
  UInt64.ofNat (min ((SszType.desc (DataColumnSidecar preset .glamsterdam)).minSize +
    config.largestBlobLimit.toNat * (Constants.BYTES_PER_CELL + Constants.BYTES_PER_PROOF))
    UINT64_MAX.toNat)

/-- Whether a branch climbs from a list of blob commitments to the root of a block body.

The branch has the depth of the inclusion proof, and the list sits at its place in the body. -/
def verifyKzgCommitmentsInclusionProof (preset : Preset) {fork : Fork}
    (commitments : BlobKZGCommitments preset fork)
    (branch : Vector Bytes32 preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat)
    (bodyRoot : Root) : Bool :=
  -- The leaf is the root of the list, at the generalized index of the list in the body.
  match blobKzgCommitmentsGindex preset fork, SszType.hashTreeRoot commitments with
  | .ok gindex, .ok leaf =>
    -- Its position is that index among the nodes of its level.
    match getSubtreeIndex gindex with
    | .ok index =>
      -- The branch climbs `KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH` levels from the leaf.
      --
      -- It ends at the body root.
      isValidMerkleBranch leaf branch.toList preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat
        index bodyRoot
    -- An index that names no node fails the check.
    | .error _ => false
  -- A generalized index or a root that cannot be computed fails the check.
  | _, _ => false

/-- Before Gloas: whether the branch of a sidecar climbs from its commitments to its body root. -/
def verifyDataColumnSidecarInclusionProof (preset : Preset) {fork : Fork}
    (beforeGloas : fork < .glamsterdam) (sidecar : DataColumnSidecar preset fork) : Bool :=
  -- Its commitments, its branch, and the body root of its header.
  verifyKzgCommitmentsInclusionProof preset (sidecar.kzgCommitments beforeGloas)
    (sidecar.kzgCommitmentsInclusionProof beforeGloas)
    (sidecar.signedBlockHeader beforeGloas).message.bodyRoot

/-- The largest number of column sidecars in one request: every column of the most blocks. -/
def computeMaxRequestDataColumnSidecars (preset : Preset) (config : Config) : UInt64 :=
  -- `MAX_REQUEST_BLOCKS_DENEB * NUMBER_OF_COLUMNS`.
  config.MAX_REQUEST_BLOCKS_DENEB * preset.NUMBER_OF_COLUMNS

/-- The entries of one row: each cell with its proof, in the order of the columns.

The row stops at the shorter of the two arrays; an extended blob gives 128 of each. -/
def matrixRow (row : RowIndex) (cells : Array Cell) (proofs : Array KZGProof) :
    List MatrixEntry :=
  -- Cell `i` and proof `i` form the entry of column `i` in the row.
  (cells.toList.zip proofs.toList).zipIdx.map fun ((cell, proof), column) =>
    ⟨cell, proof, column.toUInt64, row⟩

/-- The row of one blob: the cells and proofs of its extended blob. -/
def computeMatrixRow (setup : TrustedSetup) (blob : Blob) (row : Nat) :
    Except KzgError (List MatrixEntry) := do
  -- The cells and the proofs of the extended blob.
  let (cells, proofs) ← computeCellsAndKzgProofs setup blob
  -- Cell `i` and proof `i` form the entry of column `i` in the row.
  return matrixRow row.toUInt64 cells proofs

/-- The matrix of a list of blobs: the cells and proofs of each extended blob, row after row. -/
def computeMatrix (setup : TrustedSetup) (blobs : List Blob) :
    Except KzgError (List MatrixEntry) := do
  -- Blob `r` gives row `r`.
  let rows ← blobs.zipIdx.mapM fun (blob, row) => computeMatrixRow setup blob row
  -- The rows, one after another.
  return rows.flatten

/-- The full matrix of `count` rows, recovered from some of its entries.

The recovery of a row fails unless its entries name at least half of the columns, each once. -/
def recoverMatrix (setup : TrustedSetup) (partialMatrix : List MatrixEntry) (count : UInt64) :
    Except KzgError (List MatrixEntry) := do
  -- Each row `r < count` in turn.
  let rows ← (List.range count.toNat).mapM fun row => do
    -- The entries whose row is `r`, in their order.
    let entries := partialMatrix.filter (·.rowIndex = row.toUInt64)
    -- The cells and the proofs of the whole extended blob are recovered.
    --
    -- They come from the column index and the cell of each of those entries.
    let (cells, proofs) ← recoverCellsAndKzgProofs setup
      (entries.map (·.columnIndex.toNat)).toArray (entries.map (·.cell)).toArray
    -- Cell `i` and proof `i` form the entry of column `i` in row `r`.
    return matrixRow row.toUInt64 cells proofs
  -- The rows, one after another.
  return rows.flatten

/-- The column sidecars of a block, from the cells and the proofs of each of its blobs. -/
def getDataColumnSidecars (preset : Preset) {fork : Fork}
    (signedBlockHeader : Until .glamsterdam fork SignedBeaconBlockHeader)
    (kzgCommitments : Until .glamsterdam fork (BlobKZGCommitments preset fork))
    (kzgCommitmentsInclusionProof :
      Until .glamsterdam fork (Vector Bytes32 preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat))
    (beaconBlockRoot : Since .glamsterdam fork Root) (slot : Since .glamsterdam fork Slot)
    (cellsAndKzgProofs : List (Array Cell × Array KZGProof)) :
    Except Err (List (DataColumnSidecar preset fork)) := do
  -- Before Gloas, a count of rows other than the count of commitments is an error.
  if beforeGloas : fork < .glamsterdam then
    let count := (kzgCommitments beforeGloas).data.size
    if cellsAndKzgProofs.length ≠ count then throw (.count count cellsAndKzgProofs.length)
  -- With no rows there is no sidecar, since the check of a sidecar rejects one with no blob.
  if cellsAndKzgProofs.isEmpty then return []
  -- Sidecar `i` serves column `i`, for each `i < NUMBER_OF_COLUMNS`.
  (List.range preset.NUMBER_OF_COLUMNS.toNat).mapM fun column => do
    -- Cell `i` of every row, in the order of the blobs; a row without it is an error.
    let cells ← cellsAndKzgProofs.mapM fun (cells, _) =>
      match cells[column]? with
      | some cell => pure cell
      | none => throw (.count preset.NUMBER_OF_COLUMNS.toNat cells.size)
    -- Proof `i` of every row, in the order of the blobs; a row without it is an error.
    let proofs ← cellsAndKzgProofs.mapM fun (_, proofs) =>
      match proofs[column]? with
      | some proof => pure proof
      | none => throw (.count preset.NUMBER_OF_COLUMNS.toNat proofs.size)
    -- Before Gloas the column and its proofs are lists with a limit; from Gloas they have none.
    let limit := preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat
    if cellsBound : fork < .glamsterdam → cells.toArray.size ≤ limit then
      if proofsBound : fork < .glamsterdam → proofs.toArray.size ≤ limit then
        -- Before Gloas the sidecar carries the signed header, the commitments and their branch.
        --
        -- From Gloas it carries the slot and the root of the block, as EIP-7732 specifies.
        return ⟨column.toUInt64, ⟨cells.toArray, cellsBound⟩, kzgCommitments,
          ⟨proofs.toArray, proofsBound⟩, signedBlockHeader, kzgCommitmentsInclusionProof,
          slot, beaconBlockRoot⟩
    -- Before Gloas, more than `MAX_BLOB_COMMITMENTS_PER_BLOCK` cells or proofs is an error.
    throw (.count limit (max cells.length proofs.length))

/-- The branch from the list of blob commitments of a body up to its root, nearest node first. -/
def blobKzgCommitmentsInclusionProof {preset : Preset} {fork : Fork}
    (body : BeaconBlockBody preset fork) :
    Except Err (Vector Bytes32 preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat) := do
  -- The generalized index of the list of blob commitments.
  let gindex ← blobKzgCommitmentsGindex preset fork
  -- The sibling of each node on the path from that index up to the body root, bottom up.
  let nodes ← buildProof (SszType.desc (BeaconBlockBody preset fork)) (SszType.toValue body) gindex
  -- Each sibling is one 32-byte chunk.
  let nodes ← nodes.mapM toChunk
  -- Any count of siblings other than `KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH` is an error.
  Base.exactArray preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat nodes.toArray
    (.count preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat)

/-- The column sidecars of a signed block from Deneb's body on, with the cells of its blobs. -/
def getDataColumnSidecarsFromBlock {preset : Preset} {fork : Fork} (deneb : .dencun ≤ fork)
    (signed : SignedBeaconBlock preset fork)
    (cellsAndKzgProofs : List (Array Cell × Array KZGProof)) :
    Except Err (List (DataColumnSidecar preset fork)) := do
  -- Before Gloas, the signed header of the block, the commitments of its body and their branch.
  if beforeGloas : fork < .glamsterdam then
    let header ← signed.signedHeader
    let branch ← blobKzgCommitmentsInclusionProof signed.message.body
    let gloas := not_glamsterdam_le beforeGloas
    getDataColumnSidecars preset (fun _ => header)
      (fun _ => signed.message.body.blobKzgCommitments ⟨deneb, beforeGloas⟩) (fun _ => branch)
      (absurd · gloas) (absurd · gloas) cellsAndKzgProofs
  -- From Gloas, the root of the block and its slot.
  else
    let root ← SszType.hashTreeRoot signed.message
    getDataColumnSidecars preset (absurd · beforeGloas) (absurd · beforeGloas)
      (absurd · beforeGloas) (fun _ => root) (fun _ => signed.message.slot) cellsAndKzgProofs

/-- All the column sidecars of a block, from one of them and the cells of its blobs. -/
def getDataColumnSidecarsFromColumnSidecar {preset : Preset} {fork : Fork}
    (sidecar : DataColumnSidecar preset fork)
    (cellsAndKzgProofs : List (Array Cell × Array KZGProof)) :
    Except Err (List (DataColumnSidecar preset fork)) :=
  -- Before Gloas, the signed header, the commitments and the branch that the sidecar carries.
  --
  -- From Gloas, the root and the slot of the block that it carries.
  getDataColumnSidecars preset sidecar.signedBlockHeader sidecar.kzgCommitments
    sidecar.kzgCommitmentsInclusionProof sidecar.beaconBlockRoot sidecar.slot cellsAndKzgProofs

/-- One bit per blob of a block, for the cells of one column.

From Gloas the bitlist is progressive, as [EIP-7688] specifies.

[EIP-7688]: https://eips.ethereum.org/EIPS/eip-7688#specification -/
abbrev CellsBitList (preset : Preset) (fork : Fork) :=
  ForkBitlist .glamsterdam fork preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat

/-- At Fulu: what all the columns of a block share, to check their cells. -/
structure PartialDataColumnHeader (preset : Preset) (fork : Fork) where
  /-- The commitments to all the blobs of the block. -/
  kzgCommitments : BlobKZGCommitments preset fork
  /-- The header of the block, signed by its proposer. -/
  signedBlockHeader : SignedBeaconBlockHeader
  /-- The branch from the commitments up to the body root, nearest node first. -/
  kzgCommitmentsInclusionProof : Vector Bytes32 preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat
  deriving DecidableEq

instance {preset : Preset} {fork : Fork} : SszType (PartialDataColumnHeader preset fork) :=
  .container ["kzg_commitments", "signed_block_header", "kzg_commitments_inclusion_proof"]
    (fun h => (h.kzgCommitments, h.signedBlockHeader, h.kzgCommitmentsInclusionProof))
    (fun (kzgCommitments, signedBlockHeader, branch) => ⟨kzgCommitments, signedBlockHeader, branch⟩)

/-- From Fulu: some cells of one column, those that the bitmap marks, with their proofs.

The topic of the message names the column.

At Fulu a header comes along only on an eager push, as a list of at most one.

Gloas removes the header, since the bid of the block holds the commitments.

Gloas also makes the cells and the proofs progressive lists. -/
structure PartialDataColumnSidecar (preset : Preset) (fork : Fork) where
  /-- Bit `i` is set when the cell of blob `i` is present. -/
  cellsPresentBitmap : CellsBitList preset fork
  /-- The cells that are present, in the order of their blobs. -/
  partialColumn : ForkList .glamsterdam fork Cell preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat
  /-- The proof of each cell that is present. -/
  kzgProofs : ForkList .glamsterdam fork KZGProof preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat
  /-- Before Gloas: the header of the block, or nothing. -/
  header : Until .glamsterdam fork (SszList (PartialDataColumnHeader preset fork) 1)

namespace PartialDataColumnSidecar

/-- The names of the fields of a partial sidecar at a fork, in their order. -/
def names (fork : Fork) : List String :=
  ["cells_present_bitmap", "partial_column", "kzg_proofs"] ++
    untilNames .glamsterdam fork ["header"]

instance {preset : Preset} {fork : Fork} : SszType (PartialDataColumnSidecar preset fork) :=
  .container (names fork)
    (fun s => (s.cellsPresentBitmap, s.partialColumn, s.kzgProofs, s.header))
    (fun (bitmap, cells, proofs, header) => ⟨bitmap, cells, proofs, header⟩)

/-- The headers that a partial sidecar carries: at most one before Gloas, and none from Gloas. -/
def headers {preset : Preset} {fork : Fork} (sidecar : PartialDataColumnSidecar preset fork) :
    Array (PartialDataColumnHeader preset fork) :=
  -- Before Gloas, the list of at most one header, and from Gloas none.
  if before : fork < .glamsterdam then (sidecar.header before).data else #[]

end PartialDataColumnSidecar

/-- From Fulu: the cells that a peer has, and those that it asks for.

A peer that has a cell has its proof too. -/
structure PartialDataColumnPartsMetadata (preset : Preset) (fork : Fork) where
  /-- Bit `i` is set when the peer has the cell of blob `i` and will provide it. -/
  available : CellsBitList preset fork
  /-- Bit `i` is set when the peer wants the cell of blob `i`. -/
  requests : CellsBitList preset fork
  deriving DecidableEq

instance {preset : Preset} {fork : Fork} : SszType (PartialDataColumnPartsMetadata preset fork) :=
  .container ["available", "requests"] (fun m => (m.available, m.requests))
    (fun (available, requests) => ⟨available, requests⟩)

/-- From Fulu: the group of the partial messages of one block, named by the root of the block.

Gloas adds the slot of the block. -/
structure PartialDataColumnGroupID (fork : Fork) where
  /-- The root of the block. -/
  beaconBlockRoot : Root
  /-- From Gloas: the slot of the block. -/
  slot : Since .glamsterdam fork Slot

namespace PartialDataColumnGroupID

/-- The names of the fields of a group at a fork, in their order. -/
def names (fork : Fork) : List String :=
  ["beacon_block_root"] ++ sinceNames .glamsterdam fork ["slot"]

instance {fork : Fork} : SszType (PartialDataColumnGroupID fork) :=
  .container (names fork) (fun g => (g.beaconBlockRoot, g.slot))
    (fun (beaconBlockRoot, slot) => ⟨beaconBlockRoot, slot⟩)

/-- The version byte of a gossip group ID at a fork: 0 before Gloas, and 1 from Gloas. -/
def version (fork : Fork) : UInt8 :=
  if fork < .glamsterdam then 0 else 1

/-- The gossip group ID of a group: the version byte of the fork, then the SSZ bytes. -/
def toGroupId {fork : Fork} (group : PartialDataColumnGroupID fork) : Except Err ByteArray := do
  return ByteArray.mk #[version fork] ++ (← SszType.serialize group)

/-- The group that a gossip group ID names.

An ID whose first byte is not the version of the fork names no group, as it is ignored.

Nor does an ID whose remaining bytes are not the SSZ bytes of a group. -/
def ofGroupId (fork : Fork) (bytes : ByteArray) : Option (PartialDataColumnGroupID fork) :=
  -- The first byte is the version of the fork.
  if bytes.data[0]? = some (version fork) then
    -- The group is the SSZ decoding of the remaining bytes, if they decode.
    (SszType.deserialize (PartialDataColumnGroupID fork) (bytes.extract 1 bytes.size)).toOption
  -- An empty ID or another version names no group.
  else none

end PartialDataColumnGroupID

/-- Whether the branch of a header climbs from its commitments to its body root. -/
def verifyPartialDataColumnHeaderInclusionProof (preset : Preset) {fork : Fork}
    (header : PartialDataColumnHeader preset fork) : Bool :=
  -- The commitments of the header, its branch, and the body root of its signed header.
  verifyKzgCommitmentsInclusionProof preset header.kzgCommitments
    header.kzgCommitmentsInclusionProof header.signedBlockHeader.message.bodyRoot

/-- The indices of the blobs whose cells a partial sidecar carries, in order. -/
def PartialDataColumnSidecar.blobIndices {preset : Preset} {fork : Fork}
    (sidecar : PartialDataColumnSidecar preset fork) : Array Nat :=
  -- The positions `i` whose bit is set, in increasing order.
  (sidecar.cellsPresentBitmap.bits.zipIdx.filter (·.1)).map (·.2)

/-- Whether the cells of a partial sidecar match the commitments of their blobs, by their proofs.

A set bit with no commitment fails with an error, and so do unequal counts. -/
def verifyPartialDataColumnSidecarKzgProofs {preset : Preset} {fork : Fork}
    (setup : TrustedSetup) (sidecar : PartialDataColumnSidecar preset fork)
    (allCommitments : BlobKZGCommitments preset fork) (columnIndex : ColumnIndex) :
    Except KzgError Bool := do
  -- The indices of the blobs whose bit is set, in increasing order.
  let indices := sidecar.blobIndices
  -- The commitment of each of those blobs.
  let commitments ← indices.mapM fun index =>
    if inside : index < allCommitments.data.size then pure allCommitments.data[index]
    else throw (.commitmentIndexOutOfBounds index allCommitments.data.size)
  -- The `j`-th cell present answers to the commitment of the `j`-th set bit, with proof `j`.
  --
  -- Every cell sits at the index of the column in the extended blob of its row.
  verifyCellKzgProofBatch setup (commitments.map (·.bytes))
    (Array.replicate indices.size columnIndex.toNat)
    sidecar.partialColumn.data (sidecar.kzgProofs.data.map (·.bytes))

end EthLib.Consensus
