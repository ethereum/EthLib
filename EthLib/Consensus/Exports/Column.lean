module

public import EthLib.Consensus.DataAvailability.Column
public import EthLib.Consensus.Exports.Ssz
public import EthLib.Cryptography.Exports.Kzg

/-!
# `Exports.Column`

C-ABI exports of the data column sidecars and of the matrix of cells, from Fulu.

A sidecar, a block and a matrix entry arrive in their SSZ encoding.

From Gloas a sidecar names its block by root, and the checks read the commitments of its bid.

So the checks of a sidecar take the bytes of its signed block too, which are empty before Gloas.

Blobs, entries and rows of cells arrive one after another in one byte string.

A row of cells holds the 128 cells of an extended blob, then their 128 proofs.

A list of sidecars comes back in the SSZ encoding of a list.

An input that the export reads itself, such as a wrong length, has code 0.
-/

public section

namespace EthLib.Consensus.Exports

open EthLib.Exports (Result)
open Base Cryptography.Kzg Cryptography.Kzg.Constants Serialization.Ssz
open Cryptography.Kzg.Exports (runKzgWithSetup)
open Serialization.Ssz.Exports (runSsz)

/-- The pieces of `n` bytes that make up the bytes, in order, or none if they do not divide. -/
def pieces (n : Nat) (bytes : ByteArray) : Option (Array (Vector UInt8 n)) :=
  if n = 0 ∨ bytes.size % n ≠ 0 then none
  else (Array.range (bytes.size / n)).mapM fun i =>
    let piece := bytes.extract (i * n) ((i + 1) * n)
    if h : piece.size = n then some ⟨piece.data, h⟩ else none

/-- The preset and a fork from Fulu on, which the names name. -/
def columnPresetAndFork (name fork : ByteArray) : Result (Preset × Fork) := do
  let preset ← presetOf (← nameOf name)
  let fork ← forkOf fork
  if fork < .fusaka then throw (0, s!"no data column sidecar at {fork.name}")
  return (preset, fork)

/-- The preset and a fork from Fulu up to Gloas, which the names name, with the fork's bound. -/
def fuluPresetAndFork (name fork : ByteArray) :
    Result (Preset × (fork : Fork) ×' fork < .glamsterdam) := do
  let (preset, fork) ← columnPresetAndFork name fork
  if beforeGloas : fork < .glamsterdam then return (preset, ⟨fork, beforeGloas⟩)
  else throw (0, s!"no form of this check at {fork.name}")

/-- Read a sidecar, with the code of a decoding error. -/
def readSidecar (preset : Preset) (fork : Fork) (data : ByteArray) :
    Result (DataColumnSidecar preset fork) :=
  runSsz "input rejected" (SszType.deserialize (DataColumnSidecar preset fork) data)

/-- From Gloas, the commitments in the bid of the block of a sidecar, from the signed block.

Before Gloas the sidecar carries its commitments, so the block must be empty.

From Gloas a block whose root is not the root that the sidecar names fails with code 0. -/
def bidCommitmentsOf {preset : Preset} {fork : Fork} (sidecar : DataColumnSidecar preset fork)
    (block : ByteArray) : Result (Since .glamsterdam fork (BlobKZGCommitments preset fork)) := do
  if beforeGloas : fork < .glamsterdam then
    if !block.isEmpty then throw (0, s!"no block for a sidecar at {fork.name}")
    return (absurd · (not_glamsterdam_le beforeGloas))
  else
    let gloas := not_lt_glamsterdam beforeGloas
    let signed ← runSsz "block rejected"
      (SszType.deserialize (SignedBeaconBlock preset fork) block)
    let root ← runSsz "block rejected" (SszType.hashTreeRoot signed.message)
    if root ≠ sidecar.beaconBlockRoot gloas then
      throw (0, "the block is not the block of the sidecar")
    return signed.message.bidCommitments

/-- Whether a sidecar, given as bytes, has a valid shape.

Before Gloas the count of its commitments stays within the blob limit of its epoch.

The configuration of the name holds, with the replacements that the JSON object gives. -/
@[export eth_consensus_verify_data_column_sidecar]
def verifyDataColumnSidecarExport (name fork data block replacements : ByteArray) :
    Result Bool := do
  let (preset, fork) ← columnPresetAndFork name fork
  let config ← configWith name replacements
  let sidecar ← readSidecar preset fork data
  return verifyDataColumnSidecar preset config sidecar (← bidCommitmentsOf sidecar block)

/-- Whether the branch of a sidecar, given as bytes, climbs to the body root of its header. -/
@[export eth_consensus_verify_data_column_sidecar_inclusion_proof]
def verifyDataColumnSidecarInclusionProofExport (name fork data : ByteArray) : Result Bool := do
  let (preset, ⟨fork, beforeGloas⟩) ← fuluPresetAndFork name fork
  return verifyDataColumnSidecarInclusionProof preset beforeGloas (← readSidecar preset fork data)

/-- Whether the cells of a sidecar, given as bytes, match its commitments by their proofs.

From Gloas the commitments come from the bid of the signed block.

A sidecar or a block that does not decode has code 0. -/
@[export eth_consensus_verify_data_column_sidecar_kzg_proofs]
def verifyDataColumnSidecarKzgProofsExport (name fork data block : ByteArray) : Result Bool := do
  let (preset, fork) ← columnPresetAndFork name fork
  let sidecar ← (SszType.deserialize (DataColumnSidecar preset fork) data).mapError
    fun e => (0, s!"input rejected: {reprStr e}")
  let commitments ← (bidCommitmentsOf sidecar block).mapError fun (_, message) => (0, message)
  runKzgWithSetup fun setup => verifyDataColumnSidecarKzgProofs setup sidecar commitments

/-- At Fulu: whether the branch of a partial header, given as bytes, climbs to its body root. -/
@[export eth_consensus_verify_partial_data_column_header_inclusion_proof]
def verifyPartialDataColumnHeaderInclusionProofExport (name fork data : ByteArray) :
    Result Bool := do
  let (preset, ⟨fork, _⟩) ← fuluPresetAndFork name fork
  let header ← runSsz "input rejected"
    (SszType.deserialize (PartialDataColumnHeader preset fork) data)
  return verifyPartialDataColumnHeaderInclusionProof preset header

/-- At Fulu: whether the cells of a partial sidecar match their commitments by their proofs.

The commitments of all the blobs of the block arrive in their SSZ encoding.

A sidecar or a list of commitments that does not decode has code 0. -/
@[export eth_consensus_verify_partial_data_column_sidecar_kzg_proofs]
def verifyPartialDataColumnSidecarKzgProofsExport (name fork data commitments : ByteArray)
    (columnIndex : UInt64) : Result Bool := do
  let (preset, ⟨fork, _⟩) ← fuluPresetAndFork name fork
  let sidecar ← (SszType.deserialize (PartialDataColumnSidecar preset fork) data).mapError
    fun e => (0, s!"input rejected: {reprStr e}")
  let commitments ← (SszType.deserialize (BlobKZGCommitments preset fork) commitments).mapError
    fun e => (0, s!"commitments rejected: {reprStr e}")
  runKzgWithSetup fun setup =>
    verifyPartialDataColumnSidecarKzgProofs setup sidecar commitments columnIndex

/-- The bytes of the entries of a matrix, one after another. -/
def matrixBytes (entries : List MatrixEntry) : Result ByteArray :=
  entries.foldlM (fun bytes entry => return bytes ++ (← runSsz "entry rejected"
    (SszType.serialize entry))) ByteArray.empty

/-- The matrix of the blobs, given one after another, as its entries one after another. -/
@[export eth_consensus_compute_matrix]
def computeMatrixExport (blobs : ByteArray) : Result ByteArray := do
  let some blobs := pieces BYTES_PER_BLOB blobs | throw (0, "blobs have a wrong length")
  matrixBytes (← runKzgWithSetup fun setup => computeMatrix setup blobs.toList)

/-- The bytes of one matrix entry: a cell, a proof, a column and a row. -/
def MATRIX_ENTRY_BYTES : Nat := BYTES_PER_CELL + BYTES_PER_PROOF + 8 + 8

/-- The full matrix of `count` rows, from some entries given one after another. -/
@[export eth_consensus_recover_matrix]
def recoverMatrixExport (entries : ByteArray) (count : UInt64) : Result ByteArray := do
  let some pieces := pieces MATRIX_ENTRY_BYTES entries
    | throw (0, "entries have a wrong length")
  let entries ← pieces.toList.mapM fun piece =>
    runSsz "entry rejected" (SszType.deserialize MatrixEntry ⟨piece.toArray⟩)
  matrixBytes (← runKzgWithSetup fun setup => recoverMatrix setup entries count)

/-- The rows of cells and proofs, given one after another. -/
def readRows (rows : ByteArray) : Result (List (Array Cell × Array KZGProof)) := do
  let width := CELLS_PER_EXT_BLOB * (BYTES_PER_CELL + BYTES_PER_PROOF)
  let some rows := pieces width rows | throw (0, "rows have a wrong length")
  rows.toList.mapM fun row => do
    let bytes : ByteArray := ⟨row.toArray⟩
    let cellBytes := CELLS_PER_EXT_BLOB * BYTES_PER_CELL
    let some cells := pieces BYTES_PER_CELL (bytes.extract 0 cellBytes)
      | throw (0, "a row does not split into cells")
    let some proofs := pieces BYTES_PER_PROOF (bytes.extract cellBytes width)
      | throw (0, "a row does not split into proofs")
    return (cells, proofs)

/-- The bytes of a list of sidecars, in the SSZ encoding of a list. -/
def sidecarsBytes {preset : Preset} {fork : Fork}
    (sidecars : List (DataColumnSidecar preset fork)) :
    Result ByteArray := do
  if bound : sidecars.toArray.size ≤ preset.NUMBER_OF_COLUMNS.toNat then
    runSsz "sidecars rejected"
      (SszType.serialize (⟨sidecars.toArray, bound⟩ :
        SszList (DataColumnSidecar preset fork) preset.NUMBER_OF_COLUMNS.toNat))
  else throw (0, "too many sidecars")

/-- The column sidecars of a signed block, from its bytes and the rows of its blobs. -/
@[export eth_consensus_get_data_column_sidecars_from_block]
def getDataColumnSidecarsFromBlockExport (name fork block rows : ByteArray) :
    Result ByteArray := do
  let (preset, fork) ← columnPresetAndFork name fork
  let signed ← runSsz "input rejected"
    (SszType.deserialize (SignedBeaconBlock preset fork) block)
  if deneb : .dencun ≤ fork then
    sidecarsBytes (← runSsz "sidecars rejected"
      (getDataColumnSidecarsFromBlock deneb signed (← readRows rows)))
  else throw (0, s!"no blobs at {fork.name}")

/-- All the column sidecars of a block, from the bytes of one of them and the rows of its blobs. -/
@[export eth_consensus_get_data_column_sidecars_from_column_sidecar]
def getDataColumnSidecarsFromColumnSidecarExport (name fork sidecar rows : ByteArray) :
    Result ByteArray := do
  let (preset, fork) ← columnPresetAndFork name fork
  sidecarsBytes (← runSsz "sidecars rejected"
    (getDataColumnSidecarsFromColumnSidecar (← readSidecar preset fork sidecar) (← readRows rows)))

end EthLib.Consensus.Exports
