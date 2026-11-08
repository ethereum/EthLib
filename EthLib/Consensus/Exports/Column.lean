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

The exports of the matrix, of the lists of sidecars and of the shape check take typed values.

A blob, a matrix entry and a sidecar each cross as bytes, in a list.

A row holds the 128 cells of an extended blob and their 128 proofs, as a pair of lists.

An input that the export reads itself, such as a wrong length, has code 0.
-/

public section

namespace EthLib.Consensus.Exports

open EthLib.Exports (Result PyValue pyExport)
open Base Cryptography.Kzg Cryptography.Kzg.Constants Serialization.Ssz
open Cryptography.Kzg.Exports (runKzgWithSetup)
open Serialization.Ssz.Exports (runSsz)

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

The configuration of the name holds, with the replacements that a `dict` gives. -/
def verifyDataColumnSidecarOf
    (args : String × String × ByteArray × ByteArray × Option PyValue) : Result Bool := do
  let (name, fork, data, block, replacements) := args
  let (preset, fork) ← columnPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let sidecar ← readSidecar preset fork data
  return verifyDataColumnSidecar preset config sidecar (← bidCommitmentsOf sidecar block)

/-- Whether a sidecar, given as bytes, has a valid shape.

The arguments are the name of the preset and the configuration, the fork and the sidecar.

Then come the signed block, empty before Gloas, and replacements of values of the configuration.
-/
@[export eth_consensus_verify_data_column_sidecar]
def verifyDataColumnSidecarExport (args : PyValue) : Result PyValue :=
  pyExport verifyDataColumnSidecarOf args

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

/-- The SSZ bytes of each value of a list. -/
def encodeEach {α : Type} [SszType α] (what : String) (values : List α) :
    Result (List ByteArray) :=
  values.mapM fun value => runSsz s!"{what} rejected" (SszType.serialize value)

/-- The matrix of the blobs, as the SSZ bytes of each of its entries. -/
def computeMatrixOf (blobs : List Blob) : Result (List ByteArray) := do
  encodeEach "entry" (← runKzgWithSetup fun setup => computeMatrix setup blobs)

/-- The matrix of the blobs, as the SSZ bytes of each of its entries, in a list.

The argument is the list of the blobs. -/
@[export eth_consensus_compute_matrix]
def computeMatrixExport (args : PyValue) : Result PyValue := pyExport computeMatrixOf args

/-- The bytes of one matrix entry: a cell, a proof, a column and a row. -/
def MATRIX_ENTRY_BYTES : Nat := BYTES_PER_CELL + BYTES_PER_PROOF + 8 + 8

/-- The full matrix of a count of rows, from the SSZ bytes of some of its entries.

Every entry of the right length decodes, so an entry fails only on its length, with code 0. -/
def recoverMatrixOf (args : List (Vector UInt8 MATRIX_ENTRY_BYTES) × UInt64) :
    Result (List ByteArray) := do
  let (entries, count) := args
  let entries ← entries.mapM fun entry =>
    (SszType.deserialize MatrixEntry ⟨entry.toArray⟩).mapError
      fun e => (0, s!"entry rejected: {reprStr e}")
  encodeEach "entry" (← runKzgWithSetup fun setup => recoverMatrix setup entries count)

/-- The full matrix of a count of rows, from the SSZ bytes of some of its entries, in a list.

The arguments are the list of the entries, of 2112 bytes each, and the count of rows. -/
@[export eth_consensus_recover_matrix]
def recoverMatrixExport (args : PyValue) : Result PyValue := pyExport recoverMatrixOf args

/-- The rows of cells and proofs, each with the cells and the proofs of an extended blob.

A row with another count of cells or of proofs has code 0. -/
def checkRows (rows : List (Array Cell × Array KZGProof)) :
    Result (List (Array Cell × Array KZGProof)) := do
  for (cells, proofs) in rows do
    unless cells.size = CELLS_PER_EXT_BLOB ∧ proofs.size = CELLS_PER_EXT_BLOB do
      throw (0, s!"a row holds {cells.size} cells and {proofs.size} proofs, \
        not {CELLS_PER_EXT_BLOB} of each")
  return rows

/-- The column sidecars of a signed block, from its bytes and the rows of its blobs. -/
def getDataColumnSidecarsFromBlockOf
    (args : String × String × ByteArray × List (Array Cell × Array KZGProof)) :
    Result (List ByteArray) := do
  let (name, fork, block, rows) := args
  let (preset, fork) ← columnPresetAndFork name.toUTF8 fork.toUTF8
  let signed ← runSsz "input rejected"
    (SszType.deserialize (SignedBeaconBlock preset fork) block)
  if deneb : .dencun ≤ fork then
    encodeEach "sidecar" (← runSsz "sidecars rejected"
      (getDataColumnSidecarsFromBlock deneb signed (← checkRows rows)))
  else throw (0, s!"no blobs at {fork.name}")

/-- The column sidecars of a signed block, as the SSZ bytes of each, in a list.

The arguments are the name of the preset, the fork, the signed block and the rows of its blobs. -/
@[export eth_consensus_get_data_column_sidecars_from_block]
def getDataColumnSidecarsFromBlockExport (args : PyValue) : Result PyValue :=
  pyExport getDataColumnSidecarsFromBlockOf args

/-- All the column sidecars of a block, from the bytes of one of them and the rows of its blobs. -/
def getDataColumnSidecarsFromColumnSidecarOf
    (args : String × String × ByteArray × List (Array Cell × Array KZGProof)) :
    Result (List ByteArray) := do
  let (name, fork, sidecar, rows) := args
  let (preset, fork) ← columnPresetAndFork name.toUTF8 fork.toUTF8
  encodeEach "sidecar" (← runSsz "sidecars rejected"
    (getDataColumnSidecarsFromColumnSidecar (← readSidecar preset fork sidecar) (← checkRows rows)))

/-- All the column sidecars of a block, as the SSZ bytes of each, in a list.

The arguments are the name of the preset, the fork, the bytes of one sidecar and the rows. -/
@[export eth_consensus_get_data_column_sidecars_from_column_sidecar]
def getDataColumnSidecarsFromColumnSidecarExport (args : PyValue) : Result PyValue :=
  pyExport getDataColumnSidecarsFromColumnSidecarOf args

end EthLib.Consensus.Exports
