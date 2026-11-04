module

public import EthLib.Cryptography.Bls
public import EthLib.Cryptography.Kzg.Constants
public import EthLib.Cryptography.Kzg.Polynomials
public import EthLib.Cryptography.Kzg.Core
public import EthLib.Cryptography.Kzg.Cells
public import EthLib.Cryptography.Kzg.Recovery
public import EthLib.Cryptography.Kzg.TrustedSetup
public import EthLib.Cryptography.Kzg.Errors

/-!
# `Exports.Kzg`

C-ABI exports for the Python bindings.

Each export is a C symbol that takes and returns Lean runtime objects.

The CPython extension under `bindings/python/` calls them on converted Python values.

The loader must initialize the Lean runtime before the first call.

Each input is a `ByteArray` or an `Array`.

A single output is a `ByteArray`, and several outputs are arrays of them, or pairs.

Booleans come back as `UInt8`.
-/

public section

namespace EthLib.Cryptography.Kzg.Exports

open EthLib.Cryptography.Kzg
open EthLib.Base (Bytes32)
open EthLib.Cryptography.Kzg.Constants

/-- Run a KZG computation in `IO`.

An error becomes the `IO` error that the C extension raises to the caller. -/
def runKzg {α : Type} (act : Except KzgError α) : IO α :=
  match act with
  | .ok a    => pure a
  | .error e => throw (IO.userError e.message)

/-- The embedded trusted setup, decoded.

A constant of compiled Lean is evaluated once, when its module is initialized.

So the 8257 points are decoded once, and every export reuses them. -/
def embeddedSetup : Except KzgError TrustedSetup := TrustedSetup.ofHex

/-- Run a KZG computation that reads the embedded trusted setup. -/
def runKzgWithSetup {α : Type} (act : TrustedSetup → Except KzgError α) : IO α :=
  runKzg (embeddedSetup >>= act)

/-! ## Parsing

Each input arrives as untyped bytes and is read once into its fixed-length type.

A wrong length is rejected here with its size error, before the operation runs. -/

/-- Read a blob. -/
def parseBlob : ByteArray → Except KzgError Blob := parseBytes BYTES_PER_BLOB .badBlobSize

/-- Read a commitment. -/
def parseCommitment : ByteArray → Except KzgError KZGCommitment :=
  parseBytes BYTES_PER_COMMITMENT .badCommitmentSize

/-- Read a proof. -/
def parseProof : ByteArray → Except KzgError KZGProof := parseBytes BYTES_PER_PROOF .badProofSize

/-- Read a field element. -/
def parseFieldElement : ByteArray → Except KzgError Bytes32 :=
  parseBytes BYTES_PER_FIELD_ELEMENT .badFieldElementSize

/-- Read a cell. -/
def parseCell : ByteArray → Except KzgError Cell := parseBytes BYTES_PER_CELL .badCellSize

/-- A byte vector as untyped bytes. -/
def unparse {n : Nat} (v : Vector UInt8 n) : ByteArray := ⟨v.toArray⟩

/-! ## Sizes

The Python C extension reads every size through these when its module loads.

So the binding fixes no constant of its own.

Each accessor takes a unit argument and ignores it, so its C signature is fixed.
-/

@[export eth_kzg_const_bytes_per_field_element]
def constBytesPerFieldElement (_ : Unit) : UInt64 :=
  UInt64.ofNat BYTES_PER_FIELD_ELEMENT

@[export eth_kzg_const_bytes_per_commitment]
def constBytesPerCommitment (_ : Unit) : UInt64 :=
  UInt64.ofNat BYTES_PER_COMMITMENT

@[export eth_kzg_const_bytes_per_proof]
def constBytesPerProof (_ : Unit) : UInt64 :=
  UInt64.ofNat BYTES_PER_PROOF

@[export eth_kzg_const_field_elements_per_blob]
def constFieldElementsPerBlob (_ : Unit) : UInt64 :=
  UInt64.ofNat FIELD_ELEMENTS_PER_BLOB

@[export eth_kzg_const_bytes_per_blob]
def constBytesPerBlob (_ : Unit) : UInt64 :=
  UInt64.ofNat BYTES_PER_BLOB

@[export eth_kzg_const_field_elements_per_cell]
def constFieldElementsPerCell (_ : Unit) : UInt64 :=
  UInt64.ofNat FIELD_ELEMENTS_PER_CELL

@[export eth_kzg_const_bytes_per_cell]
def constBytesPerCell (_ : Unit) : UInt64 :=
  UInt64.ofNat BYTES_PER_CELL

@[export eth_kzg_const_cells_per_ext_blob]
def constCellsPerExtBlob (_ : Unit) : UInt64 :=
  UInt64.ofNat CELLS_PER_EXT_BLOB

/-! ## Operations -/

@[export eth_kzg_blob_to_kzg_commitment]
def blobToKzgCommitmentExport (blob : ByteArray) : IO ByteArray :=
  unparse <$> runKzgWithSetup fun setup => do blobToKzgCommitment setup (← parseBlob blob)

@[export eth_kzg_compute_challenge]
def computeChallengeExport
    (blob : ByteArray) (commitment : ByteArray) : IO ByteArray :=
  runKzg do
    let blob ← parseBlob blob
    let commitment ← parseCommitment commitment
    let _ ← blobToPolynomial blob
    let commitment ← bytesToKzgCommitment commitment
    return unparse (blsFieldToBytes (computeChallenge blob commitment))

/-- An 80-byte buffer: the 48-byte proof, then the 32 bytes of `y`. -/
@[export eth_kzg_compute_kzg_proof]
def computeKzgProofExport
    (blob : ByteArray) (z : ByteArray) : IO ByteArray := do
  let (proof, y) ← runKzgWithSetup fun setup => do
    computeKzgProof setup (← parseBlob blob) (← parseFieldElement z)
  return unparse proof ++ unparse y

@[export eth_kzg_verify_kzg_proof]
def verifyKzgProofExport
    (commitment : ByteArray) (z : ByteArray)
    (y : ByteArray) (proof : ByteArray) : IO UInt8 := do
  let ok ← runKzgWithSetup fun setup => do
    verifyKzgProof setup (← parseCommitment commitment) (← parseFieldElement z)
      (← parseFieldElement y) (← parseProof proof)
  return if ok then 1 else 0

@[export eth_kzg_compute_blob_kzg_proof]
def computeBlobKzgProofExport
    (blob : ByteArray) (commitment : ByteArray) : IO ByteArray :=
  unparse <$> runKzgWithSetup fun setup => do
    computeBlobKzgProof setup (← parseBlob blob) (← parseCommitment commitment)

@[export eth_kzg_verify_blob_kzg_proof]
def verifyBlobKzgProofExport
    (blob : ByteArray) (commitment : ByteArray) (proof : ByteArray)
    : IO UInt8 := do
  let ok ← runKzgWithSetup fun setup => do
    verifyBlobKzgProof setup (← parseBlob blob) (← parseCommitment commitment) (← parseProof proof)
  return if ok then 1 else 0

@[export eth_kzg_verify_blob_kzg_proof_batch]
def verifyBlobKzgProofBatchExport
    (blobs : Array ByteArray)
    (commitments : Array ByteArray)
    (proofs : Array ByteArray) : IO UInt8 := do
  let ok ← runKzgWithSetup fun setup => do
    verifyBlobKzgProofBatch setup (← blobs.mapM parseBlob) (← commitments.mapM parseCommitment)
      (← proofs.mapM parseProof)
  return if ok then 1 else 0

@[export eth_kzg_compute_cells]
def computeCellsExport (blob : ByteArray) : IO ByteArray := do
  let cells ← runKzg do computeCells (← parseBlob blob)
  return cells.foldl (· ++ unparse ·) ByteArray.empty

@[export eth_kzg_compute_verify_cell_kzg_proof_batch_challenge]
def computeVerifyCellKzgProofBatchChallengeExport
    (commitments : Array ByteArray)
    (commitmentIndicesBE : ByteArray)
    (cellIndicesBE : ByteArray)
    (cosetsEvals : Array ByteArray)
    (proofs : Array ByteArray) : IO ByteArray :=
  runKzg do
    let commitmentIndices ← unpackIndicesBE commitmentIndicesBE
    let cellIndices       ← unpackIndicesBE cellIndicesBE
    if cellIndices.size ≠ commitmentIndices.size then
      throw (.inputLengthMismatch "cellIndices" commitmentIndices.size cellIndices.size)
    if cosetsEvals.size ≠ commitmentIndices.size then
      throw (.inputLengthMismatch "cosetsEvals" commitmentIndices.size cosetsEvals.size)
    if proofs.size ≠ commitmentIndices.size then
      throw (.inputLengthMismatch "proofs" commitmentIndices.size proofs.size)
    let commitments ← commitments.mapM parseCommitment
    for i in [:commitments.size] do
      match bytesToKzgCommitment commitments[i]! with
      | .ok _    => pure ()
      | .error _ => throw (.invalidCommitment (some i))
    if commitmentIndices.any (· ≥ commitments.size) then
      throw .commitmentIndexOutOfBounds
    if cellIndices.any (· ≥ Constants.CELLS_PER_EXT_BLOB) then
      throw .cellIndexOutOfBounds
    let proofs ← proofs.mapM parseProof
    for i in [:proofs.size] do
      match bytesToKzgProof proofs[i]! with
      | .ok _    => pure ()
      | .error _ => throw (.invalidProof (some i))
    let evals : Array CosetEvals ← cosetsEvals.mapM fun ce => do
      cellToCosetEvals (← parseCell ce)
    return unparse <| blsFieldToBytes
      (computeVerifyCellKzgProofBatchChallenge
        commitments commitmentIndices cellIndices evals proofs)

@[export eth_kzg_compute_cells_and_kzg_proofs]
def computeCellsAndKzgProofsExport (blob : ByteArray) : IO ByteArray := do
  let (cells, proofs) ← runKzgWithSetup fun setup => do
    computeCellsAndKzgProofs setup (← parseBlob blob)
  let cellsBuf  := cells.foldl  (· ++ unparse ·) ByteArray.empty
  let proofsBuf := proofs.foldl (· ++ unparse ·) ByteArray.empty
  return cellsBuf ++ proofsBuf

@[export eth_kzg_verify_cell_kzg_proof_batch]
def verifyCellKzgProofBatchExport
    (commitments : Array ByteArray)
    (cellIndicesBE : ByteArray)
    (cells : Array ByteArray)
    (proofs : Array ByteArray) : IO UInt8 := do
  let ok ← runKzgWithSetup fun setup => do
    let cellIndices ← unpackIndicesBE cellIndicesBE
    verifyCellKzgProofBatch setup (← commitments.mapM parseCommitment) cellIndices
      (← cells.mapM parseCell) (← proofs.mapM parseProof)
  return if ok then 1 else 0

@[export eth_kzg_recover_cells_and_kzg_proofs]
def recoverCellsAndKzgProofsExport
    (cellIndicesBE : ByteArray) (cells : Array ByteArray) : IO ByteArray := do
  let (cells', proofs') ← runKzgWithSetup fun setup => do
    let cellIndices ← unpackIndicesBE cellIndicesBE
    recoverCellsAndKzgProofs setup cellIndices (← cells.mapM parseCell)
  let cellsBuf  := cells'.foldl  (· ++ unparse ·) ByteArray.empty
  let proofsBuf := proofs'.foldl (· ++ unparse ·) ByteArray.empty
  return cellsBuf ++ proofsBuf

end EthLib.Cryptography.Kzg.Exports
