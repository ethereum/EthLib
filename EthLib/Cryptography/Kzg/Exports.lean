import EthLib.Cryptography.Bls
import EthLib.Cryptography.Kzg.Constants
import EthLib.Cryptography.Kzg.Polynomials
import EthLib.Cryptography.Kzg.Core
import EthLib.Cryptography.Kzg.Cells
import EthLib.Cryptography.Kzg.Recovery
import EthLib.Cryptography.Kzg.TrustedSetup
import EthLib.Cryptography.Kzg.Errors

/-!
# `Exports`

C-ABI exports for the Python bindings.

Lean's `@[export]` attribute generates a C symbol with the given name
that takes Lean-runtime objects (`lean_object*`) and returns one. The
CPython extension under `bindings/python/` calls these symbols directly
after marshalling Python values into `ByteArray`s and `Array`s.

Two notes:

* `lean_initialize_runtime_module()` must be called by the loader
  before any of these are invoked. The Python wrapper does this in its
  `PyInit_*` function.

* All inputs are `ByteArray` or `Array X`. We return `ByteArray` for
  single outputs, `Array ByteArray` (or pairs thereof) for multi-output
  public methods. Booleans are returned as `UInt8`.
-/

namespace EthLib.Cryptography.Kzg.Exports

open EthLib.Cryptography.Kzg

/-- Decode a packed buffer of big-endian `UInt64` indices into an
`Array Nat`. The Python wrapper passes index arrays this way (8 bytes
per entry) so we can keep the C ABI to plain `ByteArray`s. -/
private def unpackIndicesBE (b : ByteArray) : Array Nat := Id.run do
  let n := b.size / 8
  let mut out : Array Nat := Array.mkEmpty n
  for i in [:n] do
    out := out.push (bytesBEToNat (b.extract (i*8) ((i+1)*8)))
  return out

@[export eth_kzg_blob_to_kzg_commitment]
def blobToKzgCommitmentExport (blob : @& ByteArray) : IO ByteArray :=
  runKzg (blobToKzgCommitment blob)

@[export eth_kzg_compute_challenge]
def computeChallengeExport
    (blob : @& ByteArray) (commitment : @& ByteArray) : IO ByteArray := do
  pure <| blsFieldToBytes (computeChallenge blob commitment)

/-- Returns a 80-byte buffer: 48-byte proof followed by 32-byte y. -/
@[export eth_kzg_compute_kzg_proof]
def computeKzgProofExport
    (blob : @& ByteArray) (z : @& ByteArray) : IO ByteArray := do
  let (proof, y) ← runKzg (computeKzgProof blob z)
  return proof ++ y

@[export eth_kzg_verify_kzg_proof]
def verifyKzgProofExport
    (commitment : @& ByteArray) (z : @& ByteArray)
    (y : @& ByteArray) (proof : @& ByteArray) : IO UInt8 := do
  let ok ← runKzg (verifyKzgProof commitment z y proof)
  return if ok then 1 else 0

@[export eth_kzg_compute_blob_kzg_proof]
def computeBlobKzgProofExport
    (blob : @& ByteArray) (commitment : @& ByteArray) : IO ByteArray :=
  runKzg (computeBlobKzgProof blob commitment)

@[export eth_kzg_verify_blob_kzg_proof]
def verifyBlobKzgProofExport
    (blob : @& ByteArray) (commitment : @& ByteArray) (proof : @& ByteArray)
    : IO UInt8 := do
  let ok ← runKzg (verifyBlobKzgProof blob commitment proof)
  return if ok then 1 else 0

@[export eth_kzg_verify_blob_kzg_proof_batch]
def verifyBlobKzgProofBatchExport
    (blobs : @& Array ByteArray)
    (commitments : @& Array ByteArray)
    (proofs : @& Array ByteArray) : IO UInt8 := do
  let ok ← runKzg (verifyBlobKzgProofBatch blobs commitments proofs)
  return if ok then 1 else 0

@[export eth_kzg_compute_cells]
def computeCellsExport (blob : @& ByteArray) : IO ByteArray := do
  let cells ← runKzg (computeCells blob)
  return cells.foldl (· ++ ·) ByteArray.empty

@[export eth_kzg_compute_verify_cell_kzg_proof_batch_challenge]
def computeVerifyCellKzgProofBatchChallengeExport
    (commitments : @& Array ByteArray)
    (commitmentIndicesBE : @& ByteArray)
    (cellIndicesBE : @& ByteArray)
    (cosetsEvals : @& Array ByteArray)
    (proofs : @& Array ByteArray) : IO ByteArray := do
  let commitmentIndices := unpackIndicesBE commitmentIndicesBE
  let cellIndices       := unpackIndicesBE cellIndicesBE
  let mut evals : Array CosetEvals := Array.mkEmpty cosetsEvals.size
  for ce in cosetsEvals do
    match cellToCosetEvals ce with
    | .ok e    => evals := evals.push e
    | .error err => throw <| IO.userError err.message
  pure <| blsFieldToBytes
    (computeVerifyCellKzgProofBatchChallenge
      commitments commitmentIndices cellIndices evals proofs)

@[export eth_kzg_compute_cells_and_kzg_proofs]
def computeCellsAndKzgProofsExport (blob : @& ByteArray) : IO ByteArray := do
  let (cells, proofs) ← runKzg (computeCellsAndKzgProofs blob)
  let cellsBuf  := cells.foldl  (· ++ ·) ByteArray.empty
  let proofsBuf := proofs.foldl (· ++ ·) ByteArray.empty
  return cellsBuf ++ proofsBuf

@[export eth_kzg_verify_cell_kzg_proof_batch]
def verifyCellKzgProofBatchExport
    (commitments : @& Array ByteArray)
    (cellIndicesBE : @& ByteArray)
    (cells : @& Array ByteArray)
    (proofs : @& Array ByteArray) : IO UInt8 := do
  let cellIndices := unpackIndicesBE cellIndicesBE
  let ok ← runKzg (verifyCellKzgProofBatch commitments cellIndices cells proofs)
  return if ok then 1 else 0

@[export eth_kzg_recover_cells_and_kzg_proofs]
def recoverCellsAndKzgProofsExport
    (cellIndicesBE : @& ByteArray) (cells : @& Array ByteArray) : IO ByteArray := do
  let cellIndices := unpackIndicesBE cellIndicesBE
  let (cells', proofs') ← runKzg (recoverCellsAndKzgProofs cellIndices cells)
  let cellsBuf  := cells'.foldl  (· ++ ·) ByteArray.empty
  let proofsBuf := proofs'.foldl (· ++ ·) ByteArray.empty
  return cellsBuf ++ proofsBuf

end EthLib.Cryptography.Kzg.Exports
