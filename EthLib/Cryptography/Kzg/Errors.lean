module

/-!
# `Kzg.Errors`

Typed errors for the KZG surface.

Every operation returns its result or one of these errors, so a failure names its cause.

The C exports turn an error into the message of a Python exception.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

/-- Every way a KZG operation can reject its input. -/
inductive KzgError where
  /-- A blob was not 131072 bytes long. -/
  | badBlobSize (actual : Nat)
  /-- A commitment was not 48 bytes long. -/
  | badCommitmentSize (actual : Nat)
  /-- A proof was not 48 bytes long. -/
  | badProofSize (actual : Nat)
  /-- A cell was not 2048 bytes long. -/
  | badCellSize (actual : Nat)
  /-- A field element, `z` or `y`, was not 32 bytes long. -/
  | badFieldElementSize (actual : Nat)
  /-- Commitment bytes failed group validation. -/
  | invalidCommitment (index : Option Nat)
  /-- Proof bytes failed group validation. -/
  | invalidProof (index : Option Nat)
  /-- A field element was not canonical. -/
  | invalidFieldElement (index : Option Nat)
  /-- An input array, named by its parameter, did not have the length of the array it must match. -/
  | inputLengthMismatch (input : String) (expected actual : Nat)
  /-- A G1 linear combination got different point and scalar counts. -/
  | lincombLengthMismatch (points scalars : Nat)
  /-- A commitment index referenced a commitment that does not exist. -/
  | commitmentIndexOutOfBounds
  /-- A cell index was 128 or more. -/
  | cellIndexOutOfBounds
  /-- Cell indices were not strictly ascending. -/
  | indicesNotAscending
  /-- Fewer than 50% of a blob's cells were provided. -/
  | notEnoughCells
  /-- More cells than exist in an extended blob were provided. -/
  | tooManyCells
  /-- Polynomial division by an empty polynomial, or by one with a zero leading coefficient.

  Division in `Fr` alone would give a wrong polynomial, with no error. -/
  | zeroDivisorPolynomial
  /-- A coefficient-form product would have more than 8192 coefficients. -/
  | polynomialProductTooLong (lenA lenB : Nat)
  /-- An evaluation-form polynomial did not have 4096 elements. -/
  | badPolynomialSize (actual : Nat)
  /-- The list of commitments of the core cell check contained a repeated commitment. -/
  | duplicateCommitments
  /-- 48-byte input failed to decompress to a G1 point. -/
  | invalidG1Point
  /-- Every cell of the extended blob was missing.

  The vanishing polynomial of that case does not fit, and recovery needs half the cells anyway. -/
  | tooManyMissingCells
  /-- A buffer of packed 8-byte indices has a length that is not a multiple of 8. -/
  | badIndicesBytesSize (actual : Nat)
  /-- A list of the trusted setup had the wrong length, or one of its points did not decode. -/
  | invalidTrustedSetup

/-- Human-readable description, used at the C-ABI boundary. -/
def KzgError.message : KzgError → String
  | .badBlobSize actual         => s!"bad blob size: {actual}"
  | .badCommitmentSize actual   => s!"bad commitment size: {actual}"
  | .badProofSize actual        => s!"bad proof size: {actual}"
  | .badCellSize actual         => s!"bad cell size: {actual}"
  | .badFieldElementSize actual => s!"bad field element size: {actual}"
  | .invalidCommitment (some index) => s!"invalid commitment at index {index}"
  | .invalidCommitment none         => "invalid commitment"
  | .invalidProof (some index)      => s!"invalid proof at index {index}"
  | .invalidProof none              => "invalid proof"
  | .invalidFieldElement (some index) => s!"invalid field element at index {index}"
  | .invalidFieldElement none         => "invalid field element"
  | .inputLengthMismatch input expected actual =>
      s!"input length mismatch: {input} has length {actual}, expected {expected}"
  | .lincombLengthMismatch points scalars =>
      s!"linear combination length mismatch: {points} points, {scalars} scalars"
  | .commitmentIndexOutOfBounds => "out-of-bounds commitment index"
  | .cellIndexOutOfBounds       => "cell index out of bounds"
  | .indicesNotAscending        => "indices not strictly ascending"
  | .notEnoughCells             => "not enough cells provided"
  | .tooManyCells               => "too many cells provided"
  | .zeroDivisorPolynomial      => "division by zero polynomial"
  | .polynomialProductTooLong lenA lenB =>
      s!"polynomial product too long: {lenA} + {lenB} coefficients"
  | .badPolynomialSize actual   => s!"bad polynomial size: {actual}"
  | .duplicateCommitments       => "duplicate commitments"
  | .invalidG1Point             => "invalid G1 point"
  | .tooManyMissingCells        => "too many missing cells"
  | .badIndicesBytesSize actual =>
      s!"bad indices byte buffer size: {actual} (must be a multiple of 8)"
  | .invalidTrustedSetup        => "invalid trusted setup"

end EthLib.Cryptography.Kzg
