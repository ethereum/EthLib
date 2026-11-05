module

public import EthLib.Base.BigEndian
public import EthLib.Cryptography.Kzg.Core
public import EthLib.Cryptography.Kzg.VersionedHash

/-!
# `Evm.Precompiles.PointEvaluation`

The point evaluation precompile at address `0x0a`, from EIP-4844.

It checks a KZG proof that the polynomial of a blob takes a value `y` at a point `z`.

The call data names the blob by the versioned hash of its commitment.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.PointEvaluation

open EthLib.Base (natToBytes)
open EthLib.Cryptography.Bls (G2 Fr)
open EthLib.Cryptography.Kzg (kzgCommitmentToVersionedHash parseBytes validateKzgG1Point
  verifyKzgProofWith)

/-- The size of the call data: a versioned hash, two field elements and two compressed G1 points. -/
def INPUT_BYTES : Nat := 192

/-- The price of every call, from EIP-4844, Parameters. -/
def GAS_POINT_EVALUATION : Nat := 50000

/-- `FIELD_ELEMENTS_PER_BLOB`: the number of field elements in a blob, which the output reports. -/
def FIELD_ELEMENTS_PER_BLOB : Nat := 4096

/-- `[tau]_2`, the compressed G2 point of the trusted setup for the secret `tau`.

It is entry 1 of `g2_monomial` in the KZG trusted setup, which `Kzg.TrustedSetupData` holds too. -/
def KZG_SETUP_G2_MONOMIAL_1 : ByteArray := ⟨#[
    0xb5, 0xbf, 0xd7, 0xdd, 0x8c, 0xde, 0xb1, 0x28, 0x84, 0x3b, 0xc2, 0x87, 0x23, 0x0a, 0xf3, 0x89,
    0x26, 0x18, 0x70, 0x75, 0xcb, 0xfb, 0xef, 0xa8, 0x10, 0x09, 0xa2, 0xce, 0x61, 0x5a, 0xc5, 0x3d,
    0x29, 0x14, 0xe5, 0x87, 0x0c, 0xb4, 0x52, 0xd2, 0xaf, 0xaa, 0xab, 0x24, 0xf3, 0x49, 0x9f, 0x72,
    0x18, 0x5c, 0xbf, 0xee, 0x53, 0x49, 0x27, 0x14, 0x73, 0x44, 0x29, 0xb7, 0xb3, 0x86, 0x08, 0xe2,
    0x39, 0x26, 0xc9, 0x11, 0xcc, 0xec, 0xea, 0xc9, 0xa3, 0x68, 0x51, 0x47, 0x7b, 0xa4, 0xc6, 0x0b,
    0x08, 0x70, 0x41, 0xde, 0x62, 0x10, 0x00, 0xed, 0xc9, 0x8e, 0xda, 0xda, 0x20, 0xc1, 0xde, 0xf2]⟩

/-- Why a point evaluation call fails. -/
inductive PointEvaluationError where
  /-- The call data is not 192 bytes long. -/
  | invalidInputLength (size : Nat)
  /-- The gas given was below the price. -/
  | outOfGas (cost gas : Nat)
  /-- The versioned hash is not the one of the commitment. -/
  | versionedHashMismatch
  /-- The commitment is not a valid compressed G1 point in the subgroup. -/
  | invalidCommitment
  /-- `z` or `y` is not below the BLS12-381 group order. -/
  | invalidFieldElement
  /-- The proof is not a valid compressed G1 point in the subgroup. -/
  | invalidProof
  /-- `[tau]_2` does not decompress.

  The source decompresses the same constant, and fails the same way if it is invalid. -/
  | invalidTrustedSetup
  /-- The pairing check fails: the proof does not show `p(z) = y`. -/
  | proofRejected
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor.

The code ignores the arguments of the constructor.

A new constructor takes a new code, so that each code keeps its meaning. -/
def PointEvaluationError.code : PointEvaluationError → UInt32
  | .invalidInputLength .. => 1
  | .outOfGas .. => 2
  | .versionedHashMismatch => 3
  | .invalidCommitment => 4
  | .invalidFieldElement => 5
  | .invalidProof => 6
  | .invalidTrustedSetup => 7
  | .proofRejected => 8

/-- Whether `proof` shows that the polynomial of `commitment` takes the value `y` at `z`.

It decodes the inputs and `[tau]_2`, then runs the KZG check with `[tau]_2` alone.

The check holds when the quotient `(p(X) - y) / (X - z)` is a polynomial. -/
def verifyKzgProof (commitment z y proof : ByteArray) : Except PointEvaluationError Bool := do
  -- The inputs are decoded in the order of EIP-4844.
  let commitmentPoint ←
    (parseBytes 48 .badCommitmentSize commitment >>= validateKzgG1Point).mapError
      fun _ => .invalidCommitment
  let zField ← (Fr.fromBytesBE z).mapError fun _ => .invalidFieldElement
  let yField ← (Fr.fromBytesBE y).mapError fun _ => .invalidFieldElement
  let proofPoint ←
    (parseBytes 48 .badProofSize proof >>= validateKzgG1Point).mapError fun _ => .invalidProof
  let tau ← (G2.uncompress KZG_SETUP_G2_MONOMIAL_1).mapError fun _ => .invalidTrustedSetup
  return verifyKzgProofWith tau commitmentPoint zField yField proofPoint

/-- The output of every successful call: two 32-byte big-endian words.

They are the number of field elements in a blob, then the order of the scalar field. -/
def output : ByteArray :=
  ⟨(natToBytes 32 FIELD_ELEMENTS_PER_BLOB ++ natToBytes 32 Fr.modulus).toArray⟩

/-- The call: it checks the length, charges the gas, then checks the hash and the proof. -/
def pointEvaluation (data : ByteArray) (gas : Nat) : Except PointEvaluationError ByteArray := do
  if data.size ≠ INPUT_BYTES then
    throw (.invalidInputLength data.size)
  if gas < GAS_POINT_EVALUATION then
    throw (.outOfGas GAS_POINT_EVALUATION gas)
  let versionedHash := data.extract 0 32
  let z := data.extract 32 64
  let y := data.extract 64 96
  let commitment := data.extract 96 144
  let proof := data.extract 144 192
  if (kzgCommitmentToVersionedHash commitment).data.toList ≠ versionedHash.data.toList then
    throw .versionedHashMismatch
  if !(← verifyKzgProof commitment z y proof) then
    throw .proofRejected
  return output

end EthLib.Execution.Evm.Precompiles.PointEvaluation
