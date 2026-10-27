import EthLib.Cryptography.Bls.Fr

namespace EthLib.Cryptography.Kzg.Constants

/-- Primitive root of unity for the BLS12-381 scalar field. -/
def PRIMITIVE_ROOT_OF_UNITY : Nat := 7

/-- Scalar field modulus of BLS12-381. -/
@[inline] def BLS_MODULUS : Nat := EthLib.Cryptography.Bls.Fr.modulus

/-- Number of bytes in a serialized KZG commitment. -/
def BYTES_PER_COMMITMENT : Nat := 48

/-- Number of bytes in a serialized KZG proof. -/
def BYTES_PER_PROOF : Nat := 48

/-- Number of bytes in a serialized field element. -/
def BYTES_PER_FIELD_ELEMENT : Nat := 32

/-- Number of field elements in a blob. -/
def FIELD_ELEMENTS_PER_BLOB : Nat := 4096

/-- Number of bytes in a blob. -/
def BYTES_PER_BLOB : Nat := BYTES_PER_FIELD_ELEMENT * FIELD_ELEMENTS_PER_BLOB

/-- Number of field elements in an extended blob. -/
def FIELD_ELEMENTS_PER_EXT_BLOB : Nat := 2 * FIELD_ELEMENTS_PER_BLOB

/-- Number of field elements in a cell. -/
def FIELD_ELEMENTS_PER_CELL : Nat := 64

/-- Number of bytes in a cell. -/
def BYTES_PER_CELL : Nat := FIELD_ELEMENTS_PER_CELL * BYTES_PER_FIELD_ELEMENT

/-- Number of cells in an extended blob. -/
def CELLS_PER_EXT_BLOB : Nat := FIELD_ELEMENTS_PER_EXT_BLOB / FIELD_ELEMENTS_PER_CELL

/-- Domain separator for the Fiat-Shamir challenge in `computeChallenge`. -/
def FIAT_SHAMIR_PROTOCOL_DOMAIN : ByteArray := String.toUTF8 "FSBLOBVERIFY_V1_"

/-- Domain separator for the Fiat-Shamir challenge in `verifyKzgProofBatch`. -/
def RANDOM_CHALLENGE_KZG_BATCH_DOMAIN : ByteArray := String.toUTF8 "RCKZGBATCH___V1_"

/-- Domain separator for the Fiat-Shamir challenge in `verifyCellKzgProofBatch`. -/
def RANDOM_CHALLENGE_KZG_CELL_BATCH_DOMAIN : ByteArray := String.toUTF8 "RCKZGCBATCH__V1_"

/-- Serialized form of the point at infinity on the G1 group. -/
def G1_POINT_AT_INFINITY : ByteArray :=
  ByteArray.mk <| Array.replicate 48 0 |>.set! 0 0xc0

/-- Number of G2 points in the trusted setup. -/
def KZG_SETUP_G2_LENGTH : Nat := 65

/-- Length of a compressed G2 point in bytes. -/
def BYTES_PER_G2_POINT : Nat := 96

end EthLib.Cryptography.Kzg.Constants
