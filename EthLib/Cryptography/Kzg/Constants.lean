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

/-! ## C-callable size accessors

The Python C extension queries every size at module-init time via these
`@[export]`-d functions and caches the results, so the wrapper has no
hardcoded constants of its own.

Each accessor takes a `Unit` to make the C-ABI signature predictable
(`UInt64 (*)(uint8_t)` after Lean's calling convention squashes the
unit). -/

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

end EthLib.Cryptography.Kzg.Constants
