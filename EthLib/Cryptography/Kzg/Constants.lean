module

public import EthLib.Cryptography.Bls.Fr

@[expose] public section

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

/-!
## Domain separators

Each domain separator starts the hash input of one Fiat-Shamir challenge.

Provenance: consensus-specs defined all three, until its pull request [#5398][cs-5398] removed them.

Each has the bytes below in its file, at both commits named with that file:

```text
specs/deneb/polynomial-commitments.md, at 86fb82b2 and 8a3df1d7
  FIAT_SHAMIR_PROTOCOL_DOMAIN             "FSBLOBVERIFY_V1_"
  RANDOM_CHALLENGE_KZG_BATCH_DOMAIN       "RCKZGBATCH___V1_"

specs/fulu/polynomial-commitments-sampling.md, at 9d377fd5 and 8a3df1d7
  RANDOM_CHALLENGE_KZG_CELL_BATCH_DOMAIN  "RCKZGCBATCH__V1_"
```

[EIP-4844][eip-4844] takes its KZG functions from [commit `86fb82b2`][cs-86fb82b2].

[EIP-7594][eip-7594] points to the Fulu specifications of [commit `9d377fd5`][cs-9d377fd5].

Neither EIP states these bytes in its own text.

[Commit `8a3df1d7`][cs-8a3df1d7] is the parent of the commit that removed the two files.

This note records where the bytes come from, not which text makes them normative.

[cs-5398]: https://github.com/ethereum/consensus-specs/pull/5398
[eip-4844]: https://eips.ethereum.org/EIPS/eip-4844#cryptographic-helpers
[eip-7594]: https://eips.ethereum.org/EIPS/eip-7594#specification
[cs-86fb82b2]: https://github.com/ethereum/consensus-specs/blob/86fb82b221474cc89387fa6436806507b3849d88/specs/deneb/polynomial-commitments.md
[cs-9d377fd5]: https://github.com/ethereum/consensus-specs/blob/9d377fd53d029536e57cfda1a4d2c700c59f86bf/specs/fulu/polynomial-commitments-sampling.md
[cs-8a3df1d7]: https://github.com/ethereum/consensus-specs/tree/8a3df1d79d70000801407e33d660171be9cd06d1/specs
-/

/-- Domain separator for the Fiat-Shamir challenge of a blob and its commitment. -/
def FIAT_SHAMIR_PROTOCOL_DOMAIN : ByteArray := String.toUTF8 "FSBLOBVERIFY_V1_"

/-- Domain separator for the Fiat-Shamir challenge of the batch check of blob proofs. -/
def RANDOM_CHALLENGE_KZG_BATCH_DOMAIN : ByteArray := String.toUTF8 "RCKZGBATCH___V1_"

/-- Domain separator for the Fiat-Shamir challenge of the batch check of cell proofs. -/
def RANDOM_CHALLENGE_KZG_CELL_BATCH_DOMAIN : ByteArray := String.toUTF8 "RCKZGCBATCH__V1_"

/-- Serialized form of the point at infinity on the G1 group. -/
def G1_POINT_AT_INFINITY : Vector UInt8 48 :=
  (Vector.replicate 48 0).set 0 0xc0

/-- Number of G2 points in the trusted setup. -/
def KZG_SETUP_G2_LENGTH : Nat := 65

/-- Length of a compressed G2 point in bytes. -/
def BYTES_PER_G2_POINT : Nat := 96

end EthLib.Cryptography.Kzg.Constants
