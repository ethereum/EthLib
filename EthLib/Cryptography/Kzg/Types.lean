module

/-!
# `Kzg.Types`

The 48-byte commitment and proof and the 32-byte versioned hash of EIP-4844, as structures.

So Lean rejects a public key, a Merkle root or one of these three where another is expected.

The checks of untrusted bytes still take the bytes.

Source: "Type aliases" of [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#type-aliases).
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

/-- A KZG commitment: the 48 bytes of a compressed `G1` point.

The type names the role of the bytes, not their validity as a point. -/
structure KZGCommitment where
  /-- The 48 bytes of the compressed point. -/
  bytes : Vector UInt8 48
deriving DecidableEq, Repr, Inhabited

/-- Commitments compare as their bytes, so a search tree can hold them. -/
instance : Ord KZGCommitment where
  compare a b := compare a.bytes b.bytes

/-- A KZG proof: the 48 bytes of a compressed `G1` point.

The type names the role of the bytes, not their validity as a point. -/
structure KZGProof where
  /-- The 48 bytes of the compressed point. -/
  bytes : Vector UInt8 48
deriving DecidableEq, Repr, Inhabited

/-- The versioned hash of a KZG commitment, which names a blob.

Its first byte names the version of the commitment scheme, which the type does not check. -/
structure VersionedHash where
  /-- The 32 bytes of the hash, the version byte first. -/
  bytes : Vector UInt8 32
deriving DecidableEq, Repr, Inhabited

end EthLib.Cryptography.Kzg
