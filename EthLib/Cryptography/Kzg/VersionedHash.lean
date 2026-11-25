module

public import EthLib.Base.Bytes
public import EthLib.Cryptography.Hash.Sha256
public import EthLib.Cryptography.Kzg.Types

/-!
# `Kzg.VersionedHash`

The versioned hash of a KZG commitment, from EIP-4844.

A blob transaction names each blob by this hash, and the beacon block carries the commitment.

The first byte is a version, and the other 31 bytes come from the SHA-256 of the commitment.

Source: "Helpers" of [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#helpers).
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

/-- The first byte of the versioned hash of a KZG commitment, from EIP-4844 "Parameters". -/
def VERSIONED_HASH_VERSION_KZG : UInt8 := 0x01

/-- The version byte, then the last 31 bytes of the SHA-256 of a compressed G1 commitment. -/
def kzgCommitmentToVersionedHash (commitment : KZGCommitment) : VersionedHash :=
  -- The version byte `0x01`, then bytes 1 to 31 of `SHA-256(commitment)`.
  ⟨(Hash.Sha256.hash32 (Base.packBytes commitment.bytes)).set 0 VERSIONED_HASH_VERSION_KZG⟩

end EthLib.Cryptography.Kzg
