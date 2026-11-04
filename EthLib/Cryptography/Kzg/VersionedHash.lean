module

public import EthLib.Cryptography.Hash.Sha256

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

/-- The version byte, then the last 31 bytes of the SHA-256 of the commitment. -/
def kzgCommitmentToVersionedHash (commitment : ByteArray) : ByteArray :=
  ⟨#[VERSIONED_HASH_VERSION_KZG]⟩ ++ (Hash.sha256 commitment).extract 1 32

end EthLib.Cryptography.Kzg
