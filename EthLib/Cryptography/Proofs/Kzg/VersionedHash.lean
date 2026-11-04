module

public import EthLib.Cryptography.Kzg.VersionedHash
public import EthLib.Cryptography.Proofs.Hash.Sha256

/-!
# Proofs: the versioned hash of a KZG commitment

The versioned hash of every commitment has 32 bytes, and starts with the version `0x01`.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

/-- The versioned hash of every commitment has 32 bytes and starts with `0x01`. -/
theorem kzgCommitmentToVersionedHash_shape (commitment : ByteArray) :
    (kzgCommitmentToVersionedHash commitment).size = 32 ∧
      (kzgCommitmentToVersionedHash commitment).data.toList.head? =
        some VERSIONED_HASH_VERSION_KZG := by
  have hsize := Hash.Sha256.hash_size commitment
  constructor
  · simp [kzgCommitmentToVersionedHash, Hash.sha256, ByteArray.size_append,
      ByteArray.size_extract, hsize]
    rfl
  · simp [kzgCommitmentToVersionedHash]

end EthLib.Cryptography.Kzg
