module

public import EthLib.Cryptography.Kzg.VersionedHash
public import EthLib.Cryptography.Proofs.Hash.Sha256

/-!
# Proofs: the versioned hash of a KZG commitment

The versioned hash of every commitment starts with the version `0x01`.

Its other 31 bytes are those of the SHA-256 hash of the commitment.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

/-- The versioned hash of every commitment starts with `0x01`. -/
theorem getElem_kzgCommitmentToVersionedHash_zero (commitment : ByteArray) :
    (kzgCommitmentToVersionedHash commitment)[0] = VERSIONED_HASH_VERSION_KZG := by
  simp [kzgCommitmentToVersionedHash]

/-- Every other byte of the versioned hash is the byte of the SHA-256 hash at its position. -/
theorem getElem_kzgCommitmentToVersionedHash_of_ne_zero (commitment : ByteArray) {i : Nat}
    (h : i < 32) (nonzero : i ≠ 0) :
    (kzgCommitmentToVersionedHash commitment)[i] = (Hash.Sha256.hash32 commitment)[i] := by
  simp [kzgCommitmentToVersionedHash, Ne.symm nonzero]

end EthLib.Cryptography.Kzg
