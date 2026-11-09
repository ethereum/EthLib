module

public import EthLib.Cryptography.Keystore

/-!
# Proofs: ERC-2335 password verification

A mismatched checksum prevents secret decryption.

A key derivation beyond the caller's limits is refused before it runs.
-/

@[expose] public section

namespace EthLib.Cryptography.Keystore

/-- A short intermediate key is refused before either cryptographic step reads it. -/
theorem decryptWithKey_of_short (store : Store) (key : ByteArray) (h : key.size < 32) :
    decryptWithKey store key = .error (.shortKey key.size) := by
  simp [decryptWithKey, Nat.not_le.mpr h]
  rfl

/-- A checksum mismatch prevents the AES step. -/
theorem decryptWithKey_of_checksum_mismatch (store : Store) (key : ByteArray)
    (hsize : 32 ≤ key.size)
    (hcheck : (passwordChecksum key store.message != ⟨store.checksum.toArray⟩) = true) :
    decryptWithKey store key = .error .checksumMismatch := by
  simp [decryptWithKey, hsize, hcheck]
  rfl

/-- A key derivation beyond the caller's limits is refused, so it never runs. -/
theorem decryptStore_of_not_admits (limits : KdfLimits) (store : Store) (password : String)
    (h : limits.admits store.kdf = false) :
    decryptStore limits store password =
      .error (.limitExceeded store.kdf.memory store.kdf.work) := by
  simp [decryptStore, h]
  rfl

end EthLib.Cryptography.Keystore
