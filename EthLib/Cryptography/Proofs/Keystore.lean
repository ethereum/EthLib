module

public import EthLib.Base.Proofs.MapM
public import EthLib.Cryptography.Keystore
public import EthLib.Cryptography.Proofs.Aes.Ctr
public import EthLib.Cryptography.Proofs.Hash.Pbkdf2
public import EthLib.Cryptography.Proofs.Hash.Scrypt
public import EthLib.Cryptography.Proofs.Hash.Sha256

/-!
# Proofs: ERC-2335 decryption

A mismatched checksum prevents secret decryption.

A key derivation beyond the caller's limits gives the limit error.

Verification accepts exactly a key of at least 32 bytes whose checksum matches the ciphertext.

A derived key always has at least 32 bytes, so verification never refuses one as too short.

Decryption returns as many bytes as the ciphertext holds.

Encrypting the secret again, under a recomputed checksum, gives back the ciphertext.
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

/-- A key derivation beyond the limits gives the limit error, for any checksum and ciphertext. -/
theorem decryptStore_of_not_admits (limits : KdfLimits) (store : Store) (password : String)
    (h : limits.admits (passwordBytes password).size store.kdf = false) :
    decryptStore limits store password =
      .error (.limitExceeded store.kdf.memory (store.kdf.work (passwordBytes password).size)) := by
  simp [decryptStore, h]
  rfl

/-! ## What verification accepts -/

/-- A key of at least 32 bytes whose checksum matches the ciphertext passes verification.

With the short-key and checksum refusals, nothing else stops the AES step of this function.
-/
theorem exists_decryptWithKey_eq_ok (store : Store) (key : ByteArray)
    (hsize : 32 ≤ key.size)
    (hcheck : (passwordChecksum key store.message != ⟨store.checksum.toArray⟩) = false) :
    ∃ secret, decryptWithKey store key = .ok secret := by
  simp [decryptWithKey, hsize, hcheck]
  exact ⟨_, rfl⟩

/-- A successful verification read a key of at least 32 bytes and a matching checksum. -/
theorem decryptWithKey_ok_inv {store : Store} {key secret : ByteArray}
    (h : decryptWithKey store key = .ok secret) :
    32 ≤ key.size ∧
      (passwordChecksum key store.message != ⟨store.checksum.toArray⟩) = false := by
  by_cases hsize : 32 ≤ key.size
  · refine ⟨hsize, ?_⟩
    by_cases hcheck : (passwordChecksum key store.message != ⟨store.checksum.toArray⟩) = true
    · rw [decryptWithKey_of_checksum_mismatch store key hsize hcheck] at h
      nomatch h
    · simpa using hcheck
  · rw [decryptWithKey_of_short store key (Nat.lt_of_not_le hsize)] at h
    nomatch h

/-- Verification accepts exactly a key of at least 32 bytes whose checksum matches. -/
theorem exists_decryptWithKey_eq_ok_iff (store : Store) (key : ByteArray) :
    (∃ secret, decryptWithKey store key = .ok secret) ↔
      32 ≤ key.size ∧
        (passwordChecksum key store.message != ⟨store.checksum.toArray⟩) = false :=
  ⟨fun ⟨_, h⟩ => decryptWithKey_ok_inv h,
    fun ⟨hsize, hcheck⟩ => exists_decryptWithKey_eq_ok store key hsize hcheck⟩

/-- Decryption returns as many bytes as the ciphertext holds.

It neither pads the secret nor cuts it to a key length.
-/
theorem decryptWithKey_size {store : Store} {key secret : ByteArray}
    (h : decryptWithKey store key = .ok secret) : secret.size = store.message.size := by
  obtain ⟨hsize, hcheck⟩ := decryptWithKey_ok_inv h
  simp [decryptWithKey, hsize, hcheck] at h
  simp only [Pure.pure, Except.pure] at h
  obtain rfl := Except.ok.inj h
  exact Aes.size_ctr _ _ _ _

/-! ## The derived key is long enough -/

/-- A successful derivation gives at least the 32 bytes that password verification reads.

PBKDF2 and scrypt return exactly the requested length, and one below 32 bytes is refused first.
-/
theorem le_size_of_deriveKey {password key : ByteArray} {kdf : Kdf}
    (h : deriveKey password kdf = .ok key) : 32 ≤ key.size := by
  unfold deriveKey at h
  split at h <;> split at h
  · nomatch h
  · rw [Base.mapError_ok_iff] at h
    rw [Hash.Pbkdf2.pbkdf2_size h]
    omega
  · nomatch h
  · rw [Base.mapError_ok_iff] at h
    rw [Hash.Scrypt.scrypt_size h]
    omega

/-- Password verification never refuses a derived key as too short.

So a short-key error never reports the size of a key that derivation produced.
-/
theorem decryptWithKey_ne_shortKey_of_deriveKey {password key : ByteArray} {kdf : Kdf}
    (hkey : deriveKey password kdf = .ok key) (store : Store) (size : Nat) :
    decryptWithKey store key ≠ .error (.shortKey size) := by
  by_cases hcheck : (passwordChecksum key store.message != ⟨store.checksum.toArray⟩) = true
  · rw [decryptWithKey_of_checksum_mismatch store key (le_size_of_deriveKey hkey) hcheck]
    simp
  · obtain ⟨secret, hok⟩ :=
      exists_decryptWithKey_eq_ok store key (le_size_of_deriveKey hkey) (by simpa using hcheck)
    rw [hok]
    simp

/-! ## CTR undoes itself -/

/-- The checksum of a key and a message, as the 32 bytes a store holds. -/
def checksumVector (key message : ByteArray) : Vector UInt8 32 :=
  ⟨(passwordChecksum key message).data, Hash.Sha256.hash_size _⟩

/-- Encrypting the decrypted secret again gives back the stored ciphertext.

The AES step is CTR under one key and counter, and CTR is its own inverse.

The second store holds the checksum of the secret, so its verification passes.
-/
theorem decryptWithKey_decryptWithKey {store : Store} {key secret : ByteArray}
    (h : decryptWithKey store key = .ok secret) :
    decryptWithKey { store with message := secret, checksum := checksumVector key secret } key =
      .ok store.message := by
  obtain ⟨hsize, hmatch⟩ := decryptWithKey_ok_inv h
  have hcheck : (passwordChecksum key secret !=
      ⟨(checksumVector key secret).toArray⟩) = false := by
    show (passwordChecksum key secret != passwordChecksum key secret) = false
    simp [bne, BEq.beq, ByteArray.beq]
    exact Array.isEqv_self _
  simp [decryptWithKey, hsize, hmatch] at h
  simp only [Pure.pure, Except.pure] at h
  obtain rfl := Except.ok.inj h
  simp [decryptWithKey, hsize, hcheck, Aes.ctr_ctr]
  rfl

end EthLib.Cryptography.Keystore
