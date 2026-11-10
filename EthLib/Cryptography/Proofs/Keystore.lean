module

public import EthLib.Cryptography.Keystore
public import EthLib.Cryptography.Proofs.Aes.Ctr
public import EthLib.Cryptography.Proofs.Hash.Pbkdf2
public import EthLib.Cryptography.Proofs.Hash.Scrypt

/-!
# Proofs: ERC-2335 decryption

A mismatched checksum prevents secret decryption.

A key derivation beyond the caller's limits gives the limit error.

Verification accepts exactly a derived key of 32 bytes whose checksum matches the ciphertext.

A derived key always has those 32 bytes, so verification never refuses one.

Decryption returns as many octets as the ciphertext holds, and CTR undoes itself.
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

/-- A key of 32 bytes whose checksum matches the ciphertext passes verification.

This is the converse of the two refusals above: nothing else can stop the AES step.
-/
theorem decryptWithKey_of_checksum (store : Store) (key : ByteArray)
    (hsize : 32 ≤ key.size)
    (hcheck : (passwordChecksum key store.message != ⟨store.checksum.toArray⟩) = false) :
    ∃ secret, decryptWithKey store key = .ok secret := by
  simp [decryptWithKey, hsize, hcheck]
  exact ⟨_, rfl⟩

/-- Decryption returns as many octets as the ciphertext holds.

It neither pads the secret nor cuts it to a key length.
-/
theorem decryptWithKey_size {store : Store} {key secret : ByteArray}
    (h : decryptWithKey store key = .ok secret) : secret.size = store.message.size := by
  by_cases hsize : 32 ≤ key.size
  · by_cases hcheck : (passwordChecksum key store.message != ⟨store.checksum.toArray⟩) = true
    · rw [decryptWithKey_of_checksum_mismatch store key hsize hcheck] at h
      exact absurd h (by simp)
    · simp only [Bool.not_eq_true] at hcheck
      simp [decryptWithKey, hsize, hcheck] at h
      simp only [Pure.pure, Except.pure] at h
      obtain rfl := Except.ok.inj h
      exact Aes.size_ctr _ _ _ _
  · rw [decryptWithKey_of_short store key (Nat.lt_of_not_le hsize)] at h
    exact absurd h (by simp)

/-! ## The derived key is long enough -/

/-- A successful derivation gives the 32 bytes that password verification reads.

Both functions return exactly the requested length, and a shorter one is refused first.
-/
theorem deriveKey_size {password key : ByteArray} {kdf : Kdf}
    (h : deriveKey password kdf = .ok key) : 32 ≤ key.size := by
  unfold deriveKey at h
  split at h
  · rename_i iterations length salt
    split at h
    · exact absurd h (by simp)
    · rename_i hlen
      cases hinner : Hash.Pbkdf2.pbkdf2 password salt iterations length with
      | error e => rw [hinner] at h; exact absurd h (by simp [Except.mapError])
      | ok inner =>
        rw [hinner] at h
        simp only [Except.mapError] at h
        obtain rfl := Except.ok.inj h
        rw [Hash.Pbkdf2.pbkdf2_size hinner]
        omega
  · rename_i n r p length salt
    split at h
    · exact absurd h (by simp)
    · rename_i hlen
      cases hinner : Hash.Scrypt.scrypt password salt n r p length with
      | error e => rw [hinner] at h; exact absurd h (by simp [Except.mapError])
      | ok inner =>
        rw [hinner] at h
        simp only [Except.mapError] at h
        obtain rfl := Except.ok.inj h
        rw [Hash.Scrypt.scrypt_size hinner]
        omega

/-- Password verification never refuses the key that derivation produced.

So a `shortKey` from a parsed keystore reports its `dklen`, never the size of a derived key.
-/
theorem decryptWithKey_ne_shortKey_of_deriveKey {password key : ByteArray} {kdf : Kdf}
    (hkey : deriveKey password kdf = .ok key) (store : Store) (size : Nat) :
    decryptWithKey store key ≠ .error (.shortKey size) := by
  by_cases hcheck : (passwordChecksum key store.message != ⟨store.checksum.toArray⟩) = true
  · rw [decryptWithKey_of_checksum_mismatch store key (deriveKey_size hkey) hcheck]
    simp
  · obtain ⟨secret, hok⟩ :=
      decryptWithKey_of_checksum store key (deriveKey_size hkey) (by simpa using hcheck)
    rw [hok]
    simp

/-! ## CTR undoes itself -/

/-- The decrypted secret re-encrypts to the stored ciphertext.

The AES step is CTR under one key and counter, which is its own inverse, so a store whose message
is a successful decryption returns the message that decryption read.  Its checksum has to match
for verification to pass, which is why the caller supplies that.
-/
theorem decryptWithKey_decryptWithKey {store : Store} {key secret : ByteArray}
    (hsize : 32 ≤ key.size)
    (h : decryptWithKey store key = .ok secret)
    (hcheck : (passwordChecksum key secret != ⟨store.checksum.toArray⟩) = false) :
    decryptWithKey { store with message := secret } key = .ok store.message := by
  have hmatch : (passwordChecksum key store.message != ⟨store.checksum.toArray⟩) = false := by
    by_cases hne : (passwordChecksum key store.message != ⟨store.checksum.toArray⟩) = true
    · rw [decryptWithKey_of_checksum_mismatch store key hsize hne] at h
      exact absurd h (by simp)
    · simpa using hne
  simp [decryptWithKey, hsize, hmatch] at h
  simp only [Pure.pure, Except.pure] at h
  obtain rfl := Except.ok.inj h
  simp [decryptWithKey, hsize, hcheck, Aes.ctr_ctr]
  rfl

end EthLib.Cryptography.Keystore
