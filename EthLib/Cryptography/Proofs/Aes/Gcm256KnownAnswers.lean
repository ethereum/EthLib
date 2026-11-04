module

public import EthLib.Cryptography.Proofs.Aes.Gcm

/-!
# Proofs: known answers for AES-256-GCM

The test cases come from the NIST CAVP file
[gcmtestvectors.zip](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/mac/gcmtestvectors.zip).

Each section names its response file and the parameters of its test case.

The kernel runs each encryption, and decryption follows from the round trip.
-/

@[expose] public section

namespace EthLib.Cryptography.Aes.Gcm

/-! ## gcmEncryptExtIV256.rsp, Count = 0

Its section is `Keylen = 256, IVlen = 96, PTlen = 128, AADlen = 128, Taglen = 128`.

One block of each under an AES-256 key. -/

/-- The key. -/
def aes256Key : Key .aes256 := #v[
  0x92, 0xe1, 0x1d, 0xcd, 0xaa, 0x86, 0x6f, 0x5c, 0xe7, 0x90, 0xfd, 0x24, 0x50, 0x1f, 0x92, 0x50,
  0x9a, 0xac, 0xf4, 0xcb, 0x8b, 0x13, 0x39, 0xd5, 0x0c, 0x9c, 0x12, 0x40, 0x93, 0x5d, 0xd0, 0x8b]

/-- The IV. -/
def aes256Iv : ByteArray := ⟨#[
  0xac, 0x93, 0xa1, 0xa6, 0x14, 0x52, 0x99, 0xbd, 0xe9, 0x02, 0xf2, 0x1a]⟩

/-- The plaintext. -/
def aes256Pt : ByteArray := ⟨#[
  0x2d, 0x71, 0xbc, 0xfa, 0x91, 0x4e, 0x4a, 0xc0, 0x45, 0xb2, 0xaa, 0x60, 0x95, 0x5f, 0xad, 0x24]⟩

/-- The additional data. -/
def aes256Aad : ByteArray := ⟨#[
  0x1e, 0x08, 0x89, 0x01, 0x6f, 0x67, 0x60, 0x1c, 0x8e, 0xbe, 0xa4, 0x94, 0x3b, 0xc2, 0x3a, 0xd6]⟩

/-- The ciphertext. -/
def aes256Ct : ByteArray := ⟨#[
  0x89, 0x95, 0xae, 0x2e, 0x6d, 0xf3, 0xdb, 0xf9, 0x6f, 0xac, 0x7b, 0x71, 0x37, 0xba, 0xe6, 0x7f]⟩

/-- The tag. -/
def aes256Tag : ByteArray := ⟨#[
  0xec, 0xa5, 0xaa, 0x77, 0xd5, 0x1d, 0x4a, 0x0a, 0x14, 0xd9, 0xc5, 0x1e, 0x1d, 0xa4, 0x74, 0xab]⟩


/-- Encryption gives the ciphertext and the tag of the file. -/
theorem encrypt_aes256 :
    (encrypt (ciph .aes256 aes256Key) 16 aes256Iv aes256Pt aes256Aad).toOption =
      some (aes256Ct, aes256Tag) := by
  decide +kernel

/-- Decryption returns the plaintext, by the round trip. -/
theorem decrypt_aes256 :
    decrypt (ciph .aes256 aes256Key) 16 aes256Iv aes256Ct aes256Aad aes256Tag =
      .ok aes256Pt :=
  decrypt_encrypt _ _ _ _ _ _ _ (eq_ok_of_toOption encrypt_aes256)

end EthLib.Cryptography.Aes.Gcm
