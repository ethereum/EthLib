module

public import EthLib.Cryptography.Proofs.Aes.Gcm

/-!
# Proofs: known answers for AES-128-GCM on partial blocks

The test cases come from the NIST CAVP file
[gcmtestvectors.zip](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/mac/gcmtestvectors.zip).

Each section names its response file and the parameters of its test case.

The kernel runs each encryption, and decryption follows from the round trip.
-/

@[expose] public section

namespace EthLib.Cryptography.Aes.Gcm

/-! ## gcmEncryptExtIV128.rsp, Count = 0

Its section is `Keylen = 128, IVlen = 96, PTlen = 104, AADlen = 160, Taglen = 128`.

13 bytes of plaintext and 20 bytes of additional data, so both end in a partial block. -/

/-- The key. -/
def partialKey : Key .aes128 := #v[
  0xfe, 0x01, 0x21, 0xf4, 0x2e, 0x59, 0x9f, 0x88, 0xff, 0x02, 0xa9, 0x85, 0x40, 0x3e, 0x19, 0xbb]

/-- The IV. -/
def partialIv : ByteArray := ⟨#[
  0x3b, 0xb9, 0xeb, 0x77, 0x24, 0xcb, 0xe1, 0x94, 0x3d, 0x43, 0xde, 0x21]⟩

/-- The plaintext. -/
def partialPt : ByteArray := ⟨#[
  0xfd, 0x33, 0x1c, 0xa8, 0x64, 0x60, 0x91, 0xc2, 0x9f, 0x21, 0xe5, 0xf0, 0xa1]⟩

/-- The additional data. -/
def partialAad : ByteArray := ⟨#[
  0x26, 0x62, 0xd8, 0x95, 0x03, 0x5b, 0x65, 0x19, 0xf3, 0x51, 0x0e, 0xae, 0x0f, 0xaa, 0x39, 0x00,
  0xad, 0x23, 0xcf, 0xdf]⟩

/-- The ciphertext. -/
def partialCt : ByteArray := ⟨#[
  0x59, 0xfe, 0x29, 0xb0, 0x7b, 0x0d, 0xe8, 0xd8, 0x69, 0xef, 0xbb, 0xd9, 0xb4]⟩

/-- The tag. -/
def partialTag : ByteArray := ⟨#[
  0xd2, 0x4c, 0x3e, 0x9c, 0x1c, 0x73, 0xc0, 0xaf, 0x10, 0x97, 0xe2, 0x60, 0x61, 0xc8, 0x57, 0xde]⟩


/-- Encryption gives the ciphertext and the tag of the file. -/
theorem encrypt_partial :
    (encrypt (ciph .aes128 partialKey) 16 partialIv partialPt partialAad).toOption =
      some (partialCt, partialTag) := by
  decide +kernel

/-- Decryption returns the plaintext, by the round trip. -/
theorem decrypt_partial :
    decrypt (ciph .aes128 partialKey) 16 partialIv partialCt partialAad partialTag =
      .ok partialPt :=
  decrypt_encrypt _ _ _ _ _ _ _ (eq_ok_of_toOption encrypt_partial)

end EthLib.Cryptography.Aes.Gcm
