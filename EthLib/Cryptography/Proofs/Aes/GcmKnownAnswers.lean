module

public import EthLib.Cryptography.Proofs.Aes.Gcm

/-!
# Proofs: known answers for AES-128-GCM

The test cases come from the NIST CAVP file
[gcmtestvectors.zip](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/mac/gcmtestvectors.zip).

Each section names its response file and the parameters of its test case.

The kernel runs each encryption, and decryption follows from the round trip.
-/

@[expose] public section

namespace EthLib.Cryptography.Aes.Gcm

/-! ## gcmEncryptExtIV128.rsp, Count = 0

Its section is `Keylen = 128, IVlen = 96, PTlen = 0, AADlen = 0, Taglen = 128`.

An empty plaintext and no additional data, so only the tag is computed. -/

/-- The key. -/
def emptyKey : Key .aes128 := #v[
  0x11, 0x75, 0x4c, 0xd7, 0x2a, 0xec, 0x30, 0x9b, 0xf5, 0x2f, 0x76, 0x87, 0x21, 0x2e, 0x89, 0x57]

/-- The IV. -/
def emptyIv : ByteArray := ⟨#[
  0x3c, 0x81, 0x9d, 0x9a, 0x9b, 0xed, 0x08, 0x76, 0x15, 0x03, 0x0b, 0x65]⟩

/-- The plaintext. -/
def emptyPt : ByteArray := ByteArray.empty

/-- The additional data. -/
def emptyAad : ByteArray := ByteArray.empty

/-- The ciphertext. -/
def emptyCt : ByteArray := ByteArray.empty

/-- The tag. -/
def emptyTag : ByteArray := ⟨#[
  0x25, 0x03, 0x27, 0xc6, 0x74, 0xaa, 0xf4, 0x77, 0xae, 0xf2, 0x67, 0x57, 0x48, 0xcf, 0x69, 0x71]⟩


/-- Encryption gives the ciphertext and the tag of the file. -/
theorem encrypt_empty :
    (encrypt (ciph .aes128 emptyKey) 16 emptyIv emptyPt emptyAad).toOption =
      some (emptyCt, emptyTag) := by
  decide +kernel

/-- Decryption returns the plaintext, by the round trip. -/
theorem decrypt_empty :
    decrypt (ciph .aes128 emptyKey) 16 emptyIv emptyCt emptyAad emptyTag =
      .ok emptyPt :=
  decrypt_encrypt _ _ _ _ _ _ _ (eq_ok_of_toOption encrypt_empty)

/-! ## gcmEncryptExtIV128.rsp, Count = 0

Its section is `Keylen = 128, IVlen = 96, PTlen = 128, AADlen = 128, Taglen = 128`.

One block of plaintext and one block of additional data. -/

/-- The key. -/
def oneBlockKey : Key .aes128 := #v[
  0xc9, 0x39, 0xcc, 0x13, 0x39, 0x7c, 0x1d, 0x37, 0xde, 0x6a, 0xe0, 0xe1, 0xcb, 0x7c, 0x42, 0x3c]

/-- The IV. -/
def oneBlockIv : ByteArray := ⟨#[
  0xb3, 0xd8, 0xcc, 0x01, 0x7c, 0xbb, 0x89, 0xb3, 0x9e, 0x0f, 0x67, 0xe2]⟩

/-- The plaintext. -/
def oneBlockPt : ByteArray := ⟨#[
  0xc3, 0xb3, 0xc4, 0x1f, 0x11, 0x3a, 0x31, 0xb7, 0x3d, 0x9a, 0x5c, 0xd4, 0x32, 0x10, 0x30, 0x69]⟩

/-- The additional data. -/
def oneBlockAad : ByteArray := ⟨#[
  0x24, 0x82, 0x56, 0x02, 0xbd, 0x12, 0xa9, 0x84, 0xe0, 0x09, 0x2d, 0x3e, 0x44, 0x8e, 0xda, 0x5f]⟩

/-- The ciphertext. -/
def oneBlockCt : ByteArray := ⟨#[
  0x93, 0xfe, 0x7d, 0x9e, 0x9b, 0xfd, 0x10, 0x34, 0x8a, 0x56, 0x06, 0xe5, 0xca, 0xfa, 0x73, 0x54]⟩

/-- The tag. -/
def oneBlockTag : ByteArray := ⟨#[
  0x00, 0x32, 0xa1, 0xdc, 0x85, 0xf1, 0xc9, 0x78, 0x69, 0x25, 0xa2, 0xe7, 0x1d, 0x82, 0x72, 0xdd]⟩


/-- Encryption gives the ciphertext and the tag of the file. -/
theorem encrypt_oneBlock :
    (encrypt (ciph .aes128 oneBlockKey) 16 oneBlockIv oneBlockPt oneBlockAad).toOption =
      some (oneBlockCt, oneBlockTag) := by
  decide +kernel

/-- Decryption returns the plaintext, by the round trip. -/
theorem decrypt_oneBlock :
    decrypt (ciph .aes128 oneBlockKey) 16 oneBlockIv oneBlockCt oneBlockAad oneBlockTag =
      .ok oneBlockPt :=
  decrypt_encrypt _ _ _ _ _ _ _ (eq_ok_of_toOption encrypt_oneBlock)

/-! ## gcmEncryptExtIV128.rsp, Count = 0

Its section is `Keylen = 128, IVlen = 96, PTlen = 128, AADlen = 128, Taglen = 96`.

One block of each, with a 96-bit tag. -/

/-- The key. -/
def shortTagKey : Key .aes128 := #v[
  0x56, 0x2a, 0xe8, 0xaa, 0xdb, 0x8d, 0x23, 0xe0, 0xf2, 0x71, 0xa9, 0x9a, 0x7d, 0x1b, 0xd4, 0xd1]

/-- The IV. -/
def shortTagIv : ByteArray := ⟨#[
  0xf7, 0xa5, 0xe2, 0x39, 0x94, 0x13, 0xb8, 0x9b, 0x6a, 0xd3, 0x1a, 0xff]⟩

/-- The plaintext. -/
def shortTagPt : ByteArray := ⟨#[
  0xbb, 0xdc, 0x35, 0x04, 0xd8, 0x03, 0x68, 0x2a, 0xa0, 0x8a, 0x77, 0x3c, 0xde, 0x5f, 0x23, 0x1a]⟩

/-- The additional data. -/
def shortTagAad : ByteArray := ⟨#[
  0x2b, 0x96, 0x80, 0xb8, 0x86, 0xb3, 0xef, 0xb7, 0xc6, 0x35, 0x4b, 0x38, 0xc6, 0x3b, 0x53, 0x73]⟩

/-- The ciphertext. -/
def shortTagCt : ByteArray := ⟨#[
  0xe2, 0xb7, 0xe5, 0xed, 0x5f, 0xf2, 0x7f, 0xc8, 0x66, 0x41, 0x48, 0xf5, 0xa6, 0x28, 0xa4, 0x6d]⟩

/-- The tag. -/
def shortTagTag : ByteArray := ⟨#[
  0xcb, 0xf2, 0x01, 0x51, 0x84, 0xff, 0xfb, 0x82, 0xf2, 0x65, 0x1c, 0x36]⟩


/-- Encryption gives the ciphertext and the tag of the file. -/
theorem encrypt_shortTag :
    (encrypt (ciph .aes128 shortTagKey) 12 shortTagIv shortTagPt shortTagAad).toOption =
      some (shortTagCt, shortTagTag) := by
  decide +kernel

/-- Decryption returns the plaintext, by the round trip. -/
theorem decrypt_shortTag :
    decrypt (ciph .aes128 shortTagKey) 12 shortTagIv shortTagCt shortTagAad shortTagTag =
      .ok shortTagPt :=
  decrypt_encrypt _ _ _ _ _ _ _ (eq_ok_of_toOption encrypt_shortTag)

/-! ## gcmDecrypt128.rsp, Count = 1

Its section is `Keylen = 128, IVlen = 96, PTlen = 128, AADlen = 128, Taglen = 128`.

A ciphertext whose tag does not verify: the file marks it FAIL. -/

/-- The key. -/
def forgedKey : Key .aes128 := #v[
  0x86, 0x7f, 0xc5, 0xd5, 0x47, 0x6d, 0x50, 0x08, 0xf0, 0x70, 0x3d, 0x81, 0xe3, 0x62, 0x22, 0x55]

/-- The IV. -/
def forgedIv : ByteArray := ⟨#[
  0x22, 0x94, 0x55, 0x29, 0xdf, 0xf9, 0x47, 0xc3, 0xc9, 0x26, 0x4d, 0xf7]⟩

/-- The additional data. -/
def forgedAad : ByteArray := ⟨#[
  0x26, 0x1a, 0x9e, 0xfd, 0x4f, 0x32, 0xbc, 0x3d, 0x07, 0xc1, 0x15, 0xb4, 0xed, 0xcf, 0x8a, 0xdf]⟩

/-- The ciphertext. -/
def forgedCt : ByteArray := ⟨#[
  0x1c, 0x78, 0x50, 0x25, 0xe5, 0xa2, 0x67, 0x8e, 0x4b, 0x29, 0xb2, 0x92, 0x76, 0xe3, 0x95, 0xbb]⟩

/-- The tag. -/
def forgedTag : ByteArray := ⟨#[
  0x87, 0xfd, 0xf1, 0x26, 0x18, 0x46, 0x16, 0x4a, 0x95, 0x0c, 0x37, 0xa3, 0xf2, 0xee, 0xa1, 0x7d]⟩


/-- Decryption rejects the forged tag. -/
theorem decrypt_forged :
    (decrypt (ciph .aes128 forgedKey) 16 forgedIv forgedCt forgedAad forgedTag).toOption =
      none := by
  decide +kernel

end EthLib.Cryptography.Aes.Gcm
