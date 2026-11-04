module

public import EthLib.Cryptography.Proofs.Aes.CtrInputs

/-!
# Proofs: known answers for CTR-AES256

The kernel runs the first two blocks of the example F.5.5 of SP 800-38A.

The decryption example F.5.6 then follows from the round trip, with no second run.
-/

@[expose] public section

namespace EthLib.Cryptography.Aes

/-! ## CTR-AES256, F.5.5 and F.5.6 -/

/-- The AES-256 key of F.5.5. -/
def f55Key : Key .aes256 := #v[
  0x60, 0x3d, 0xeb, 0x10, 0x15, 0xca, 0x71, 0xbe, 0x2b, 0x73, 0xae, 0xf0, 0x85, 0x7d, 0x77, 0x81,
  0x1f, 0x35, 0x2c, 0x07, 0x3b, 0x61, 0x08, 0xd7, 0x2d, 0x98, 0x10, 0xa3, 0x09, 0x14, 0xdf, 0xf4]

/-- The first two ciphertext blocks of F.5.5. -/
def f55Ciphertext : ByteArray := ⟨#[
  0x60, 0x1e, 0xc3, 0x13, 0x77, 0x57, 0x89, 0xa5, 0xb7, 0xa7, 0xf5, 0x04, 0xbb, 0xf3, 0xd2, 0x28,
  0xf4, 0x43, 0xe3, 0xca, 0x4d, 0x62, 0xb5, 0x9a, 0xca, 0x84, 0xe9, 0x90, 0xca, 0xca, 0xf5, 0xc5]⟩

/-- CTR-AES256.Encrypt of F.5.5, on its first two blocks. -/
theorem ctr_f55 :
    (ctr (ciph .aes256 f55Key) 128 f5Counter f5Plaintext).data = f55Ciphertext.data := by
  decide +kernel

/-- CTR-AES256.Decrypt of F.5.6, on its first two blocks. -/
theorem ctr_f56 : ctr (ciph .aes256 f55Key) 128 f5Counter f55Ciphertext = f5Plaintext := by
  rw [← ByteArray.ext ctr_f55, ctr_ctr]

end EthLib.Cryptography.Aes
