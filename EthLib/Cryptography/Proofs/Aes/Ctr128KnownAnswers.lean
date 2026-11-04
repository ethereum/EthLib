module

public import EthLib.Cryptography.Proofs.Aes.CtrInputs

/-!
# Proofs: known answers for CTR-AES128

The kernel runs the first two blocks of the example F.5.1 of SP 800-38A.

The decryption example F.5.2 then follows from the round trip, with no second run.
-/

@[expose] public section

namespace EthLib.Cryptography.Aes

/-! ## CTR-AES128, F.5.1 and F.5.2 -/

/-- The AES-128 key of F.5.1. -/
def f51Key : Key .aes128 :=
  #v[0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c]

/-- The first two ciphertext blocks of F.5.1. -/
def f51Ciphertext : ByteArray := ⟨#[
  0x87, 0x4d, 0x61, 0x91, 0xb6, 0x20, 0xe3, 0x26, 0x1b, 0xef, 0x68, 0x64, 0x99, 0x0d, 0xb6, 0xce,
  0x98, 0x06, 0xf6, 0x6b, 0x79, 0x70, 0xfd, 0xff, 0x86, 0x17, 0x18, 0x7b, 0xb9, 0xff, 0xfd, 0xff]⟩

/-- CTR-AES128.Encrypt of F.5.1, on its first two blocks. -/
theorem ctr_f51 :
    (ctr (ciph .aes128 f51Key) 128 f5Counter f5Plaintext).data = f51Ciphertext.data := by
  decide +kernel

/-- CTR-AES128.Decrypt of F.5.2, on its first two blocks. -/
theorem ctr_f52 : ctr (ciph .aes128 f51Key) 128 f5Counter f51Ciphertext = f5Plaintext := by
  rw [← ByteArray.ext ctr_f51, ctr_ctr]

end EthLib.Cryptography.Aes
