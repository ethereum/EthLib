module

public import EthLib.Cryptography.Proofs.Aes.Block

/-!
# Proofs: known answers for AES

The kernel runs the cipher on the examples of FIPS 197.

Each inverse cipher answer then follows from the inversion theorem, with no second run.
-/

@[expose] public section

namespace EthLib.Cryptography.Aes

/-! ## FIPS 197-upd1, Appendix B

The cipher example of [FIPS 197-upd1](https://doi.org/10.6028/NIST.FIPS.197-upd1), for AES-128.

Its key is the key of the key expansion example of Appendix A.1. -/

/-- The key of Appendix B. -/
def appendixBKey : Key .aes128 :=
  #v[0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c]

/-- The input of Appendix B. -/
def appendixBInput : Block :=
  #v[0x32, 0x43, 0xf6, 0xa8, 0x88, 0x5a, 0x30, 0x8d, 0x31, 0x31, 0x98, 0xa2, 0xe0, 0x37, 0x07, 0x34]

/-- The output of Appendix B. -/
def appendixBOutput : Block :=
  #v[0x39, 0x25, 0x84, 0x1d, 0x02, 0xdc, 0x09, 0xfb, 0xdc, 0x11, 0x85, 0x97, 0x19, 0x6a, 0x0b, 0x32]

/-- AES-128 of the Appendix B input. -/
theorem ciph_appendixB : ciph .aes128 appendixBKey appendixBInput = appendixBOutput := by
  decide +kernel

/-! ## FIPS 197, Appendix C

The example vectors of the original
[FIPS 197](https://csrc.nist.gov/files/pubs/fips/197/final/docs/fips-197.pdf) of 2001.

FIPS 197-upd1 moved them to the website of the NIST Computer Security Resource Center. -/

/-- The plaintext of Appendix C. -/
def appendixCPlaintext : Block :=
  #v[0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff]

/-- The AES-128 key of Appendix C.1. -/
def appendixC1Key : Key .aes128 :=
  #v[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f]

/-- The AES-128 output of Appendix C.1. -/
def appendixC1Output : Block :=
  #v[0x69, 0xc4, 0xe0, 0xd8, 0x6a, 0x7b, 0x04, 0x30, 0xd8, 0xcd, 0xb7, 0x80, 0x70, 0xb4, 0xc5, 0x5a]

/-- The AES-256 key of Appendix C.3. -/
def appendixC3Key : Key .aes256 := #v[
  0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
  0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f]

/-- The AES-256 output of Appendix C.3. -/
def appendixC3Output : Block :=
  #v[0x8e, 0xa2, 0xb7, 0xca, 0x51, 0x67, 0x45, 0xbf, 0xea, 0xfc, 0x49, 0x90, 0x4b, 0x49, 0x60, 0x89]

/-- The AES-128 cipher of Appendix C.1. -/
theorem ciph_appendixC1 : ciph .aes128 appendixC1Key appendixCPlaintext = appendixC1Output := by
  decide +kernel

/-- The AES-128 inverse cipher of Appendix C.1. -/
theorem ciphInv_appendixC1 :
    ciphInv .aes128 appendixC1Key appendixC1Output = appendixCPlaintext := by
  rw [← ciph_appendixC1, ciphInv_ciph]

/-- The AES-256 cipher of Appendix C.3. -/
theorem ciph_appendixC3 : ciph .aes256 appendixC3Key appendixCPlaintext = appendixC3Output := by
  decide +kernel

/-- The AES-256 inverse cipher of Appendix C.3. -/
theorem ciphInv_appendixC3 :
    ciphInv .aes256 appendixC3Key appendixC3Output = appendixCPlaintext := by
  rw [← ciph_appendixC3, ciphInv_ciph]

end EthLib.Cryptography.Aes
