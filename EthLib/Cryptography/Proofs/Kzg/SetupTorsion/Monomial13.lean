module

public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Check

/-!
# Proofs: monomial points 3328 to 3583 of the embedded setup

Each theorem checks 16 monomial points of `G1` in the kernel.

The check passes when each point has order dividing `r`.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupTorsion

theorem g1Monomial_chunk_208 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3328).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3328 16]
  decide +kernel

theorem g1Monomial_chunk_209 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3344).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3344 16]
  decide +kernel

theorem g1Monomial_chunk_210 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3360).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3360 16]
  decide +kernel

theorem g1Monomial_chunk_211 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3376).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3376 16]
  decide +kernel

theorem g1Monomial_chunk_212 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3392).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3392 16]
  decide +kernel

theorem g1Monomial_chunk_213 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3408).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3408 16]
  decide +kernel

theorem g1Monomial_chunk_214 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3424).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3424 16]
  decide +kernel

theorem g1Monomial_chunk_215 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3440).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3440 16]
  decide +kernel

theorem g1Monomial_chunk_216 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3456).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3456 16]
  decide +kernel

theorem g1Monomial_chunk_217 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3472).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3472 16]
  decide +kernel

theorem g1Monomial_chunk_218 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3488).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3488 16]
  decide +kernel

theorem g1Monomial_chunk_219 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3504).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3504 16]
  decide +kernel

theorem g1Monomial_chunk_220 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3520).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3520 16]
  decide +kernel

theorem g1Monomial_chunk_221 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3536).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3536 16]
  decide +kernel

theorem g1Monomial_chunk_222 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3552).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3552 16]
  decide +kernel

theorem g1Monomial_chunk_223 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3568).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3568 16]
  decide +kernel

end EthLib.Cryptography.Kzg.SetupTorsion
