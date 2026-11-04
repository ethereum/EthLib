module

public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Check

/-!
# Proofs: monomial points 3584 to 3839 of the embedded setup

Each theorem checks 16 monomial points of `G1` in the kernel.

The check passes when each point has order dividing `r`.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupTorsion

theorem g1Monomial_chunk_224 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3584).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3584 16]
  decide +kernel

theorem g1Monomial_chunk_225 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3600).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3600 16]
  decide +kernel

theorem g1Monomial_chunk_226 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3616).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3616 16]
  decide +kernel

theorem g1Monomial_chunk_227 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3632).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3632 16]
  decide +kernel

theorem g1Monomial_chunk_228 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3648).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3648 16]
  decide +kernel

theorem g1Monomial_chunk_229 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3664).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3664 16]
  decide +kernel

theorem g1Monomial_chunk_230 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3680).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3680 16]
  decide +kernel

theorem g1Monomial_chunk_231 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3696).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3696 16]
  decide +kernel

theorem g1Monomial_chunk_232 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3712).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3712 16]
  decide +kernel

theorem g1Monomial_chunk_233 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3728).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3728 16]
  decide +kernel

theorem g1Monomial_chunk_234 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3744).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3744 16]
  decide +kernel

theorem g1Monomial_chunk_235 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3760).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3760 16]
  decide +kernel

theorem g1Monomial_chunk_236 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3776).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3776 16]
  decide +kernel

theorem g1Monomial_chunk_237 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3792).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3792 16]
  decide +kernel

theorem g1Monomial_chunk_238 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3808).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3808 16]
  decide +kernel

theorem g1Monomial_chunk_239 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3824).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3824 16]
  decide +kernel

end EthLib.Cryptography.Kzg.SetupTorsion
