module

public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Check

/-!
# Proofs: monomial points 3840 to 4095 of the embedded setup

Each theorem checks 16 monomial points of `G1` in the kernel.

The check passes when each point has order dividing `r`.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupTorsion

theorem g1Monomial_chunk_240 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3840).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3840 16]
  decide +kernel

theorem g1Monomial_chunk_241 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3856).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3856 16]
  decide +kernel

theorem g1Monomial_chunk_242 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3872).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3872 16]
  decide +kernel

theorem g1Monomial_chunk_243 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3888).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3888 16]
  decide +kernel

theorem g1Monomial_chunk_244 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3904).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3904 16]
  decide +kernel

theorem g1Monomial_chunk_245 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3920).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3920 16]
  decide +kernel

theorem g1Monomial_chunk_246 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3936).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3936 16]
  decide +kernel

theorem g1Monomial_chunk_247 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3952).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3952 16]
  decide +kernel

theorem g1Monomial_chunk_248 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3968).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3968 16]
  decide +kernel

theorem g1Monomial_chunk_249 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3984).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3984 16]
  decide +kernel

theorem g1Monomial_chunk_250 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 4000).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 4000 16]
  decide +kernel

theorem g1Monomial_chunk_251 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 4016).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 4016 16]
  decide +kernel

theorem g1Monomial_chunk_252 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 4032).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 4032 16]
  decide +kernel

theorem g1Monomial_chunk_253 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 4048).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 4048 16]
  decide +kernel

theorem g1Monomial_chunk_254 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 4064).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 4064 16]
  decide +kernel

theorem g1Monomial_chunk_255 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 4080).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 4080 16]
  decide +kernel

end EthLib.Cryptography.Kzg.SetupTorsion
