module

public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Check

/-!
# Proofs: monomial points 3072 to 3327 of the embedded setup

Each theorem checks 16 monomial points of `G1` in the kernel.

The check passes when each point has order dividing `r`.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupTorsion

theorem g1Monomial_chunk_192 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3072).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3072 16]
  decide +kernel

theorem g1Monomial_chunk_193 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3088).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3088 16]
  decide +kernel

theorem g1Monomial_chunk_194 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3104).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3104 16]
  decide +kernel

theorem g1Monomial_chunk_195 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3120).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3120 16]
  decide +kernel

theorem g1Monomial_chunk_196 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3136).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3136 16]
  decide +kernel

theorem g1Monomial_chunk_197 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3152).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3152 16]
  decide +kernel

theorem g1Monomial_chunk_198 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3168).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3168 16]
  decide +kernel

theorem g1Monomial_chunk_199 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3184).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3184 16]
  decide +kernel

theorem g1Monomial_chunk_200 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3200).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3200 16]
  decide +kernel

theorem g1Monomial_chunk_201 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3216).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3216 16]
  decide +kernel

theorem g1Monomial_chunk_202 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3232).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3232 16]
  decide +kernel

theorem g1Monomial_chunk_203 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3248).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3248 16]
  decide +kernel

theorem g1Monomial_chunk_204 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3264).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3264 16]
  decide +kernel

theorem g1Monomial_chunk_205 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3280).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3280 16]
  decide +kernel

theorem g1Monomial_chunk_206 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3296).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3296 16]
  decide +kernel

theorem g1Monomial_chunk_207 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3312).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3312 16]
  decide +kernel

end EthLib.Cryptography.Kzg.SetupTorsion
