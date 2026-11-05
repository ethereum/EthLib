module

public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Check

/-!
# Proofs: monomial points 0 to 255 of the embedded setup

Each theorem checks 16 monomial points of `G1` in the kernel.

The check passes when each point has order dividing `r`.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupTorsion

theorem g1Monomial_chunk_0 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 0).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 0 16]
  decide +kernel

theorem g1Monomial_chunk_1 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 16).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 16 16]
  decide +kernel

theorem g1Monomial_chunk_2 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 32).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 32 16]
  decide +kernel

theorem g1Monomial_chunk_3 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 48).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 48 16]
  decide +kernel

theorem g1Monomial_chunk_4 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 64).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 64 16]
  decide +kernel

theorem g1Monomial_chunk_5 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 80).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 80 16]
  decide +kernel

theorem g1Monomial_chunk_6 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 96).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 96 16]
  decide +kernel

theorem g1Monomial_chunk_7 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 112).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 112 16]
  decide +kernel

theorem g1Monomial_chunk_8 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 128).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 128 16]
  decide +kernel

theorem g1Monomial_chunk_9 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 144).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 144 16]
  decide +kernel

theorem g1Monomial_chunk_10 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 160).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 160 16]
  decide +kernel

theorem g1Monomial_chunk_11 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 176).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 176 16]
  decide +kernel

theorem g1Monomial_chunk_12 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 192).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 192 16]
  decide +kernel

theorem g1Monomial_chunk_13 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 208).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 208 16]
  decide +kernel

theorem g1Monomial_chunk_14 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 224).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 224 16]
  decide +kernel

theorem g1Monomial_chunk_15 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 240).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 240 16]
  decide +kernel

end EthLib.Cryptography.Kzg.SetupTorsion
