module

public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Check

/-!
# Proofs: monomial points 256 to 511 of the embedded setup

Each theorem checks 16 monomial points of `G1` in the kernel.

The check passes when each point has order dividing `r`.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupTorsion

theorem g1Monomial_chunk_16 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 256).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 256 16]
  decide +kernel

theorem g1Monomial_chunk_17 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 272).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 272 16]
  decide +kernel

theorem g1Monomial_chunk_18 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 288).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 288 16]
  decide +kernel

theorem g1Monomial_chunk_19 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 304).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 304 16]
  decide +kernel

theorem g1Monomial_chunk_20 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 320).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 320 16]
  decide +kernel

theorem g1Monomial_chunk_21 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 336).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 336 16]
  decide +kernel

theorem g1Monomial_chunk_22 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 352).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 352 16]
  decide +kernel

theorem g1Monomial_chunk_23 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 368).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 368 16]
  decide +kernel

theorem g1Monomial_chunk_24 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 384).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 384 16]
  decide +kernel

theorem g1Monomial_chunk_25 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 400).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 400 16]
  decide +kernel

theorem g1Monomial_chunk_26 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 416).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 416 16]
  decide +kernel

theorem g1Monomial_chunk_27 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 432).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 432 16]
  decide +kernel

theorem g1Monomial_chunk_28 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 448).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 448 16]
  decide +kernel

theorem g1Monomial_chunk_29 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 464).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 464 16]
  decide +kernel

theorem g1Monomial_chunk_30 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 480).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 480 16]
  decide +kernel

theorem g1Monomial_chunk_31 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 496).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 496 16]
  decide +kernel

end EthLib.Cryptography.Kzg.SetupTorsion
