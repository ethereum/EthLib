module

public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Check

/-!
# Proofs: monomial points 512 to 767 of the embedded setup

Each theorem checks 16 monomial points of `G1` in the kernel.

The check passes when each point has order dividing `r`.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupTorsion

theorem g1Monomial_chunk_32 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 512).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 512 16]
  decide +kernel

theorem g1Monomial_chunk_33 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 528).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 528 16]
  decide +kernel

theorem g1Monomial_chunk_34 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 544).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 544 16]
  decide +kernel

theorem g1Monomial_chunk_35 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 560).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 560 16]
  decide +kernel

theorem g1Monomial_chunk_36 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 576).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 576 16]
  decide +kernel

theorem g1Monomial_chunk_37 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 592).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 592 16]
  decide +kernel

theorem g1Monomial_chunk_38 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 608).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 608 16]
  decide +kernel

theorem g1Monomial_chunk_39 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 624).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 624 16]
  decide +kernel

theorem g1Monomial_chunk_40 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 640).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 640 16]
  decide +kernel

theorem g1Monomial_chunk_41 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 656).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 656 16]
  decide +kernel

theorem g1Monomial_chunk_42 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 672).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 672 16]
  decide +kernel

theorem g1Monomial_chunk_43 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 688).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 688 16]
  decide +kernel

theorem g1Monomial_chunk_44 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 704).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 704 16]
  decide +kernel

theorem g1Monomial_chunk_45 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 720).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 720 16]
  decide +kernel

theorem g1Monomial_chunk_46 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 736).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 736 16]
  decide +kernel

theorem g1Monomial_chunk_47 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 752).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 752 16]
  decide +kernel

end EthLib.Cryptography.Kzg.SetupTorsion
