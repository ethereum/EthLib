module

public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Check

/-!
# Proofs: monomial points 768 to 1023 of the embedded setup

Each theorem checks 16 monomial points of `G1` in the kernel.

The check passes when each point has order dividing `r`.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupTorsion

theorem g1Monomial_chunk_48 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 768).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 768 16]
  decide +kernel

theorem g1Monomial_chunk_49 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 784).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 784 16]
  decide +kernel

theorem g1Monomial_chunk_50 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 800).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 800 16]
  decide +kernel

theorem g1Monomial_chunk_51 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 816).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 816 16]
  decide +kernel

theorem g1Monomial_chunk_52 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 832).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 832 16]
  decide +kernel

theorem g1Monomial_chunk_53 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 848).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 848 16]
  decide +kernel

theorem g1Monomial_chunk_54 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 864).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 864 16]
  decide +kernel

theorem g1Monomial_chunk_55 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 880).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 880 16]
  decide +kernel

theorem g1Monomial_chunk_56 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 896).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 896 16]
  decide +kernel

theorem g1Monomial_chunk_57 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 912).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 912 16]
  decide +kernel

theorem g1Monomial_chunk_58 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 928).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 928 16]
  decide +kernel

theorem g1Monomial_chunk_59 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 944).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 944 16]
  decide +kernel

theorem g1Monomial_chunk_60 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 960).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 960 16]
  decide +kernel

theorem g1Monomial_chunk_61 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 976).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 976 16]
  decide +kernel

theorem g1Monomial_chunk_62 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 992).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 992 16]
  decide +kernel

theorem g1Monomial_chunk_63 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1008).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1008 16]
  decide +kernel

end EthLib.Cryptography.Kzg.SetupTorsion
