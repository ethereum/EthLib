module

public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Check

/-!
# Proofs: monomial points 1024 to 1279 of the embedded setup

Each theorem checks 16 monomial points of `G1` in the kernel.

The check passes when each point has order dividing `r`.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupTorsion

theorem g1Monomial_chunk_64 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1024).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1024 16]
  decide +kernel

theorem g1Monomial_chunk_65 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1040).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1040 16]
  decide +kernel

theorem g1Monomial_chunk_66 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1056).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1056 16]
  decide +kernel

theorem g1Monomial_chunk_67 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1072).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1072 16]
  decide +kernel

theorem g1Monomial_chunk_68 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1088).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1088 16]
  decide +kernel

theorem g1Monomial_chunk_69 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1104).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1104 16]
  decide +kernel

theorem g1Monomial_chunk_70 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1120).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1120 16]
  decide +kernel

theorem g1Monomial_chunk_71 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1136).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1136 16]
  decide +kernel

theorem g1Monomial_chunk_72 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1152).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1152 16]
  decide +kernel

theorem g1Monomial_chunk_73 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1168).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1168 16]
  decide +kernel

theorem g1Monomial_chunk_74 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1184).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1184 16]
  decide +kernel

theorem g1Monomial_chunk_75 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1200).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1200 16]
  decide +kernel

theorem g1Monomial_chunk_76 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1216).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1216 16]
  decide +kernel

theorem g1Monomial_chunk_77 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1232).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1232 16]
  decide +kernel

theorem g1Monomial_chunk_78 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1248).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1248 16]
  decide +kernel

theorem g1Monomial_chunk_79 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1264).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1264 16]
  decide +kernel

end EthLib.Cryptography.Kzg.SetupTorsion
