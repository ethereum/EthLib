module

public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Check

/-!
# Proofs: monomial points 1280 to 1535 of the embedded setup

Each theorem checks 16 monomial points of `G1` in the kernel.

The check passes when each point has order dividing `r`.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupTorsion

theorem g1Monomial_chunk_80 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1280).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1280 16]
  decide +kernel

theorem g1Monomial_chunk_81 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1296).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1296 16]
  decide +kernel

theorem g1Monomial_chunk_82 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1312).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1312 16]
  decide +kernel

theorem g1Monomial_chunk_83 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1328).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1328 16]
  decide +kernel

theorem g1Monomial_chunk_84 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1344).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1344 16]
  decide +kernel

theorem g1Monomial_chunk_85 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1360).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1360 16]
  decide +kernel

theorem g1Monomial_chunk_86 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1376).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1376 16]
  decide +kernel

theorem g1Monomial_chunk_87 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1392).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1392 16]
  decide +kernel

theorem g1Monomial_chunk_88 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1408).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1408 16]
  decide +kernel

theorem g1Monomial_chunk_89 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1424).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1424 16]
  decide +kernel

theorem g1Monomial_chunk_90 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1440).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1440 16]
  decide +kernel

theorem g1Monomial_chunk_91 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1456).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1456 16]
  decide +kernel

theorem g1Monomial_chunk_92 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1472).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1472 16]
  decide +kernel

theorem g1Monomial_chunk_93 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1488).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1488 16]
  decide +kernel

theorem g1Monomial_chunk_94 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1504).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1504 16]
  decide +kernel

theorem g1Monomial_chunk_95 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1520).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1520 16]
  decide +kernel

end EthLib.Cryptography.Kzg.SetupTorsion
