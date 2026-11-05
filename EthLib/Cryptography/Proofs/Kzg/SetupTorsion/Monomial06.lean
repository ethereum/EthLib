module

public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Check

/-!
# Proofs: monomial points 1536 to 1791 of the embedded setup

Each theorem checks 16 monomial points of `G1` in the kernel.

The check passes when each point has order dividing `r`.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupTorsion

theorem g1Monomial_chunk_96 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1536).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1536 16]
  decide +kernel

theorem g1Monomial_chunk_97 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1552).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1552 16]
  decide +kernel

theorem g1Monomial_chunk_98 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1568).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1568 16]
  decide +kernel

theorem g1Monomial_chunk_99 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1584).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1584 16]
  decide +kernel

theorem g1Monomial_chunk_100 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1600).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1600 16]
  decide +kernel

theorem g1Monomial_chunk_101 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1616).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1616 16]
  decide +kernel

theorem g1Monomial_chunk_102 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1632).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1632 16]
  decide +kernel

theorem g1Monomial_chunk_103 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1648).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1648 16]
  decide +kernel

theorem g1Monomial_chunk_104 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1664).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1664 16]
  decide +kernel

theorem g1Monomial_chunk_105 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1680).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1680 16]
  decide +kernel

theorem g1Monomial_chunk_106 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1696).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1696 16]
  decide +kernel

theorem g1Monomial_chunk_107 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1712).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1712 16]
  decide +kernel

theorem g1Monomial_chunk_108 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1728).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1728 16]
  decide +kernel

theorem g1Monomial_chunk_109 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1744).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1744 16]
  decide +kernel

theorem g1Monomial_chunk_110 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1760).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1760 16]
  decide +kernel

theorem g1Monomial_chunk_111 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1776).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1776 16]
  decide +kernel

end EthLib.Cryptography.Kzg.SetupTorsion
