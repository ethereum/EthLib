module

public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Check

/-!
# Proofs: monomial points 1792 to 2047 of the embedded setup

Each theorem checks 16 monomial points of `G1` in the kernel.

The check passes when each point has order dividing `r`.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupTorsion

theorem g1Monomial_chunk_112 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1792).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1792 16]
  decide +kernel

theorem g1Monomial_chunk_113 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1808).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1808 16]
  decide +kernel

theorem g1Monomial_chunk_114 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1824).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1824 16]
  decide +kernel

theorem g1Monomial_chunk_115 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1840).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1840 16]
  decide +kernel

theorem g1Monomial_chunk_116 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1856).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1856 16]
  decide +kernel

theorem g1Monomial_chunk_117 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1872).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1872 16]
  decide +kernel

theorem g1Monomial_chunk_118 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1888).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1888 16]
  decide +kernel

theorem g1Monomial_chunk_119 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1904).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1904 16]
  decide +kernel

theorem g1Monomial_chunk_120 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1920).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1920 16]
  decide +kernel

theorem g1Monomial_chunk_121 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1936).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1936 16]
  decide +kernel

theorem g1Monomial_chunk_122 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1952).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1952 16]
  decide +kernel

theorem g1Monomial_chunk_123 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1968).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1968 16]
  decide +kernel

theorem g1Monomial_chunk_124 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 1984).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 1984 16]
  decide +kernel

theorem g1Monomial_chunk_125 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2000).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2000 16]
  decide +kernel

theorem g1Monomial_chunk_126 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2016).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2016 16]
  decide +kernel

theorem g1Monomial_chunk_127 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2032).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2032 16]
  decide +kernel

end EthLib.Cryptography.Kzg.SetupTorsion
