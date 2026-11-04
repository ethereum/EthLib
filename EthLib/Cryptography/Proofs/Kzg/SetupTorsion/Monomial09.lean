module

public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Check

/-!
# Proofs: monomial points 2304 to 2559 of the embedded setup

Each theorem checks 16 monomial points of `G1` in the kernel.

The check passes when each point has order dividing `r`.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupTorsion

theorem g1Monomial_chunk_144 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2304).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2304 16]
  decide +kernel

theorem g1Monomial_chunk_145 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2320).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2320 16]
  decide +kernel

theorem g1Monomial_chunk_146 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2336).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2336 16]
  decide +kernel

theorem g1Monomial_chunk_147 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2352).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2352 16]
  decide +kernel

theorem g1Monomial_chunk_148 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2368).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2368 16]
  decide +kernel

theorem g1Monomial_chunk_149 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2384).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2384 16]
  decide +kernel

theorem g1Monomial_chunk_150 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2400).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2400 16]
  decide +kernel

theorem g1Monomial_chunk_151 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2416).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2416 16]
  decide +kernel

theorem g1Monomial_chunk_152 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2432).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2432 16]
  decide +kernel

theorem g1Monomial_chunk_153 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2448).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2448 16]
  decide +kernel

theorem g1Monomial_chunk_154 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2464).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2464 16]
  decide +kernel

theorem g1Monomial_chunk_155 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2480).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2480 16]
  decide +kernel

theorem g1Monomial_chunk_156 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2496).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2496 16]
  decide +kernel

theorem g1Monomial_chunk_157 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2512).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2512 16]
  decide +kernel

theorem g1Monomial_chunk_158 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2528).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2528 16]
  decide +kernel

theorem g1Monomial_chunk_159 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2544).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2544 16]
  decide +kernel

end EthLib.Cryptography.Kzg.SetupTorsion
