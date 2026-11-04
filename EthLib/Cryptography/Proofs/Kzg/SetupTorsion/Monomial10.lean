module

public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Check

/-!
# Proofs: monomial points 2560 to 2815 of the embedded setup

Each theorem checks 16 monomial points of `G1` in the kernel.

The check passes when each point has order dividing `r`.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupTorsion

theorem g1Monomial_chunk_160 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2560).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2560 16]
  decide +kernel

theorem g1Monomial_chunk_161 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2576).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2576 16]
  decide +kernel

theorem g1Monomial_chunk_162 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2592).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2592 16]
  decide +kernel

theorem g1Monomial_chunk_163 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2608).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2608 16]
  decide +kernel

theorem g1Monomial_chunk_164 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2624).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2624 16]
  decide +kernel

theorem g1Monomial_chunk_165 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2640).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2640 16]
  decide +kernel

theorem g1Monomial_chunk_166 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2656).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2656 16]
  decide +kernel

theorem g1Monomial_chunk_167 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2672).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2672 16]
  decide +kernel

theorem g1Monomial_chunk_168 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2688).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2688 16]
  decide +kernel

theorem g1Monomial_chunk_169 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2704).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2704 16]
  decide +kernel

theorem g1Monomial_chunk_170 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2720).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2720 16]
  decide +kernel

theorem g1Monomial_chunk_171 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2736).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2736 16]
  decide +kernel

theorem g1Monomial_chunk_172 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2752).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2752 16]
  decide +kernel

theorem g1Monomial_chunk_173 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2768).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2768 16]
  decide +kernel

theorem g1Monomial_chunk_174 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2784).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2784 16]
  decide +kernel

theorem g1Monomial_chunk_175 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2800).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2800 16]
  decide +kernel

end EthLib.Cryptography.Kzg.SetupTorsion
