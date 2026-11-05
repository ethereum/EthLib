module

public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Check

/-!
# Proofs: monomial points 2816 to 3071 of the embedded setup

Each theorem checks 16 monomial points of `G1` in the kernel.

The check passes when each point has order dividing `r`.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupTorsion

theorem g1Monomial_chunk_176 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2816).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2816 16]
  decide +kernel

theorem g1Monomial_chunk_177 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2832).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2832 16]
  decide +kernel

theorem g1Monomial_chunk_178 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2848).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2848 16]
  decide +kernel

theorem g1Monomial_chunk_179 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2864).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2864 16]
  decide +kernel

theorem g1Monomial_chunk_180 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2880).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2880 16]
  decide +kernel

theorem g1Monomial_chunk_181 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2896).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2896 16]
  decide +kernel

theorem g1Monomial_chunk_182 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2912).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2912 16]
  decide +kernel

theorem g1Monomial_chunk_183 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2928).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2928 16]
  decide +kernel

theorem g1Monomial_chunk_184 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2944).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2944 16]
  decide +kernel

theorem g1Monomial_chunk_185 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2960).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2960 16]
  decide +kernel

theorem g1Monomial_chunk_186 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2976).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2976 16]
  decide +kernel

theorem g1Monomial_chunk_187 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2992).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2992 16]
  decide +kernel

theorem g1Monomial_chunk_188 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3008).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3008 16]
  decide +kernel

theorem g1Monomial_chunk_189 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3024).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3024 16]
  decide +kernel

theorem g1Monomial_chunk_190 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3040).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3040 16]
  decide +kernel

theorem g1Monomial_chunk_191 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 3056).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 3056 16]
  decide +kernel

end EthLib.Cryptography.Kzg.SetupTorsion
