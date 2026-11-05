module

public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Check

/-!
# Proofs: monomial points 2048 to 2303 of the embedded setup

Each theorem checks 16 monomial points of `G1` in the kernel.

The check passes when each point has order dividing `r`.

Separate theorems keep the memory of each kernel check small.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupTorsion

theorem g1Monomial_chunk_128 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2048).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2048 16]
  decide +kernel

theorem g1Monomial_chunk_129 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2064).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2064 16]
  decide +kernel

theorem g1Monomial_chunk_130 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2080).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2080 16]
  decide +kernel

theorem g1Monomial_chunk_131 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2096).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2096 16]
  decide +kernel

theorem g1Monomial_chunk_132 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2112).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2112 16]
  decide +kernel

theorem g1Monomial_chunk_133 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2128).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2128 16]
  decide +kernel

theorem g1Monomial_chunk_134 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2144).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2144 16]
  decide +kernel

theorem g1Monomial_chunk_135 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2160).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2160 16]
  decide +kernel

theorem g1Monomial_chunk_136 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2176).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2176 16]
  decide +kernel

theorem g1Monomial_chunk_137 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2192).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2192 16]
  decide +kernel

theorem g1Monomial_chunk_138 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2208).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2208 16]
  decide +kernel

theorem g1Monomial_chunk_139 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2224).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2224 16]
  decide +kernel

theorem g1Monomial_chunk_140 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2240).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2240 16]
  decide +kernel

theorem g1Monomial_chunk_141 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2256).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2256 16]
  decide +kernel

theorem g1Monomial_chunk_142 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2272).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2272 16]
  decide +kernel

theorem g1Monomial_chunk_143 :
    (((TrustedSetupData.g1MonomialHex.toList.map codes).drop 2288).take 16).all
      checkCodes = true := by
  rw [codes_chunk% TrustedSetupData.g1MonomialHex 2288 16]
  decide +kernel

end EthLib.Cryptography.Kzg.SetupTorsion
