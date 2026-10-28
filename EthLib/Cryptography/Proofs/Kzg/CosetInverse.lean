import EthLib.Cryptography.Proofs.Kzg.FftInverse
import EthLib.Cryptography.Proofs.Kzg.Domain

/-!
# Proofs: the inverse coset FFT

A coset FFT evaluates a polynomial on the domain shifted by a constant `k`.

```text
    coefficients c_i  --shift by k^i-->  FFT  ==  evaluations at k * w^i
```

The inverse transform undoes the FFT and then the shift.

So both round trips are the identity, including on the 8192-point recovery domain.
-/


namespace EthLib.Cryptography.Kzg
open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr
attribute [-instance] Fin.instNatPow

/-- Cancelling the coefficient shifts used by coset FFTs. -/
theorem shiftVals_shiftVals_inverse (vals : Array Fr) (factor : Fr)
    (hf : factor ≠ 0) :
    shiftVals (shiftVals vals factor) factor.inverse = vals := by
  have hc (a : Fr) (i : Nat) :
      (a * Fr.powNat factor i) * Fr.powNat factor.inverse i = a := by
    have hp := Bls.Fr.powNat_eq_pow factor i
    have hi := Bls.Fr.powNat_eq_pow factor.inverse i
    rw [hp, hi]
    have hinv : factor.inverse ^ i = (factor ^ i)⁻¹ := by
      rw [Bls.Fr.inverse_eq_inv, inv_pow]
    rw [hinv, Bls.Fr.mul_assoc]
    have he : factor ^ i * (factor ^ i)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero i hf)
    rw [he]
    exact mul_one a
  apply Array.ext
  · simp only [size_shiftVals]
  · intro i hi hi'
    simp only [getElem_shiftVals]
    exact hc vals[i] i

/-- The executable coset inverse recovers the coefficient vector. -/
theorem cosetFftField_cosetFftField_inv {k : Nat} {ω : Fr}
    (hω : IsPrimitiveRoot ω (2 ^ k))
    (vals roots : Array Fr) (hn : vals.size = 2 ^ k) (hrs : roots.size = 2 ^ k)
    (hroots : ∀ i, i < 2 ^ k → roots[i]! = ω ^ i) :
    cosetFftField (cosetFftField vals roots false) roots true = vals := by
  simp only [cosetFftField, Bool.false_eq_true, ↓reduceIte]
  rw [fftField_fftField_inv hω _ roots (by simpa using hn) hrs hroots]
  exact shiftVals_shiftVals_inverse vals _ (by decide)

/-- The reverse executable coset round-trip. -/
theorem cosetFftField_inv_cosetFftField {k : Nat} {ω : Fr}
    (hω : IsPrimitiveRoot ω (2 ^ k))
    (vals roots : Array Fr) (hn : vals.size = 2 ^ k) (hrs : roots.size = 2 ^ k)
    (hroots : ∀ i, i < 2 ^ k → roots[i]! = ω ^ i) :
    cosetFftField (cosetFftField vals roots true) roots false = vals := by
  simp only [cosetFftField, Bool.false_eq_true, ↓reduceIte]
  have hs : (Fr.ofNat PRIMITIVE_ROOT_OF_UNITY).inverse.inverse =
      Fr.ofNat PRIMITIVE_ROOT_OF_UNITY := by
    rw [Bls.Fr.inverse_eq_inv, Bls.Fr.inverse_eq_inv, inv_inv]
  have hc := shiftVals_shiftVals_inverse (fftField vals roots true)
    (Fr.ofNat PRIMITIVE_ROOT_OF_UNITY).inverse (by
      rw [Bls.Fr.inverse_eq_inv]
      exact inv_ne_zero (by decide))
  rw [hs] at hc
  rw [hc]
  exact fftField_inv_fftField hω vals roots hn hrs hroots

/-- The actual extended-blob domain satisfies the hypotheses above. -/
theorem cosetFftField_extended_roundtrip (vals : Array Fr)
    (hn : vals.size = FIELD_ELEMENTS_PER_EXT_BLOB) :
    cosetFftField
      (cosetFftField vals (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) false)
      (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) true = vals := by
  apply cosetFftField_cosetFftField_inv (k := 13)
    (ω := domainRoot FIELD_ELEMENTS_PER_EXT_BLOB)
  · exact isPrimitiveRoot_domainRoot (Nat.dvd_of_mod_eq_zero (by decide))
  · exact hn
  · exact size_computeRootsOfUnity _
  · intro i hi
    rw [getElem!_pos _ i (by rw [size_computeRootsOfUnity]; exact hi),
      getElem_computeRootsOfUnity]

end EthLib.Cryptography.Kzg
