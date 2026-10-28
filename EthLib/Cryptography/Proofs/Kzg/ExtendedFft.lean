import EthLib.Cryptography.Proofs.Kzg.FftEvaluation

/-!
# Proofs: the FFT on the extended domain

Recovery runs FFTs over the 8192 roots of unity of the extended blob.

This file instantiates the general FFT facts at that domain.

- The forward FFT evaluates the polynomial at each root.
- The coset FFT evaluates it at each root times the recovery shift.
- The inverse FFT gives back the coefficients.
-/

namespace EthLib.Cryptography.Kzg
open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr
attribute [-instance] Fin.instNatPow

private theorem extended_roots (i : Nat) (hi : i < 2 ^ 13) :
    (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB)[i]! =
      domainRoot FIELD_ELEMENTS_PER_EXT_BLOB ^ i := by
  rw [getElem!_pos (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) i
    (by rw [size_computeRootsOfUnity]; exact hi), getElem_computeRootsOfUnity]

/-- Forward evaluation on the actual extended domain. -/
theorem getElem!_fftField_extended (p : PolynomialCoeff)
    (hp : p.size = FIELD_ELEMENTS_PER_EXT_BLOB) (i : Nat) (hi : i < FIELD_ELEMENTS_PER_EXT_BLOB) :
    (fftField p (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) false)[i]! =
      evalPolyAt p (domainRoot FIELD_ELEMENTS_PER_EXT_BLOB ^ i) :=
  getElem!_fftField_eval (k := 13)
    (isPrimitiveRoot_domainRoot (Nat.dvd_of_mod_eq_zero (by decide))) p _ hp
    (size_computeRootsOfUnity _) extended_roots i hi

/-- Forward coset evaluation on the actual recovery domain. -/
theorem getElem!_cosetFftField_extended (p : PolynomialCoeff)
    (hp : p.size = FIELD_ELEMENTS_PER_EXT_BLOB) (i : Nat) (hi : i < FIELD_ELEMENTS_PER_EXT_BLOB) :
    (cosetFftField p (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) false)[i]! =
      evalPolyAt p (Fr.ofNat PRIMITIVE_ROOT_OF_UNITY * domainRoot FIELD_ELEMENTS_PER_EXT_BLOB ^ i) :=
  getElem!_cosetFftField_eval (k := 13)
    (isPrimitiveRoot_domainRoot (Nat.dvd_of_mod_eq_zero (by decide))) p _ hp
    (size_computeRootsOfUnity _) extended_roots i hi

/-- Actual extended-domain inverse FFT recovers coefficients. -/
theorem fftField_extended_roundtrip (p : PolynomialCoeff)
    (hp : p.size = FIELD_ELEMENTS_PER_EXT_BLOB) :
    fftField (fftField p (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) false)
      (computeRootsOfUnity FIELD_ELEMENTS_PER_EXT_BLOB) true = p :=
  fftField_fftField_inv (k := 13)
    (isPrimitiveRoot_domainRoot (Nat.dvd_of_mod_eq_zero (by decide))) p _ hp
    (size_computeRootsOfUnity _) extended_roots

end EthLib.Cryptography.Kzg
