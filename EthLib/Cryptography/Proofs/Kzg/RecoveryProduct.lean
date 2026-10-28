import EthLib.Cryptography.Proofs.Kzg.Recovery
import EthLib.Cryptography.Proofs.Kzg.CoefficientPolynomial

/-!
# Proofs: the product fits the domain

`P` has degree below 4096, and `Z` has degree at most the number of missing positions.

With at most half the cells missing, `deg(P * Z) < 8192`.

So 8192 evaluations determine `P * Z` exactly, and the inverse FFT returns its coefficients.
-/

namespace EthLib.Cryptography.Kzg
open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr
attribute [-instance] Fin.instNatPow

/-- The vanishing polynomial degree is bounded by the number of erased field elements. -/
theorem natDegree_constructVanishingPolynomial_le
    {missing : Array CellIndex} {z : PolynomialCoeff}
    (hz : constructVanishingPolynomial missing = .ok z) :
    (coefficientPolynomial z).natDegree ≤ missing.size * FIELD_ELEMENTS_PER_CELL := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeff_coefficientPolynomial]
  exact constructVanishingPolynomial_high_zero hz i hi

/-- With at most half the cells erased, the numerator product fits the extended FFT domain. -/
theorem recovery_product_natDegree_lt
    {missing : Array CellIndex} {z p : PolynomialCoeff}
    (hz : constructVanishingPolynomial missing = .ok z)
    (hm : missing.size ≤ CELLS_PER_EXT_BLOB / 2)
    (hp : p.size = FIELD_ELEMENTS_PER_BLOB) :
    (coefficientPolynomial p * coefficientPolynomial z).natDegree < FIELD_ELEMENTS_PER_EXT_BLOB := by
  have hprod := Polynomial.natDegree_mul_le
    (p := coefficientPolynomial p) (q := coefficientPolynomial z)
  have hpdeg := natDegree_coefficientPolynomial_lt (p := p) (by rw [hp]; decide)
  have hzdeg := natDegree_constructVanishingPolynomial_le hz
  rw [hp] at hpdeg
  change p.size = 4096 at hp
  change missing.size ≤ 64 at hm
  change (coefficientPolynomial z).natDegree ≤ missing.size * 64 at hzdeg
  change (coefficientPolynomial p).natDegree < 4096 at hpdeg
  change (coefficientPolynomial p * coefficientPolynomial z).natDegree < 8192
  omega

/-- A concrete 8192-coefficient numerator with the correct product evaluations exists. -/
theorem exists_recovery_product
    {missing : Array CellIndex} {z p : PolynomialCoeff}
    (hz : constructVanishingPolynomial missing = .ok z)
    (hm : missing.size ≤ CELLS_PER_EXT_BLOB / 2)
    (hp : p.size = FIELD_ELEMENTS_PER_BLOB) :
    ∃ q : PolynomialCoeff, q.size = FIELD_ELEMENTS_PER_EXT_BLOB ∧
      ∀ x : Fr, evalPolyAt q x = evalPolyAt p x * evalPolyAt z x := by
  refine ⟨polynomialCoefficients FIELD_ELEMENTS_PER_EXT_BLOB
    (coefficientPolynomial p * coefficientPolynomial z), ?_, ?_⟩
  · exact Array.size_ofFn
  · exact eval_polynomialCoefficients_mul FIELD_ELEMENTS_PER_EXT_BLOB p z
      (recovery_product_natDegree_lt hz hm hp)

end EthLib.Cryptography.Kzg
