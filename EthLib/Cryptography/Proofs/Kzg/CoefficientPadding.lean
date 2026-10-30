module

public import EthLib.Cryptography.Proofs.Kzg.CoefficientPolynomial

/-!
# Proofs: zero-padding a coefficient array

Recovery works on 8192 coefficients and returns the first 4096.

Padding with zeros and truncating again are both exact.

- Padding keeps every coefficient and the evaluation at every point.
- Truncating a padded array gives back the original.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg
open EthLib.Cryptography.Bls (Fr)
open scoped EthLib.Cryptography.Bls.Fr

/-- Pad an executable coefficient array with zeros to a chosen length. -/
def padCoefficients (n : Nat) (p : PolynomialCoeff) : PolynomialCoeff :=
  Array.ofFn fun i : Fin n => p[i.val]!

@[simp] theorem size_padCoefficients (n : Nat) (p : PolynomialCoeff) :
    (padCoefficients n p).size = n := Array.size_ofFn

/-- Padding preserves every coefficient, including zero coefficients beyond the old end. -/
theorem getElem!_padCoefficients (n : Nat) (p : PolynomialCoeff) (hp : p.size ≤ n) (i : Nat) :
    (padCoefficients n p)[i]! = p[i]! := by
  by_cases hi : i < n
  · rw [getElem!_pos (padCoefficients n p) i (by simpa using hi)]
    exact Array.getElem_ofFn _
  · rw [getElem!_neg (padCoefficients n p) i (by simpa using hi),
      getElem!_neg p i (by omega)]

/-- Padding represents exactly the same polynomial. -/
theorem coefficientPolynomial_padCoefficients (n : Nat) (p : PolynomialCoeff) (hp : p.size ≤ n) :
    coefficientPolynomial (padCoefficients n p) = coefficientPolynomial p := by
  apply Polynomial.ext
  intro i
  rw [coeff_coefficientPolynomial, coeff_coefficientPolynomial, getElem!_padCoefficients n p hp i]

/-- Padding does not change evaluation. -/
theorem evalPolyAt_padCoefficients (n : Nat) (p : PolynomialCoeff) (hp : p.size ≤ n) (x : Fr) :
    evalPolyAt (padCoefficients n p) x = evalPolyAt p x := by
  rw [← eval_coefficientPolynomial, coefficientPolynomial_padCoefficients n p hp,
    eval_coefficientPolynomial]

/-- Truncating a zero-padded coefficient vector to its original length recovers it. -/
theorem extract_padCoefficients (n : Nat) (p : PolynomialCoeff) (hp : p.size ≤ n) :
    (padCoefficients n p).extract 0 p.size = p := by
  apply Array.ext
  · simp [hp]
  · intro i hi hi'
    rw [Array.getElem_extract]
    have hpad : i < (padCoefficients n p).size := by rw [size_padCoefficients]; omega
    simp only [Nat.zero_add]
    rw [← getElem!_pos (padCoefficients n p) i (by rw [size_padCoefficients]; omega),
      getElem!_padCoefficients n p hp i, getElem!_pos p i hi']

end EthLib.Cryptography.Kzg
