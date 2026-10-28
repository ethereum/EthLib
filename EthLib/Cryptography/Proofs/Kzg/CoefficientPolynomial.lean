import EthLib.Cryptography.Proofs.Kzg.FftEvaluation
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Proofs: coefficient arrays as Mathlib polynomials

The code stores a polynomial as an array of coefficients, lowest degree first.

This file maps that array to a polynomial over the scalar field.

The map preserves coefficients, evaluation and the degree bound.

So facts about degree and roots from Mathlib apply to the arrays the code computes.
-/

namespace EthLib.Cryptography.Kzg
open EthLib.Cryptography.Bls (Fr)
open scoped EthLib.Cryptography.Bls.Fr
attribute [-instance] Fin.instNatPow

/-- Mathematical polynomial denoted by an executable coefficient array. -/
noncomputable def coefficientPolynomial (p : PolynomialCoeff) : _root_.Polynomial Fr :=
  Polynomial.ofFn p.size (fun i => p[i.val])

/-- Coefficient lookup agrees, including the executable zero default outside the array. -/
theorem coeff_coefficientPolynomial (p : PolynomialCoeff) (i : Nat) :
    (coefficientPolynomial p).coeff i = p[i]! := by
  by_cases hi : i < p.size
  · rw [coefficientPolynomial, Polynomial.ofFn_coeff_eq_val_of_lt _ hi,
      getElem!_pos p i hi]
  · rw [coefficientPolynomial, Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hi),
      getElem!_neg p i hi]
    rfl

/-- The representation bridge preserves executable evaluation. -/
theorem eval_coefficientPolynomial (p : PolynomialCoeff) (x : Fr) :
    (coefficientPolynomial p).eval x = evalPolyAt p x := by
  rw [coefficientPolynomial, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]
  rw [evalPolyAt, evalCoeffPoly, evalCoeffPolyAux_eq_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [getElem!_pos p i.val i.isLt]
  rfl

/-- Array length is a strict bound on the represented degree. -/
theorem natDegree_coefficientPolynomial_lt {p : PolynomialCoeff} (hp : 0 < p.size) :
    (coefficientPolynomial p).natDegree < p.size :=
  Polynomial.ofFn_natDegree_lt hp _

/-- Convert a degree-bounded mathematical polynomial to a fixed-length coefficient array. -/
noncomputable def polynomialCoefficients (n : Nat) (p : _root_.Polynomial Fr) : PolynomialCoeff :=
  Array.ofFn fun i : Fin n => p.coeff i.val

/-- The fixed-length coefficient representation is exact under its degree bound. -/
theorem coefficientPolynomial_polynomialCoefficients (n : Nat) (p : _root_.Polynomial Fr)
    (hp : p.natDegree < n) :
    coefficientPolynomial (polynomialCoefficients n p) = p := by
  apply Polynomial.ext
  intro i
  by_cases hi : i < n
  · rw [coefficientPolynomial, Polynomial.ofFn_coeff_eq_val_of_lt _ (by
      change i < (Array.ofFn (fun j : Fin n => p.coeff j.val)).size
      simpa using hi)]
    exact Array.getElem_ofFn _
  · rw [coefficientPolynomial, Polynomial.ofFn_coeff_eq_zero_of_ge _ (by
      change (Array.ofFn (fun j : Fin n => p.coeff j.val)).size ≤ i
      simpa using Nat.le_of_not_gt hi)]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hp (Nat.le_of_not_gt hi))).symm

/-- Coefficients of a bounded product give its product evaluation at every point. -/
theorem eval_polynomialCoefficients_mul (n : Nat) (a b : PolynomialCoeff)
    (hdegree : (coefficientPolynomial a * coefficientPolynomial b).natDegree < n)
    (x : Fr) :
    evalPolyAt (polynomialCoefficients n (coefficientPolynomial a * coefficientPolynomial b)) x =
      evalPolyAt a x * evalPolyAt b x := by
  rw [← eval_coefficientPolynomial, coefficientPolynomial_polynomialCoefficients n _ hdegree,
    Polynomial.eval_mul, eval_coefficientPolynomial, eval_coefficientPolynomial]
  rfl

end EthLib.Cryptography.Kzg
