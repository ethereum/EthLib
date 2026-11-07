module

public import EthLib.Cryptography.Proofs.Kzg.Polynomials
public import EthLib.Cryptography.Proofs.Bls.FrZMod
public import EthLib.Cryptography.Proofs.Bls.FrBatchInverse
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Proofs: barycentric evaluation in Mathlib form

The slow path of evaluation in evaluation form is the barycentric formula.

This file restates it with Mathlib operations only.

The fold becomes a finite sum, and the powers and the inverse become Mathlib's.

The width becomes a cast of a natural number.

That form feeds the proof that evaluation is Lagrange interpolation.

It uses the scoped field instance on `Fr` of the BLS proofs.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr

/-- The batch inverses of the barycentric denominators are their inverses. -/
theorem getElem!_batchInverse_denominators (domain : Array Fr) (z : Fr) (width k : Nat)
    (hk : k < width) :
    (Fr.batchInverse (Array.ofFn (n := width) fun i => z - domain[i.val]!))[k]! =
      (z - domain[k]!).inverse := by
  rw [Fr.batchInverse_eq_map, getElem!_pos _ k (by simpa using hk)]
  simp

/-- When `z` is not in `domain`, evaluation is the barycentric sum with the batch inverses. -/
theorem evaluatePolynomialInEvaluationFormAux_of_idxOf?_none
    (polynomial domain : Array Fr) (z : Fr)
    (hsize : polynomial.size = domain.size)
    (h : domain.idxOf? z = none) :
    evaluatePolynomialInEvaluationFormAux polynomial domain z =
      barycentricSumInvAux polynomial domain
        (Fr.batchInverse ((polynomial.zip domain).map fun x => z - x.2)) Fr.zero 0
          polynomial.size *
        (z ^ (Fr.ofNat polynomial.size) - Fr.one) * (Fr.ofNat polynomial.size).inverse := by
  have hz : z ∉ domain := Array.idxOf?_eq_none_iff.mp h
  have hfind : (polynomial.zip domain).find? (·.2 == z) = none := by
    rw [Array.find?_eq_none]
    intro x hx hxz
    exact hz (beq_iff_eq.mp hxz ▸ (Array.of_mem_zip hx).2)
  rw [evaluatePolynomialInEvaluationFormAux]
  simp only [hfind]
  rw [foldl_zip_zip_eq_barycentricSumInvAux _ _ _ hsize (by simp [Fr.batchInverse_eq_map, hsize])]

/-- The batch inverses of the denominators, read from the pairs of values and points. -/
theorem getElem!_batchInverse_zip_denominators (polynomial domain : Array Fr) (z : Fr) (k : Nat)
    (hsize : polynomial.size = domain.size) (hk : k < polynomial.size) :
    (Fr.batchInverse ((polynomial.zip domain).map fun x => z - x.2))[k]! =
      (z - domain[k]!).inverse := by
  rw [Fr.batchInverse_eq_map, getElem!_pos _ k (by simp; omega),
    getElem!_pos domain k (by omega)]
  simp [Array.getElem_zip]

/-- When `z` is not in the domain, evaluation follows the barycentric formula.

That is the formula the docstring describes.

Mirror of `evaluatePolynomialInEvaluationFormAux_fastPath`. -/
theorem evaluatePolynomialInEvaluationFormAux_slowPath
    (polynomial domain : Array Fr) (z : Fr)
    (hsize : polynomial.size = domain.size)
    (h : domain.idxOf? z = none) :
    evaluatePolynomialInEvaluationFormAux polynomial domain z =
      barycentricRefSum polynomial domain z polynomial.size *
      (z ^ (Fr.ofNat polynomial.size) - Fr.one) *
      (Fr.ofNat polynomial.size).inverse := by
  rw [evaluatePolynomialInEvaluationFormAux_of_idxOf?_none _ _ _ hsize h,
    barycentricSumInvAux_eq _ _ _ z _ 0 _
      (fun k _ hk => getElem!_batchInverse_zip_denominators _ domain z k hsize (by omega)),
    barycentricSumAux_zero_eq_refSum]

/-- Off the evaluation domain, evaluating the polynomial at `z` follows the barycentric formula. -/
theorem evaluatePolynomialInEvaluationForm_slowPath
    (polynomial : Polynomial) (z : Fr)
    (hsize : polynomial.size = FIELD_ELEMENTS_PER_BLOB)
    (h : (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB).idxOf? z = none) :
    evaluatePolynomialInEvaluationForm polynomial z =
      .ok (barycentricRefSum polynomial (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB)
        z polynomial.size *
      (z ^ (Fr.ofNat polynomial.size) - Fr.one) *
      (Fr.ofNat polynomial.size).inverse) := by
  rw [evaluatePolynomialInEvaluationForm, ite_eq_right (by simp [hsize])]
  exact congrArg Except.ok
    (evaluatePolynomialInEvaluationFormAux_slowPath polynomial _ z
      (by rw [hsize, size_rootsOfUnityBrp]) h)

/-- The barycentric sum as a `Finset.sum`, with the spec's division. -/
theorem barycentricRefSum_eq_sum_div (p D : Array Fr) (z : Fr) (n : Nat) :
    barycentricRefSum p D z n
      = ∑ i ∈ Finset.range n, p[i]! * D[i]! / (z - D[i]!) := by
  induction n with
  | zero => simp [barycentricRefSum]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    show barycentricRefSum p D z n + _ = _
    rfl

/-- The barycentric sum as a `Finset.sum` over field operations only.

The spec division is unfolded to `* _⁻¹` via little Fermat. -/
theorem barycentricRefSum_eq_sum (p D : Array Fr) (z : Fr) (n : Nat) :
    barycentricRefSum p D z n
      = ∑ i ∈ Finset.range n, p[i]! * D[i]! * (z - D[i]!)⁻¹ := by
  rw [barycentricRefSum_eq_sum_div]
  exact Finset.sum_congr rfl fun i _ => Bls.Fr.div_eq_mul_inv' _ _

/-- The blob width is nonzero in `Fr` (it is `4096`, far below `r`).

So dividing by it in the barycentric formula is meaningful. -/
theorem natCast_field_elements_per_blob_ne_zero :
    ((FIELD_ELEMENTS_PER_BLOB : Nat) : Fr) ≠ 0 := by
  exact Bls.Fr.natCast_ne_zero (by decide) (by decide)

/-- Slow path of `evaluatePolynomialInEvaluationFormAux` in Mathlib operations.

Needs the width to be canonical (`p.size < r`).

Then the spec's detour of the exponent through `Fr` is invisible. -/
theorem evaluatePolynomialInEvaluationFormAux_slowPath_sum
    (p D : Array Fr) (z : Fr) (hw : p.size < Fr.modulus) (hsize : p.size = D.size)
    (h : D.idxOf? z = none) :
    evaluatePolynomialInEvaluationFormAux p D z =
      (∑ i ∈ Finset.range p.size, p[i]! * D[i]! * (z - D[i]!)⁻¹)
        * (z ^ p.size - 1) * ((p.size : Nat) : Fr)⁻¹ := by
  rw [evaluatePolynomialInEvaluationFormAux_slowPath p D z hsize h,
      barycentricRefSum_eq_sum, Bls.Fr.hpow_ofNat_eq_pow z hw,
      Bls.Fr.inverse_eq_inv, Bls.Fr.ofNat_eq_natCast, Bls.Fr.one_def]

/-- Slow path of `evaluatePolynomialInEvaluationForm` in Mathlib operations.

Let `D` be the bit-reversed 4096th roots of unity.

Take a full-width polynomial and `z` outside the domain.

Then `f(z) = (Σ_i p[i]·D[i]/(z − D[i])) · (z^4096 − 1) / 4096`. -/
theorem evaluatePolynomialInEvaluationForm_slowPath_sum
    (p : Polynomial) (z : Fr) (hsize : p.size = FIELD_ELEMENTS_PER_BLOB)
    (h : (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB).idxOf? z = none) :
    evaluatePolynomialInEvaluationForm p z =
      .ok ((∑ i ∈ Finset.range FIELD_ELEMENTS_PER_BLOB,
          p[i]! * (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB)[i]!
            * (z - (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB)[i]!)⁻¹)
        * (z ^ FIELD_ELEMENTS_PER_BLOB - 1)
        * ((FIELD_ELEMENTS_PER_BLOB : Nat) : Fr)⁻¹) := by
  rw [evaluatePolynomialInEvaluationForm, ite_eq_right (by simp [hsize])]
  have hw : p.size < Fr.modulus := by rw [hsize]; decide
  have := evaluatePolynomialInEvaluationFormAux_slowPath_sum p
    (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB) z hw (by rw [hsize, size_rootsOfUnityBrp]) h
  rw [hsize] at this
  exact congrArg Except.ok this

end EthLib.Cryptography.Kzg
