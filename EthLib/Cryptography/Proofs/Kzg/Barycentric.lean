import EthLib.Cryptography.Proofs.Kzg.Polynomials
import EthLib.Cryptography.Proofs.Bls.FrZMod
import EthLib.Cryptography.Proofs.Bls.FrBatchInverse
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Proofs: barycentric evaluation in Mathlib form

Restates the slow (barycentric) path of
`evaluatePolynomialInEvaluationForm` purely in Mathlib operations:
the fold `barycentricRefSum` becomes a `Finset.sum`
(`barycentricRefSum_eq_sum`), the spec's `Fr`-exponent power and
Fermat inverse become monoid power and field inverse, and the width
constant becomes a `Nat.cast`. The result,
`evaluatePolynomialInEvaluationForm_slowPath_sum`, is the form the
Lagrange-interpolation argument consumes.

Uses the scoped `Field Fr` instance from `Proofs.Bls.FrZMod`.
-/

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr

-- See the note in `Proofs.Bls.FrZMod`: core's `NatPow` instance on `Fin`
-- shadows Mathlib's monoid power on `Fr` and breaks
-- `rw` with Mathlib `pow` lemmas. File-local, so repeated here.
attribute [-instance] Fin.instNatPow

/-- The batch inverses of the barycentric denominators are their inverses. -/
theorem getElem!_batchInverse_denominators (domain : Array Fr) (z : Fr) (width k : Nat)
    (hk : k < width) :
    (Fr.batchInverse (Array.ofFn (n := width) fun i => z - domain[i.val]!))[k]! =
      (z - domain[k]!).inverse := by
  rw [Fr.batchInverse_eq_map, getElem!_pos _ k (by simpa using hk)]
  simp

/-- When `z` is not in the domain, evaluation follows the barycentric
formula the docstring describes. Mirror of
`evaluatePolynomialInEvaluationFormAux_fastPath`. -/
theorem evaluatePolynomialInEvaluationFormAux_slowPath
    (polynomial domain : Array Fr) (z : Fr)
    (h : domain.idxOf? z = none) :
    evaluatePolynomialInEvaluationFormAux polynomial domain z =
      barycentricRefSum polynomial domain z polynomial.size *
      (z ^ (Fr.ofNat polynomial.size) - Fr.one) *
      (Fr.ofNat polynomial.size).inverse := by
  rw [evaluatePolynomialInEvaluationFormAux]
  simp only [h]
  rw [barycentricSumInvAux_eq _ _ _ z _ 0 _
      (fun k _ hk => getElem!_batchInverse_denominators domain z _ k (by omega)),
    barycentricSumAux_zero_eq_refSum]

/-- When `z` is not in the evaluation domain, evaluating the polynomial
at `z` follows the barycentric formula. -/
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
    (evaluatePolynomialInEvaluationFormAux_slowPath polynomial _ z h)

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

/-- The barycentric sum as a `Finset.sum` over field operations only
(spec division unfolded to `* _⁻¹` via little Fermat). -/
theorem barycentricRefSum_eq_sum (p D : Array Fr) (z : Fr) (n : Nat) :
    barycentricRefSum p D z n
      = ∑ i ∈ Finset.range n, p[i]! * D[i]! * (z - D[i]!)⁻¹ := by
  rw [barycentricRefSum_eq_sum_div]
  exact Finset.sum_congr rfl fun i _ => Bls.Fr.div_eq_mul_inv' _ _

/-- The blob width is nonzero in `Fr` (it is `4096`, far below `r`), so
dividing by it in the barycentric formula is meaningful. -/
theorem natCast_field_elements_per_blob_ne_zero :
    ((FIELD_ELEMENTS_PER_BLOB : Nat) : Fr) ≠ 0 := by
  rw [← Bls.Fr.ofNat_eq_natCast]
  decide

/-- Slow path of `evaluatePolynomialInEvaluationFormAux` in Mathlib
operations. Needs the width to be canonical (`p.size < r`) so the
spec's detour of the exponent through `Fr` is invisible. -/
theorem evaluatePolynomialInEvaluationFormAux_slowPath_sum
    (p D : Array Fr) (z : Fr) (hw : p.size < Fr.modulus)
    (h : D.idxOf? z = none) :
    evaluatePolynomialInEvaluationFormAux p D z =
      (∑ i ∈ Finset.range p.size, p[i]! * D[i]! * (z - D[i]!)⁻¹)
        * (z ^ p.size - 1) * ((p.size : Nat) : Fr)⁻¹ := by
  rw [evaluatePolynomialInEvaluationFormAux_slowPath p D z h,
      barycentricRefSum_eq_sum, Bls.Fr.hpow_ofNat_eq_pow z hw,
      Bls.Fr.inverse_eq_inv, Bls.Fr.ofNat_eq_natCast, Bls.Fr.one_def]

/-- Slow path of `evaluatePolynomialInEvaluationForm` in Mathlib
operations: for a full-width polynomial and `z` outside the domain,

  `f(z) = (Σ_i p[i]·D[i]/(z − D[i])) · (z^4096 − 1) / 4096`

with `D` the bit-reversed 4096th roots of unity. -/
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
    (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB) z hw h
  rw [hsize] at this
  exact congrArg Except.ok this

end EthLib.Cryptography.Kzg
