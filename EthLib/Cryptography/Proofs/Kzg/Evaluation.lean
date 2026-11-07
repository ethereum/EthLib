module

public import EthLib.Cryptography.Proofs.Kzg.Domain
public import EthLib.Cryptography.Proofs.Kzg.Barycentric
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Proofs: evaluation in evaluation form

Take a polynomial `p` of 4096 values on the bit-reversed roots of unity.

Its evaluation at `z` is the Lagrange interpolant of the pairs `(D[i], p[i])`, evaluated at `z`.

So if `p[i] = f(D[i])` for a polynomial `f` of degree below 4096, evaluation returns `f(z)`.

The proof splits on whether `z` is in the domain.

In the domain, the interpolant takes the value of its node.

Outside it, the interpolant is a barycentric sum with the nodal polynomial `X^4096 - 1`.

The nodal weights are `D[i] / 4096`, from the derivative `4096 X^4095` and `D[i]^4096 = 1`.

That is the formula of the specification.

It uses the scoped field instance on `Fr` of the BLS proofs.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.BitReversal
open scoped EthLib.Cryptography.Bls.Fr
open Polynomial

-- A few unification problems below exceed the default depth.
--
-- An example is seeing through `Lagrange.nodal` to its `Finset.prod`.
set_option maxRecDepth 4000

/-- The evaluation domain as a function on indices, as Mathlib's interpolation API expects it.

`evalDomain i` is element `i` of the bit-reversed 4096th roots of unity. -/
def evalDomain (i : Fin FIELD_ELEMENTS_PER_BLOB) : Fr :=
  (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB)[i.val]'
    (by rw [size_rootsOfUnityBrp]; exact i.isLt)

theorem evalDomain_eq_getElem! (i : Fin FIELD_ELEMENTS_PER_BLOB) :
    evalDomain i = (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB)[i.val]! := by
  rw [evalDomain, getElem!_pos (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB) i.val
    (by rw [size_rootsOfUnityBrp]; exact i.isLt)]

/-- The 4096 domain points are pairwise distinct: the interpolation nodes are honest nodes. -/
theorem evalDomain_injective : Function.Injective evalDomain := by
  intro i j h
  rw [evalDomain_eq_getElem!, evalDomain_eq_getElem!] at h
  exact Fin.ext (getElem_rootsOfUnityBrp_inj field_elements_per_blob_eq_two_pow
    field_elements_per_blob_dvd_modulus_sub_one i.isLt j.isLt h)

/-- Every domain point is a 4096th root of unity. -/
theorem evalDomain_pow_width (i : Fin FIELD_ELEMENTS_PER_BLOB) :
    evalDomain i ^ FIELD_ELEMENTS_PER_BLOB = 1 := by
  rw [← mem_rootsOfUnityBrp field_elements_per_blob_eq_two_pow
    field_elements_per_blob_dvd_modulus_sub_one]
  exact Array.mem_iff_getElem.mpr ⟨i.val, _, rfl⟩

/-- The nodal (vanishing) polynomial of the evaluation domain is `X^4096 − 1`.

The domain enumerates exactly the 4096th roots of unity.

The proof compares degrees, leading coefficients, and values at the 4096 distinct nodes.

Both sides vanish there. -/
theorem nodal_evalDomain :
    Lagrange.nodal Finset.univ evalDomain
      = X ^ FIELD_ELEMENTS_PER_BLOB - 1 := by
  apply Polynomial.eq_of_degree_le_of_eval_index_eq Finset.univ
    (Function.Injective.injOn evalDomain_injective)
  · simp [Lagrange.degree_nodal]
  · rw [← C_1, degree_X_pow_sub_C (by decide : 0 < FIELD_ELEMENTS_PER_BLOB)]
    simp [Lagrange.degree_nodal]
  · rw [Lagrange.nodal_monic.leadingCoeff, ← C_1,
      (monic_X_pow_sub_C 1
        (by decide : FIELD_ELEMENTS_PER_BLOB ≠ 0)).leadingCoeff]
  · intro i _
    rw [Lagrange.eval_nodal_at_node (Finset.mem_univ i),
        eval_sub, eval_pow, eval_X, eval_one]
    exact (sub_eq_zero_of_eq (evalDomain_pow_width i)).symm

/-- The barycentric weight of node `i` is `D[i]/4096`.

The weight is `(nodal'(D[i]))⁻¹`, and the derivative of `X^4096 − 1` is `4096·X^4095`.

Also `D[i]^4095 = D[i]⁻¹`, since `D[i]^4096 = 1`. -/
theorem nodalWeight_evalDomain (i : Fin FIELD_ELEMENTS_PER_BLOB) :
    Lagrange.nodalWeight Finset.univ evalDomain i
      = evalDomain i * ((FIELD_ELEMENTS_PER_BLOB : Nat) : Fr)⁻¹ := by
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ i),
      nodal_evalDomain, derivative_sub, derivative_one, derivative_X_pow,
      sub_zero, eval_mul, eval_pow, eval_X, eval_C]
  have hvpow : evalDomain i ^ (FIELD_ELEMENTS_PER_BLOB - 1)
      = (evalDomain i)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ,
      show FIELD_ELEMENTS_PER_BLOB - 1 + 1 = FIELD_ELEMENTS_PER_BLOB by decide]
    exact evalDomain_pow_width i
  rw [mul_inv, hvpow, inv_inv, mul_comm]

/-- Pure commutativity shuffle used in the slow-path sum below. -/
private theorem mul_shuffle (a b c q : Fr) :
    a * c * b * q = q * a * b * c := by
  rw [mul_comm, ← mul_assoc, ← mul_assoc, mul_right_comm]

/-- A domain miss means `z` is none of the interpolation nodes. -/
theorem ne_evalDomain_of_idxOf?_eq_none {z : Fr}
    (h : (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB).idxOf? z = none)
    (j : Fin FIELD_ELEMENTS_PER_BLOB) : z ≠ evalDomain j := by
  intro heq
  have hsz : j.val < (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB).size := by
    rw [size_rootsOfUnityBrp]; exact j.isLt
  have hmem : evalDomain j ∈ rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB :=
    Array.mem_iff_getElem.mpr ⟨j.val, hsz, rfl⟩
  rw [← heq] at hmem
  exact Array.idxOf?_eq_none_iff.mp h hmem

/-- **Correctness of `evaluatePolynomialInEvaluationForm`** (Lagrange form).

Take a full-width polynomial in evaluation form.

The function computes the evaluation at `z` of the Lagrange interpolant of the pairs `(D[i], p[i])`.

Here `D` is the bit-reversed roots-of-unity domain.

Together with interpolation uniqueness this pins the function down completely.

See `evaluatePolynomialInEvaluationForm_eq_eval` for the statement with an interpolated polynomial.
-/
theorem evaluatePolynomialInEvaluationForm_eq_interpolate
    (p : Polynomial) (z : Fr) (hsize : p.size = FIELD_ELEMENTS_PER_BLOB) :
    evaluatePolynomialInEvaluationForm p z
      = .ok (Polynomial.eval z ((Lagrange.interpolate Finset.univ evalDomain)
          fun i => p[i.val]!)) := by
  cases hidx : (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB).idxOf? z with
  | some i =>
    -- Fast path: `z = D[i]`, and the interpolant evaluates to `p[i]` at its `i`-th node.
    obtain ⟨hi, hz⟩ := idxOf?_rootsOfUnityBrp_eq_some hidx
    rw [evaluatePolynomialInEvaluationForm_fastPath p z i hsize hidx]
    have hz' : evalDomain ⟨i, hi⟩ = z := by
      rw [evalDomain_eq_getElem!]; exact hz
    rw [← hz', Lagrange.eval_interpolate_at_node _
      evalDomain_injective.injOn (Finset.mem_univ ⟨i, hi⟩)]
  | none =>
    -- Slow path: barycentric formula on both sides.
    rw [evaluatePolynomialInEvaluationForm_slowPath_sum p z hsize hidx,
        Lagrange.eval_interpolate_not_at_node _
          (fun j _ => ne_evalDomain_of_idxOf?_eq_none hidx j)]
    have hnodal : Polynomial.eval z (Lagrange.nodal Finset.univ evalDomain)
        = z ^ FIELD_ELEMENTS_PER_BLOB - 1 := by
      rw [nodal_evalDomain, eval_sub, eval_pow, eval_X, eval_one]
    have hsum : ∑ j : Fin FIELD_ELEMENTS_PER_BLOB,
          Lagrange.nodalWeight Finset.univ evalDomain j
            * (z - evalDomain j)⁻¹ * p[j.val]!
        = (∑ i ∈ Finset.range FIELD_ELEMENTS_PER_BLOB,
            p[i]! * (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB)[i]!
              * (z - (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB)[i]!)⁻¹)
          * ((FIELD_ELEMENTS_PER_BLOB : Nat) : Fr)⁻¹ := by
      rw [← Fin.sum_univ_eq_sum_range, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [nodalWeight_evalDomain j, evalDomain_eq_getElem!]
      exact mul_shuffle _ _ _ _
    refine congrArg Except.ok ?_
    calc (∑ i ∈ Finset.range FIELD_ELEMENTS_PER_BLOB,
            p[i]! * (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB)[i]!
              * (z - (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB)[i]!)⁻¹)
          * (z ^ FIELD_ELEMENTS_PER_BLOB - 1)
          * ((FIELD_ELEMENTS_PER_BLOB : Nat) : Fr)⁻¹
        = (z ^ FIELD_ELEMENTS_PER_BLOB - 1)
            * ((∑ i ∈ Finset.range FIELD_ELEMENTS_PER_BLOB,
                p[i]! * (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB)[i]!
                  * (z - (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB)[i]!)⁻¹)
              * ((FIELD_ELEMENTS_PER_BLOB : Nat) : Fr)⁻¹) := by
          rw [mul_right_comm]
          exact mul_comm _ _
      _ = Polynomial.eval z (Lagrange.nodal Finset.univ evalDomain)
            * ∑ j : Fin FIELD_ELEMENTS_PER_BLOB,
                Lagrange.nodalWeight Finset.univ evalDomain j
                  * (z - evalDomain j)⁻¹ * p[j.val]! :=
          (congrArg₂ (· * ·) hnodal hsum).symm

/-- **Correctness of `evaluatePolynomialInEvaluationForm`** (spec voice).

Let the blob's field elements be the evaluations of a polynomial `f` of degree `< 4096`.

The evaluations are over the bit-reversed roots-of-unity domain.

Then the function returns `f(z)` for *any* `z : Fr`, whether inside or outside the domain.

`f` is unique by interpolation, so this characterizes the function completely. -/
theorem evaluatePolynomialInEvaluationForm_eq_eval
    (p : Polynomial) (f : _root_.Polynomial Fr) (z : Fr)
    (hsize : p.size = FIELD_ELEMENTS_PER_BLOB)
    (hdeg : f.degree < FIELD_ELEMENTS_PER_BLOB)
    (hp : ∀ i, i < FIELD_ELEMENTS_PER_BLOB →
      p[i]! = f.eval (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB)[i]!) :
    evaluatePolynomialInEvaluationForm p z = .ok (f.eval z) := by
  rw [evaluatePolynomialInEvaluationForm_eq_interpolate p z hsize]
  have hf : f = (Lagrange.interpolate Finset.univ evalDomain)
      fun i => p[i.val]! := by
    refine Lagrange.eq_interpolate_of_eval_eq _ evalDomain_injective.injOn
      (by simpa using hdeg) fun i _ => ?_
    rw [hp i.val i.isLt, evalDomain_eq_getElem!]
  rw [← hf]

end EthLib.Cryptography.Kzg
