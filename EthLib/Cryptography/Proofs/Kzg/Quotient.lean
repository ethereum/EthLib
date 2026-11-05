module

public import EthLib.Cryptography.Proofs.Kzg.Commitment
public import EthLib.Cryptography.Proofs.Kzg.Barycentric
public import EthLib.Cryptography.Proofs.Bls.FrBatchInverse

/-!
# Proofs: the quotient of a KZG proof

A KZG proof commits to `q` with `p(X) - p(z) = (X - z) q(X)`, through its values on the domain.

At a domain point `ω ≠ z`, the value is `(p(ω) - p(z)) / (ω - z)`.

At `ω = z` a second formula applies, because the values `ω q(ω)` sum to zero over the domain.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (G1 G2 Fr)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr
open Polynomial

/-- The quotient `(p(X) - p(z)) / (X - z)`, for `p` the interpolant of the values. -/
noncomputable def quotientPoly (poly : Polynomial) (z : Fr) : _root_.Polynomial Fr :=
  (interpolant poly - C ((interpolant poly).eval z)) /ₘ (X - C z)

/-- `p(X) - p(z) = (X - z) q(X)`: the division by `X - z` is exact. -/
theorem interpolant_sub_eq_mul (poly : Polynomial) (z : Fr) :
    interpolant poly - C ((interpolant poly).eval z) = (X - C z) * quotientPoly poly z := by
  refine (mul_divByMonic_eq_iff_isRoot.mpr ?_).symm
  simp [IsRoot]

/-- The interpolant has degree below 4096. -/
theorem natDegree_interpolant_lt (poly : Polynomial) :
    (interpolant poly).natDegree < FIELD_ELEMENTS_PER_BLOB := by
  have h := Lagrange.degree_interpolate_lt (s := Finset.univ) (r := fun i => poly[i.val]!)
    evalDomain_injective.injOn
  rw [Finset.card_univ, Fintype.card_fin] at h
  by_cases h0 : interpolant poly = 0
  · rw [h0, natDegree_zero]
    decide
  · exact (natDegree_lt_iff_degree_lt h0).mpr h

/-- The quotient has degree at most 4094. -/
theorem natDegree_quotientPoly_le (poly : Polynomial) (z : Fr) :
    (quotientPoly poly z).natDegree ≤ FIELD_ELEMENTS_PER_BLOB - 2 := by
  -- The lemma takes the semiring of `Fr` from `Ring`, and the goal takes it from `Semifield`.
  --
  -- To match the two on the interpolant, the kernel replay unfolds polynomial addition.
  --
  -- That addition matches on its arguments, so the kernel computes the interpolant.
  --
  -- For a variable polynomial the match is cheap, and the rewrite below needs no match.
  have natDegree_sub_C' (p : _root_.Polynomial Fr) (a : Fr) :
      (p - C a).natDegree = p.natDegree :=
    natDegree_sub_C
  rw [quotientPoly, natDegree_divByMonic _ (monic_X_sub_C z), natDegree_X_sub_C,
    natDegree_sub_C']
  have := natDegree_interpolant_lt poly
  omega

/-- The interpolant takes value `i` at domain point `i`. -/
theorem eval_interpolant_evalDomain (poly : Polynomial) (i : Fin FIELD_ELEMENTS_PER_BLOB) :
    (interpolant poly).eval (evalDomain i) = poly[i.val]! :=
  Lagrange.eval_interpolate_at_node _ evalDomain_injective.injOn (Finset.mem_univ i)

/-- Off `z`, the quotient at a domain point is the difference quotient of the values. -/
theorem eval_quotientPoly_evalDomain {poly : Polynomial} {z : Fr}
    {i : Fin FIELD_ELEMENTS_PER_BLOB} (hi : evalDomain i ≠ z) :
    (quotientPoly poly z).eval (evalDomain i) =
      (poly[i.val]! - (interpolant poly).eval z) * (evalDomain i - z)⁻¹ := by
  have h := congrArg (eval (evalDomain i)) (interpolant_sub_eq_mul poly z)
  simp only [eval_sub, eval_C, eval_mul, eval_X, eval_interpolant_evalDomain] at h
  have hne : evalDomain i - z ≠ 0 := sub_ne_zero.mpr hi
  calc (quotientPoly poly z).eval (evalDomain i)
      = (evalDomain i - z) * (quotientPoly poly z).eval (evalDomain i) * (evalDomain i - z)⁻¹ := by
        rw [mul_comm (evalDomain i - z)]
        exact (mul_inv_cancel_right₀ hne _).symm
    _ = _ := congrArg (· * (evalDomain i - z)⁻¹) h.symm

/-- A polynomial of degree at most 4094 has `sum_i ω_i g(ω_i) = 0` over the domain.

The coefficient of `X^4095` is the sum of the values times the weights `ω_i / 4096`. -/
theorem sum_eval_mul_evalDomain_eq_zero {g : _root_.Polynomial Fr}
    (hg : g.natDegree ≤ FIELD_ELEMENTS_PER_BLOB - 2) :
    ∑ i : Fin FIELD_ELEMENTS_PER_BLOB, g.eval (evalDomain i) * evalDomain i = 0 := by
  have h4096 : FIELD_ELEMENTS_PER_BLOB = 4096 := rfl
  have hlt : g.natDegree < FIELD_ELEMENTS_PER_BLOB := by
    rw [h4096] at hg ⊢
    omega
  have hdeg : g.degree < (Finset.univ : Finset (Fin FIELD_ELEMENTS_PER_BLOB)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    by_cases h0 : g = 0
    · rw [h0, degree_zero]
      exact WithBot.bot_lt_coe _
    · exact (natDegree_lt_iff_degree_lt h0).mp hlt
  have h := Lagrange.coeff_eq_sum evalDomain_injective.injOn hdeg
  rw [Finset.card_univ, Fintype.card_fin,
    coeff_eq_zero_of_natDegree_lt (by rw [h4096] at hg ⊢; omega)] at h
  -- Each term is the value times the weight `ω_i / 4096`.
  have key : ∑ i : Fin FIELD_ELEMENTS_PER_BLOB,
      g.eval (evalDomain i) / ∏ j ∈ Finset.univ.erase i, (evalDomain i - evalDomain j) =
        (∑ i : Fin FIELD_ELEMENTS_PER_BLOB, g.eval (evalDomain i) * evalDomain i) *
          ((FIELD_ELEMENTS_PER_BLOB : Nat) : Fr)⁻¹ := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hw := nodalWeight_evalDomain i
    rw [Lagrange.nodalWeight, Finset.prod_inv_distrib] at hw
    rw [div_eq_mul_inv, mul_assoc]
    exact congrArg (_ * ·) hw
  have h0 := h.trans key
  exact (mul_eq_zero.mp h0.symm).resolve_right
    (inv_ne_zero natCast_field_elements_per_blob_ne_zero)

/-- A fold that adds a term per entry, or skips the entry, is the sum of the kept terms. -/
private theorem foldl_skip_eq_sum {α : Type} [Inhabited α] (c : α → Bool) (g : α → Fr) :
    ∀ (l : List α) (acc : Fr),
      l.foldl (fun r t => if c t then r else r + g t) acc =
        acc + ∑ j ∈ Finset.range l.length, if c l[j]! then 0 else g l[j]!
  | [], acc => by
    simp only [List.foldl_nil, List.length_nil, Finset.range_zero, Finset.sum_empty]
    exact (add_zero acc).symm
  | t :: l, acc => by
    rw [List.foldl_cons, foldl_skip_eq_sum c g l, List.length_cons, Finset.sum_range_succ']
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
    split
    · exact congrArg (acc + ·) (add_zero _).symm
    · exact (add_assoc _ _ _).trans (congrArg (acc + ·) (add_comm _ _))

/-- Entry `j` of three zipped arrays of one length is the triple of their entries `j`. -/
private theorem getElem!_toList_zip_zip {a b c : Array Fr} {n : Nat}
    (ha : a.size = n) (hb : b.size = n) (hc : c.size = n) {j : Nat} (hj : j < n) :
    ((a.zip b).zip c).toList[j]! = ((a[j]!, b[j]!), c[j]!) := by
  have hz : j < ((a.zip b).zip c).toList.length := by simp [ha, hb, hc, hj]
  rw [getElem!_pos _ j hz, Array.getElem_toList, Array.getElem_zip, Array.getElem_zip,
    getElem!_pos a j (by omega), getElem!_pos b j (by omega), getElem!_pos c j (by omega)]

/-- The within-domain formula is a sum over the other domain points. -/
theorem computeQuotientEvalWithinDomain_eq_sum (z y : Fr) {poly : Polynomial}
    (hsize : poly.size = FIELD_ELEMENTS_PER_BLOB) :
    computeQuotientEvalWithinDomain z poly y =
      ∑ j : Fin FIELD_ELEMENTS_PER_BLOB, if evalDomain j = z then 0
        else (poly[j.val]! - y) * evalDomain j * (z * (z - evalDomain j))⁻¹ := by
  have hdom : (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB).size = FIELD_ELEMENTS_PER_BLOB :=
    size_rootsOfUnityBrp _
  have hinv : (Fr.batchInverse ((rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB).map
      fun omega_i => z * (z - omega_i))).size = FIELD_ELEMENTS_PER_BLOB := by
    rw [Fr.batchInverse_eq_map, Array.size_map, Array.size_map, hdom]
  unfold computeQuotientEvalWithinDomain
  simp only
  rw [← Array.foldl_toList]
  refine (foldl_skip_eq_sum (fun t : (Fr × Fr) × Fr => t.1.1 == z)
    (fun t : (Fr × Fr) × Fr => (t.1.2 - y) * t.1.1 * t.2) _ _).trans ?_
  set Z := ((rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB).zip poly).zip (Fr.batchInverse
    ((rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB).map fun omega_i => z * (z - omega_i))) with hZ
  have hlen : Z.toList.length = FIELD_ELEMENTS_PER_BLOB := by simp [hZ, hdom, hsize, hinv]
  rw [hlen, ← Fin.sum_univ_eq_sum_range]
  refine (zero_add _).trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [hZ, getElem!_toList_zip_zip hdom hsize hinv j.isLt, ← evalDomain_eq_getElem!]
  have hj : j.val < (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB).size := by rw [hdom]; exact j.isLt
  rw [Fr.batchInverse_eq_map, getElem!_pos (((rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB).map
      fun omega_i => z * (z - omega_i)).map Fr.inverse) j.val (by simp [hdom]),
    Array.getElem_map, Array.getElem_map,
    show (rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB)[j.val] = evalDomain j from rfl,
    Bls.Fr.inverse_eq_inv]
  simp only [beq_iff_eq]

/-- The term of a domain point other than `z`, written through the quotient at that point. -/
private theorem term_ne (p y w z : Fr) (hz : z ≠ 0) (hw : w - z ≠ 0) :
    (p - y) * w * (z * (z - w))⁻¹ = -z⁻¹ * ((p - y) * (w - z)⁻¹ * w) + 0 := by
  have hw' : z - w ≠ 0 := fun h => hw (by rw [← neg_sub, h, neg_zero])
  field_simp
  ring

/-- The term of the point `z` itself, which the formula skips. -/
private theorem term_eq (q z : Fr) (hz : z ≠ 0) : 0 = -z⁻¹ * (q * z) + q := by
  field_simp
  ring

/-- At a domain point `z`, the within-domain formula gives `q(z)`.

The proof uses that `sum_ω ω q(ω) = 0`, and takes out the term of `z`. -/
theorem computeQuotientEvalWithinDomain_eq {poly : Polynomial}
    (hsize : poly.size = FIELD_ELEMENTS_PER_BLOB) (m : Fin FIELD_ELEMENTS_PER_BLOB) :
    computeQuotientEvalWithinDomain (evalDomain m) poly ((interpolant poly).eval (evalDomain m)) =
      (quotientPoly poly (evalDomain m)).eval (evalDomain m) := by
  have hz0 : evalDomain m ≠ 0 := by
    intro h
    have hw := evalDomain_pow_width m
    rw [h] at hw
    exact zero_ne_one ((zero_pow (by decide : FIELD_ELEMENTS_PER_BLOB ≠ 0)).symm.trans hw)
  have hsum := sum_eval_mul_evalDomain_eq_zero (natDegree_quotientPoly_le poly (evalDomain m))
  rw [computeQuotientEvalWithinDomain_eq_sum _ _ hsize]
  have hterm : ∀ j : Fin FIELD_ELEMENTS_PER_BLOB,
      (if evalDomain j = evalDomain m then 0
        else (poly[j.val]! - (interpolant poly).eval (evalDomain m)) * evalDomain j *
          (evalDomain m * (evalDomain m - evalDomain j))⁻¹) =
      -(evalDomain m)⁻¹ * ((quotientPoly poly (evalDomain m)).eval (evalDomain j) * evalDomain j) +
        (if j = m then (quotientPoly poly (evalDomain m)).eval (evalDomain m) else 0) := by
    intro j
    by_cases hj : j = m
    · subst hj
      simp only [↓reduceIte]
      exact term_eq _ _ hz0
    · have hne : evalDomain j ≠ evalDomain m := fun h => hj (evalDomain_injective h)
      simp only [hne, hj, ↓reduceIte]
      rw [eval_quotientPoly_evalDomain hne]
      exact term_ne _ _ _ _ hz0 (sub_ne_zero.mpr hne)
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact (congrArg (· + _) (mul_zero _)).trans (zero_add _)

/-- Values that a polynomial of degree below 4096 takes on the domain interpolate back to it. -/
theorem interpolant_eq_of_eval {Q : Polynomial} {g : _root_.Polynomial Fr}
    (hg : g.natDegree < FIELD_ELEMENTS_PER_BLOB)
    (h : ∀ i : Fin FIELD_ELEMENTS_PER_BLOB, Q[i.val]! = g.eval (evalDomain i)) :
    interpolant Q = g := by
  have hdeg : g.degree < (Finset.univ : Finset (Fin FIELD_ELEMENTS_PER_BLOB)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    by_cases h0 : g = 0
    · rw [h0, degree_zero]
      exact WithBot.bot_lt_coe _
    · exact (natDegree_lt_iff_degree_lt h0).mp hg
  exact (Lagrange.eq_interpolate_of_eval_eq _ evalDomain_injective.injOn hdeg
    fun i _ => (h i).symm).symm

/-- On 4096 values, the proof computation commits to the values of `q`, and returns `p(z)`.

The commitment is the sum of the Lagrange points times those values. -/
theorem computeKzgProofImpl_eq (s : TrustedSetup) {poly : Polynomial}
    (hsize : poly.size = FIELD_ELEMENTS_PER_BLOB) (z : Fr) :
    ∃ Q : Array Fr, Q.size = FIELD_ELEMENTS_PER_BLOB ∧
      (∀ i : Fin FIELD_ELEMENTS_PER_BLOB, Q[i.val]! = (quotientPoly poly z).eval (evalDomain i)) ∧
      computeKzgProofImpl s poly z =
        .ok (compressG1 (G1.msm s.g1LagrangeBrp.toArray Q), (interpolant poly).eval z) := by
  let y := (interpolant poly).eval z
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_BLOB
  let Q : Array Fr := (domain.zip ((poly.map (· - y)).zip
      (Fr.batchInverse (domain.map (· - z))))).map fun (omega_i, a, inverse_i) =>
    if (omega_i - z).isZero then computeQuotientEvalWithinDomain omega_i poly y
    else a * inverse_i
  have hdom : domain.size = FIELD_ELEMENTS_PER_BLOB := size_rootsOfUnityBrp _
  have hQsize : Q.size = FIELD_ELEMENTS_PER_BLOB := by
    simp [Q, hdom, hsize, Fr.batchInverse_eq_map]
  refine ⟨Q, hQsize, fun i => ?_, ?_⟩
  · have hi : i.val < domain.size := by rw [hdom]; exact i.isLt
    rw [getElem!_pos Q i.val (by rw [hQsize]; exact i.isLt)]
    simp only [Q, Array.getElem_map, Array.getElem_zip, Fr.batchInverse_eq_map]
    rw [show domain[i.val] = evalDomain i from rfl, Bls.Fr.inverse_eq_inv,
      ← getElem!_pos poly i.val (by rw [hsize]; exact i.isLt)]
    by_cases hz : evalDomain i = z
    · have h0 : (evalDomain i - z).isZero = true := (Bls.Fr.isZero_iff _).mpr (sub_eq_zero.mpr hz)
      simp only [h0, ↓reduceIte]
      subst hz
      exact computeQuotientEvalWithinDomain_eq hsize i
    · have h0 : (evalDomain i - z).isZero = false :=
        Bool.eq_false_iff.mpr fun h => hz (sub_eq_zero.mp ((Bls.Fr.isZero_iff _).mp h))
      simp only [h0, Bool.false_eq_true, ↓reduceIte]
      exact (eval_quotientPoly_evalDomain hz).symm
  · unfold computeKzgProofImpl
    rw [evaluatePolynomialInEvaluationForm_eq_interpolate poly z hsize]
    change (g1LincombPoints s.g1LagrangeBrp.toArray Q >>= fun proofG1 =>
      pure (compressG1 proofG1, y)) = _
    rw [g1LincombPoints_eq_msm (by rw [Vector.size_toArray, hQsize])]
    rfl

end EthLib.Cryptography.Kzg
