module

public import EthLib.Cryptography.Bls.Pairing
public import EthLib.Cryptography.Proofs.Bls.G1Group
public import EthLib.Cryptography.Proofs.Bls.G2Group

/-!
# Proofs: the pairing check depends only on affine points

A point has many Jacobian representatives `(X, Y, Z)`.

They all scale to one affine point `(X / Z^2, Y / Z^3)`.

The pairing check reads only that affine point, so every representative gives the same answer.

A pair with a point at infinity adds no factor, so it does not change the answer.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

open WeierstrassCurve.Jacobian

section Jacobian

variable {F : Type} [Field F] {W : WeierstrassCurve.Jacobian F} {P Q : Fin 3 → F}

/-- Two nonsingular representatives of one point are both at infinity or both finite. -/
private theorem Z_eq_zero_iff_of_toAffine_eq (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (h : Point.toAffine W P = Point.toAffine W Q) : P 2 = 0 ↔ Q 2 = 0 := by
  by_cases hPz : P 2 = 0 <;> by_cases hQz : Q 2 = 0
  · simp [hPz, hQz]
  · rw [Point.toAffine_of_Z_eq_zero hPz, Point.toAffine_of_Z_ne_zero hQ hQz] at h
    cases h
  · rw [Point.toAffine_of_Z_ne_zero hP hPz, Point.toAffine_of_Z_eq_zero hQz] at h
    cases h
  · simp [hPz, hQz]

/-- Two finite nonsingular representatives of one point have the same affine coordinates. -/
private theorem affine_eq_of_toAffine_eq (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (h : Point.toAffine W P = Point.toAffine W Q) (hPz : P 2 ≠ 0) (hQz : Q 2 ≠ 0) :
    P 0 / P 2 ^ 2 = Q 0 / Q 2 ^ 2 ∧ P 1 / P 2 ^ 3 = Q 1 / Q 2 ^ 3 := by
  rw [Point.toAffine_of_Z_ne_zero hP hPz, Point.toAffine_of_Z_ne_zero hQ hQz] at h
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at h
  exact h

end Jacobian

namespace G1

open scoped EthLib.Cryptography.Bls.Fp

/-- The spec multiplies by the inverse of `z` where Mathlib divides by `z`. -/
private theorem mul_inverse_sq (x z w : ZMod Fp.modulus) (hw : z * w = 1) :
    x * (w * w) = x / z ^ 2 := by
  rw [eq_inv_of_mul_eq_one_right hw]
  ring

private theorem mul_inverse_cube (y z w : ZMod Fp.modulus) (hw : z * w = 1) :
    y * (w * w * w) = y / z ^ 3 := by
  rw [eq_inv_of_mul_eq_one_right hw]
  ring

private theorem z_mul_inverse {P : G1} (hz : ¬P.z.isZero = true) :
    (P.z : ZMod Fp.modulus) * (P.z.inverse : ZMod Fp.modulus) = 1 := by
  rw [Fp.inverse_eq_inv]
  exact mul_inv_cancel₀ (fun h => hz (isZero_iff.mpr h))

/-- Two valid points with the same group element have the same affine coordinates. -/
theorem toAffine_congr {P Q : G1} (hP : Valid P) (hQ : Valid Q) (h : toPoint P = toPoint Q) :
    P.isInfinity = Q.isInfinity ∧ P.toAffine = Q.toAffine := by
  have hz : P.z.isZero = true ↔ Q.z.isZero = true :=
    isZero_iff.trans ((Z_eq_zero_iff_of_toAffine_eq hP hQ h).trans isZero_iff.symm)
  refine ⟨Bool.eq_iff_iff.mpr hz, ?_⟩
  by_cases hPz : P.z.isZero = true
  · simp [G1.toAffine, hPz, hz.mp hPz]
  · have hQz : ¬Q.z.isZero = true := fun h => hPz (hz.mpr h)
    obtain ⟨hx, hy⟩ := affine_eq_of_toAffine_eq hP hQ h
      (fun h => hPz (isZero_iff.mpr h)) (fun h => hQz (isZero_iff.mpr h))
    simp only [G1.toAffine, Fp.baseField_isZero, Fp.baseField_inverse, ite_eq_right hPz,
      ite_eq_right hQz]
    exact Prod.ext
      ((mul_inverse_sq _ _ _ (z_mul_inverse hPz)).trans
        (hx.trans (mul_inverse_sq _ _ _ (z_mul_inverse hQz)).symm))
      ((mul_inverse_cube _ _ _ (z_mul_inverse hPz)).trans
        (hy.trans (mul_inverse_cube _ _ _ (z_mul_inverse hQz)).symm))

end G1

namespace G2

/-- Two valid points with the same group element have the same affine coordinates. -/
theorem toAffine_congr {P Q : G2} (hP : Valid P) (hQ : Valid Q) (h : toPoint P = toPoint Q) :
    P.isInfinity = Q.isInfinity ∧ P.toAffine = Q.toAffine := by
  have hz : P.z.isZero = true ↔ Q.z.isZero = true :=
    isZero_iff.trans ((Z_eq_zero_iff_of_toAffine_eq hP hQ h).trans isZero_iff.symm)
  refine ⟨Bool.eq_iff_iff.mpr hz, ?_⟩
  by_cases hPz : P.z.isZero = true
  · simp [G2.toAffine, hPz, hz.mp hPz]
  · have hQz : ¬Q.z.isZero = true := fun h => hPz (hz.mpr h)
    obtain ⟨hx, hy⟩ := affine_eq_of_toAffine_eq hP hQ h
      (fun h => hPz (isZero_iff.mpr h)) (fun h => hQz (isZero_iff.mpr h))
    simp only [G2.toAffine, ite_eq_right hPz, ite_eq_right hQz]
    change (P.x * (P.z⁻¹ * P.z⁻¹), P.y * (P.z⁻¹ * P.z⁻¹ * P.z⁻¹)) =
      (Q.x * (Q.z⁻¹ * Q.z⁻¹), Q.y * (Q.z⁻¹ * Q.z⁻¹ * Q.z⁻¹))
    simp only [rep_x, rep_y, rep_z] at hx hy
    refine Prod.ext ?_ ?_
    · calc P.x * (P.z⁻¹ * P.z⁻¹) = P.x / P.z ^ 2 := by ring
        _ = Q.x / Q.z ^ 2 := hx
        _ = Q.x * (Q.z⁻¹ * Q.z⁻¹) := by ring
    · calc P.y * (P.z⁻¹ * P.z⁻¹ * P.z⁻¹) = P.y / P.z ^ 3 := by ring
        _ = Q.y / Q.z ^ 3 := hy
        _ = Q.y * (Q.z⁻¹ * Q.z⁻¹ * Q.z⁻¹) := by ring

end G2

/-- The factor that one pair adds to the product of the pairing check.

A pair with a point at infinity adds no factor. -/
def pairFactor (pq : G1 × G2) : Option Fp12 :=
  if pq.1.isInfinity || pq.2.isInfinity then none
  else some (millerLoop blsX pq.2.toAffine pq.1.toAffine).conjugate

/-- The loop of the pairing check, as a fold over the factors of the pairs. -/
private theorem forIn_eq_foldl (l : List (G1 × G2)) (acc : Fp12) :
    (forIn (m := Id) l acc fun x r =>
        match x with
        | (p, q) =>
          if (p.isInfinity || q.isInfinity) = true then pure (ForInStep.yield r)
          else pure (ForInStep.yield (r * (millerLoop blsX q.toAffine p.toAffine).conjugate))) =
      (l.filterMap pairFactor).foldl (· * ·) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons pq l ih =>
    obtain ⟨p, q⟩ := pq
    rw [List.forIn_cons, List.filterMap_cons]
    unfold pairFactor
    by_cases h : (p.isInfinity || q.isInfinity) = true
    · simp only [h, ↓reduceIte]
      exact ih acc
    · simp only [h, Bool.false_eq_true, ↓reduceIte, List.foldl_cons]
      exact ih _

/-- The pairing check is the final exponentiation of the product of the factors, in order. -/
theorem pairingCheck_eq_finalExp_prod (pairs : Array (G1 × G2)) :
    pairingCheck pairs =
      (finalExponentiation ((pairs.toList.filterMap pairFactor).foldl (· * ·) Fp12.one)).isOne := by
  unfold pairingCheck
  rw [← forIn_eq_foldl, Array.forIn_toList]
  -- Only the monadic plumbing differs; the final exponentiation stays abstract, never unfolded.
  generalize (finalExponentiation : Fp12 → Fp12) = fe
  rfl

/-- Pairs whose points have the same group elements have the same factor. -/
theorem pairFactor_congr {p p' : G1} {q q' : G2}
    (hp : G1.Valid p) (hp' : G1.Valid p') (hpp : G1.toPoint p = G1.toPoint p')
    (hq : G2.Valid q) (hq' : G2.Valid q') (hqq : G2.toPoint q = G2.toPoint q') :
    pairFactor (p, q) = pairFactor (p', q') := by
  unfold pairFactor
  dsimp only
  rw [(G1.toAffine_congr hp hp' hpp).1, (G2.toAffine_congr hq hq' hqq).1,
    (G1.toAffine_congr hp hp' hpp).2, (G2.toAffine_congr hq hq' hqq).2]

/-- The pairing check depends only on the group elements of valid points. -/
theorem pairingCheck_congr {ps qs : Array (G1 × G2)} (hsize : ps.size = qs.size)
    (h : ∀ i (hi : i < ps.size),
      G1.Valid ps[i].1 ∧ G1.Valid (qs[i]'(hsize ▸ hi)).1 ∧
        G1.toPoint ps[i].1 = G1.toPoint (qs[i]'(hsize ▸ hi)).1 ∧
      G2.Valid ps[i].2 ∧ G2.Valid (qs[i]'(hsize ▸ hi)).2 ∧
        G2.toPoint ps[i].2 = G2.toPoint (qs[i]'(hsize ▸ hi)).2) :
    pairingCheck ps = pairingCheck qs := by
  have hmap : ps.toList.map pairFactor = qs.toList.map pairFactor := by
    apply List.ext_getElem (by simp [hsize])
    intro i hi _
    simp only [List.length_map, Array.length_toList] at hi
    obtain ⟨hp, hp', hpp, hq, hq', hqq⟩ := h i hi
    simpa using pairFactor_congr hp hp' hpp hq hq' hqq
  -- Both sides drop the missing factors of the same list.
  have hid : ∀ l : List (G1 × G2), l.filterMap pairFactor = (l.map pairFactor).filterMap id :=
    fun l => by rw [List.filterMap_map]; rfl
  rw [pairingCheck_eq_finalExp_prod, pairingCheck_eq_finalExp_prod, hid, hid, hmap]

/-- Appending pairs that each hold a point at infinity does not change the pairing check. -/
theorem pairingCheck_append_infinity (ps qs : Array (G1 × G2))
    (h : ∀ pq ∈ qs, (pq.1.isInfinity || pq.2.isInfinity) = true) :
    pairingCheck (ps ++ qs) = pairingCheck ps := by
  have hnil : qs.toList.filterMap pairFactor = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro pq hpq
    simp [pairFactor, h pq (Array.mem_toList_iff.mp hpq)]
  rw [pairingCheck_eq_finalExp_prod, pairingCheck_eq_finalExp_prod, Array.toList_append,
    List.filterMap_append, hnil, List.append_nil]

end EthLib.Cryptography.Bls
