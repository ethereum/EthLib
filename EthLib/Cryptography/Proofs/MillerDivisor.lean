module

public import EthLib.Cryptography.Proofs.MillerFunction

/-!
# Proofs: the ideals of the lines of Miller's algorithm

The coordinate ring of a Weierstrass curve is `F[X, Y]` modulo the curve equation.

The ideal of a finite point `(x, y)` is `⟨X - x, Y - y⟩`, and the ideal of `O` is the whole ring.

An element of the ring vanishes at a point exactly when it lies in the ideal of the point.

The line through `T` and `S` meets the curve at `T`, `S` and `-(T + S)`.

So the principal ideal of the line is the product of the ideals of these three points.

So the function `g_{T,S}` has the fractional ideal of `T` times that of `S` over that of `T + S`.

See Miller, "The Weil Pairing, and Its Efficient Calculation", J. Cryptology 17 (2004).

These are Proposition 2 and Lemma 1 of its Section 4.1, for the affine points.

The poles at `O` are not part of these ideals, since `O` is not an affine point.
-/

@[expose] public section

namespace EthLib.Cryptography.Miller

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  Ideal
open scoped nonZeroDivisors

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-! ## Evaluation at a point -/

/-- Evaluation of the coordinate ring at a pair `(x, y)` on the curve. -/
noncomputable def evalAt {x y : F} (h : W.Equation x y) : W.CoordinateRing →+* F :=
  AdjoinRoot.lift (evalRingHom x) y (by rw [eval₂_evalRingHom]; exact h)

variable {W}

/-- The value of the class of a polynomial is the polynomial at `(x, y)`. -/
theorem evalAt_mk {x y : F} (h : W.Equation x y) (p : F[X][X]) :
    evalAt W h (AdjoinRoot.mk W.polynomial p) = p.evalEval x y := by
  rw [evalAt, AdjoinRoot.lift_mk, eval₂_evalRingHom]

/-- The value of `X - t` is `x - t`. -/
theorem evalAt_XClass {x y : F} (h : W.Equation x y) (t : F) :
    evalAt W h (XClass W t) = x - t := by
  rw [XClass, evalAt_mk]
  simp [evalEval]

/-- The value of `Y - q(X)` is `y - q(x)`. -/
theorem evalAt_YClass {x y : F} (h : W.Equation x y) (q : F[X]) :
    evalAt W h (YClass W q) = y - q.eval x := by
  rw [YClass, evalAt_mk]
  simp [evalEval]

/-- Modulo the ideal of a finite point, an element is congruent to its value there. -/
theorem quotient_mk_eq_evalAt {x y : F} (h : W.Equation x y) (a : W.CoordinateRing) :
    Ideal.Quotient.mk (XYIdeal W x (C y)) a = algebraMap F _ (evalAt W h a) := by
  have hX : XClass W x ∈ XYIdeal W x (C y) := subset_span (Set.mem_insert _ _)
  have hY : YClass W (C y) ∈ XYIdeal W x (C y) := subset_span (Set.mem_insert_of_mem _ rfl)
  have hc (c : F) : algebraMap F (W.CoordinateRing ⧸ XYIdeal W x (C y)) c =
      Ideal.Quotient.mk _ (AdjoinRoot.mk W.polynomial (C (C c))) := rfl
  have hext : Ideal.Quotient.mk (XYIdeal W x (C y)) = (algebraMap F _).comp (evalAt W h) := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, AdjoinRoot.of, evalAt_mk, hc]
        simp [evalEval]
      · simp only [RingHom.comp_apply, AdjoinRoot.of, evalAt_mk, hc]
        rw [Ideal.Quotient.eq]
        simpa [evalEval, XClass] using hX
    · simp only [RingHom.comp_apply, AdjoinRoot.root, evalAt_mk, hc]
      rw [Ideal.Quotient.eq]
      simpa [evalEval, YClass] using hY
  rw [hext, RingHom.comp_apply]

/-- An element vanishes at a finite point exactly when it lies in the ideal of the point. -/
theorem evalAt_eq_zero_iff {x y : F} (h : W.Equation x y) (a : W.CoordinateRing) :
    evalAt W h a = 0 ↔ a ∈ XYIdeal W x (C y) := by
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, quotient_mk_eq_evalAt h, ha, map_zero]
  · have hle : XYIdeal W x (C y) ≤ RingHom.ker (evalAt W h) := by
      rw [XYIdeal, span_le]
      rintro b (rfl | rfl)
      · simp [evalAt_XClass]
      · simp [evalAt_YClass]
    exact hle ha

/-! ## The ideal of a line -/

variable (W)

/-- The ideal `⟨X - x, Y - y⟩` of a finite point `(x, y)`, and the whole ring for `O`. -/
noncomputable def pointIdeal : W.Point → Ideal W.CoordinateRing
  | .zero => ⊤
  | .some x y _ => XYIdeal W x (C y)

@[simp] theorem pointIdeal_zero : pointIdeal W 0 = ⊤ := rfl

/-- The ideal of a point as an invertible fractional ideal, with `1` for `O`. -/
noncomputable def pointUnit : W.Point → (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ
  | .zero => 1
  | .some _ _ h => XYIdeal' h

variable {W}

@[simp] theorem pointUnit_zero : pointUnit W 0 = 1 := rfl

/-- The invertible fractional ideal of a point is its ideal. -/
theorem coe_pointUnit (P : W.Point) :
    (pointUnit W P : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) = pointIdeal W P := by
  cases P
  · rw [pointIdeal, FractionalIdeal.coeIdeal_top]
    rfl
  · rfl

/-- The vertical through a finite point `R` has the ideal of `R` times the ideal of `-R`. -/
theorem span_XClass {x y : F} (h : W.Nonsingular x y) :
    span {XClass W x} = pointIdeal W (.some x y h) * pointIdeal W (-.some x y h) := by
  rw [Point.neg_some, pointIdeal, pointIdeal, mul_comm, XYIdeal_neg_mul h, XIdeal]

variable (W) [DecidableEq F]

/-- The line through `T` and `S` as an element of the coordinate ring.

It is `X - x` for a vertical through `(x, y)` and `l(X) - Y` for a line `Y = l(X)`. -/
noncomputable def lineElem : W.Point → W.Point → W.CoordinateRing
  | .zero, .zero => 1
  | .some x _ _, .zero => XClass W x
  | .zero, .some x _ _ => XClass W x
  | .some x₁ y₁ _, .some x₂ y₂ _ =>
    if x₁ = x₂ ∧ y₁ = W.negY x₂ y₂ then XClass W x₁
    else -YClass W (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂))

variable {W}

/-- At a point of the curve, the line of the ring takes the value of the line of the loop. -/
theorem evalAt_lineElem (T S : W.Point) {xp yp : F} (h : W.Equation xp yp) :
    evalAt W h (lineElem W T S) = line W T S xp yp := by
  cases T <;> cases S <;> simp only [lineElem, line, map_one, evalAt_XClass]
  split_ifs
  · rw [evalAt_XClass]
  · rw [map_neg, evalAt_YClass, linePolynomial]
    simp only [eval_add, eval_mul, eval_C, eval_sub, eval_X]
    ring

/-- No line is zero in the coordinate ring. -/
theorem lineElem_ne_zero (T S : W.Point) : lineElem W T S ≠ 0 := by
  cases T <;> cases S <;> simp only [lineElem, ne_eq, one_ne_zero, not_false_eq_true,
    XClass_ne_zero]
  split_ifs
  · exact XClass_ne_zero _
  · exact neg_ne_zero.mpr (YClass_ne_zero _)

/-- The line through `T` and `S` generates the product of the ideals of `T`, `S` and `-(T + S)`.

This is Proposition 2 of Miller (2004), Section 4.1, without the pole at `O`. -/
theorem span_lineElem (T S : W.Point) :
    span {lineElem W T S} = pointIdeal W T * pointIdeal W S * pointIdeal W (-(T + S)) := by
  rcases T with _ | ⟨x₁, y₁, h₁⟩ <;> rcases S with _ | ⟨x₂, y₂, h₂⟩ <;>
    try simp only [← Point.zero_def, zero_add, add_zero]
  · simp [lineElem, pointIdeal]
  · rw [show lineElem W 0 (.some x₂ y₂ h₂) = XClass W x₂ from rfl, span_XClass h₂,
      pointIdeal_zero, top_mul]
  · rw [show lineElem W (.some x₁ y₁ h₁) 0 = XClass W x₁ from rfl, span_XClass h₁,
      pointIdeal_zero, mul_top]
  · by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
    · rw [Point.add_of_Y_eq hxy.1 hxy.2, neg_zero, pointIdeal_zero, mul_top, lineElem,
        ite_eq_left hxy]
      obtain ⟨rfl, rfl⟩ := hxy
      rw [span_XClass h₂, mul_comm]
      rfl
    · rw [Point.add_some hxy, Point.neg_some, lineElem, ite_eq_right hxy, span_singleton_neg]
      simp only [pointIdeal]
      apply (span_singleton_mul_right_inj (XClass_ne_zero (W' := W)
        (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)))).mp
      change XIdeal W _ * YIdeal W _ = XIdeal W _ * _
      rw [← mul_assoc, XYIdeal_mul_XYIdeal h₁.1 h₂.1 hxy,
        ← XYIdeal_neg_mul (nonsingular_add h₁ h₂ hxy)]
      ac_rfl

/-! ## Fractional ideals in the function field -/

variable (W)

/-- Miller's function `g_{T,S} = L_{T,S} / L_{T+S,-(T+S)}`, in the function field. -/
noncomputable def lineRatioElem (T S : W.Point) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (lineElem W T S) /
    algebraMap W.CoordinateRing W.FunctionField (lineElem W (T + S) (-(T + S)))

variable {W}

/-- The fractional ideal of the line through `T` and `S` is that of `T`, `S` and `-(T + S)`. -/
theorem spanSingleton_lineElem (T S : W.Point) :
    FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (algebraMap W.CoordinateRing W.FunctionField (lineElem W T S)) =
      ↑(pointUnit W T * pointUnit W S * pointUnit W (-(T + S))) := by
  rw [← FractionalIdeal.coeIdeal_span_singleton, span_lineElem, Units.val_mul, Units.val_mul,
    coe_pointUnit, coe_pointUnit, coe_pointUnit, FractionalIdeal.coeIdeal_mul,
    FractionalIdeal.coeIdeal_mul]

/-- The fractional ideal of `g_{T,S}` is the ideal of `T` times that of `S` over that of `T + S`.

This is Lemma 1 of Miller (2004), Section 4.1, without the point `O`. -/
theorem spanSingleton_lineRatioElem (T S : W.Point) :
    FractionalIdeal.spanSingleton W.CoordinateRing⁰ (lineRatioElem W T S) =
      ↑(pointUnit W T * pointUnit W S * (pointUnit W (T + S))⁻¹) := by
  have hy : algebraMap W.CoordinateRing W.FunctionField (lineElem W (T + S) (-(T + S))) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero (lineElem_ne_zero _ _))
  set v := pointUnit W (T + S) * pointUnit W (-(T + S)) * pointUnit W (-(T + S + -(T + S)))
  have hv := spanSingleton_lineElem (W := W) (T + S) (-(T + S))
  rw [← Units.mul_inv_cancel_right
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰ (lineRatioElem W T S)) v, ← hv,
    ← map_mul, lineRatioElem, div_mul_cancel₀ _ hy,
    spanSingleton_lineElem, ← Units.val_mul]
  congr 1
  simp only [v, add_neg_cancel, neg_zero, pointUnit_zero, mul_one]
  group

end EthLib.Cryptography.Miller
