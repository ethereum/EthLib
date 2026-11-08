module

public import EthLib.Cryptography.Proofs.MillerFunction
public import EthLib.Cryptography.Proofs.ShortWeierstrass

/-!
# Proofs: scaling the coordinates of a short Weierstrass curve

Let `f` be a ring map from `F` to `K`, and let `u` be a nonzero element of `K`.

Take `y^2 = x^3 + c` over `F` and `y^2 = x^3 + d` over `K`, with `f c u^6 = d`.

Then `(x, y)` goes to `(f x u^2, f y u^3)` on the second curve.

This map of points is an injective group homomorphism.

A sextic untwist is such a map, and so is the Frobenius map of a curve over the prime field.

The line of Miller's algorithm through two images has the image of the slope times `u`.

A point with `x = 0` on `y^2 = x^3 + c` has order 3.
-/

@[expose] public section

namespace EthLib.Cryptography.ShortWeierstrass

open WeierstrassCurve WeierstrassCurve.Affine

section Scaling

variable {F K : Type*} [Field F] [Field K] (f : F →+* K) (u : K)

/-- The image of a point of the first curve satisfies the equation of the second. -/
theorem scaled_equation {c : F} {d : K} (hc : f c * u ^ 6 = d) {x y : F}
    (h : (curve 0 c).Equation x y) : (curve 0 d).Equation (f x * u ^ 2) (f y * u ^ 3) := by
  rw [equation_iff] at h ⊢
  have he := congrArg f h
  simp only [map_mul, map_add, zero_mul, add_zero] at he
  rw [← hc]
  linear_combination u ^ 6 * he

/-- A pair whose image satisfies the equation of the second curve satisfies that of the first. -/
theorem equation_of_scaled (hu : u ≠ 0) {c : F} {d : K} (hc : f c * u ^ 6 = d) {x y : F}
    (h : (curve 0 d).Equation (f x * u ^ 2) (f y * u ^ 3)) : (curve 0 c).Equation x y := by
  rw [equation_iff] at h ⊢
  apply f.injective
  have h0 : (f (y * y) - f (x * x * x + 0 * x + c)) * u ^ 6 = 0 := by
    rw [← hc] at h
    simp only [map_mul, map_add, zero_mul, add_zero]
    linear_combination h
  rw [mul_eq_zero, sub_eq_zero] at h0
  exact h0.resolve_right (pow_ne_zero 6 hu)

/-- The image of a nonsingular point is nonsingular. -/
theorem scaled_nonsingular (hu : u ≠ 0) {c : F} {d : K} (hc : f c * u ^ 6 = d) {x y : F}
    (h : (curve 0 c).Nonsingular x y) : (curve 0 d).Nonsingular (f x * u ^ 2) (f y * u ^ 3) := by
  rw [nonsingular_iff'] at h ⊢
  refine ⟨scaled_equation f u hc h.1, ?_⟩
  simp only [curve, zero_mul, mul_zero, add_zero, zero_sub, neg_ne_zero] at h ⊢
  rcases h.2 with h2 | h2
  · left
    have hx := (map_ne_zero f).mpr h2
    rw [map_mul, map_pow, map_ofNat] at hx
    rw [show 3 * (f x * u ^ 2) ^ 2 = 3 * f x ^ 2 * u ^ 4 by ring]
    exact mul_ne_zero hx (pow_ne_zero 4 hu)
  · right
    have hy := (map_ne_zero f).mpr h2
    rw [map_mul, map_ofNat] at hy
    rw [show 2 * (f y * u ^ 3) = 2 * f y * u ^ 3 by ring]
    exact mul_ne_zero hy (pow_ne_zero 3 hu)

variable {u}

theorem scaled_x_eq_iff (hu : u ≠ 0) (x t : F) : f x * u ^ 2 = f t * u ^ 2 ↔ x = t := by
  rw [mul_left_inj' (pow_ne_zero 2 hu), f.injective.eq_iff]

theorem scaled_y_neg_eq_iff (hu : u ≠ 0) (y z : F) : f y * u ^ 3 = -(f z * u ^ 3) ↔ y = -z := by
  rw [← neg_mul, ← map_neg, mul_left_inj' (pow_ne_zero 3 hu), f.injective.eq_iff]

variable [DecidableEq F] [DecidableEq K]

/-- The slope through two images is the image of the slope, times `u`. -/
theorem scaled_slope (hu : u ≠ 0) (c : F) (d : K) (x t y z : F) :
    (curve 0 d).slope (f x * u ^ 2) (f t * u ^ 2) (f y * u ^ 3) (f z * u ^ 3) =
      f ((curve 0 c).slope x t y z) * u := by
  simp only [slope, negY_eq, scaled_x_eq_iff f hu, scaled_y_neg_eq_iff f hu]
  simp only [curve, zero_mul, mul_zero, add_zero, sub_zero]
  by_cases hx : x = t
  · subst t
    rw [ite_eq_left rfl, ite_eq_left rfl]
    by_cases hy : y = -z
    · rw [ite_eq_left hy, ite_eq_left hy, map_zero, zero_mul]
    · rw [ite_eq_right hy, ite_eq_right hy]
      simp only [map_div₀, map_mul, map_pow, map_ofNat, map_sub, map_neg]
      field_simp
  · rw [ite_eq_right hx, ite_eq_right hx]
    simp only [map_div₀, map_sub]
    have h1 : f x - f t ≠ 0 := sub_ne_zero.mpr fun h => hx (f.injective h)
    field_simp

omit [DecidableEq F] [DecidableEq K] in
theorem scaled_addX (c : F) (d : K) (x t m : F) :
    (curve 0 d).addX (f x * u ^ 2) (f t * u ^ 2) (f m * u) =
      f ((curve 0 c).addX x t m) * u ^ 2 := by
  simp only [addX, curve, zero_mul, add_zero, sub_zero, map_sub, map_pow]
  ring

omit [DecidableEq F] [DecidableEq K] in
theorem scaled_addY (c : F) (d : K) (x t y m : F) :
    (curve 0 d).addY (f x * u ^ 2) (f t * u ^ 2) (f y * u ^ 3) (f m * u) =
      f ((curve 0 c).addY x t y m) * u ^ 3 := by
  simp only [addY, negY, negAddY, addX, curve, zero_mul, add_zero, sub_zero, map_neg, map_add,
    map_mul, map_sub, map_pow]
  ring

variable (hu : u ≠ 0) {c : F} {d : K} (hc : f c * u ^ 6 = d)

/-- The point `(f x u^2, f y u^3)` of the image of `(x, y)`, and `O` for `O`. -/
noncomputable def scaledPoint : (curve 0 c).Point → (curve 0 d).Point
  | .zero => 0
  | .some x y h => .some (f x * u ^ 2) (f y * u ^ 3) (scaled_nonsingular f u hu hc h)

include hu in
theorem scaledPoint_add (P Q : (curve 0 c).Point) :
    scaledPoint f hu hc (P + Q) = scaledPoint f hu hc P + scaledPoint f hu hc Q := by
  cases P with
  | zero => rfl
  | some x y hp =>
    cases Q with
    | zero => rfl
    | some t z hq =>
      by_cases hxy : x = t ∧ y = (curve 0 c).negY t z
      · rw [Point.add_of_Y_eq hxy.1 hxy.2]
        simp only [scaledPoint]
        have hsy : f y * u ^ 3 = (curve 0 d).negY (f t * u ^ 2) (f z * u ^ 3) := by
          rw [negY_eq]
          exact (scaled_y_neg_eq_iff f hu y z).mpr (by simpa only [negY_eq] using hxy.2)
        rw [Point.add_of_Y_eq (congrArg (fun x => f x * u ^ 2) hxy.1) hsy]
      · have hscaled : ¬(f x * u ^ 2 = f t * u ^ 2 ∧
            f y * u ^ 3 = (curve 0 d).negY (f t * u ^ 2) (f z * u ^ 3)) := by
          simp only [negY_eq, scaled_x_eq_iff f hu, scaled_y_neg_eq_iff f hu]
          simpa only [negY_eq] using hxy
        rw [Point.add_some hxy]
        simp only [scaledPoint]
        rw [Point.add_some hscaled, Point.some.injEq]
        simp only [scaled_slope f hu c d, scaled_addX f c d, scaled_addY f c d, and_self]

/-- The scaling of coordinates, as a group homomorphism. -/
noncomputable def scaledHom : (curve 0 c).Point →+ (curve 0 d).Point where
  toFun := scaledPoint f hu hc
  map_zero' := rfl
  map_add' := scaledPoint_add f hu hc

theorem scaledHom_apply (P : (curve 0 c).Point) : scaledHom f hu hc P = scaledPoint f hu hc P :=
  rfl

theorem scaledHom_injective : Function.Injective (scaledHom f hu hc) := by
  intro P Q h
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some _ _ _ => cases h
  | some x y hp =>
    cases Q with
    | zero => cases h
    | some t z hq =>
      have hs : f x * u ^ 2 = f t * u ^ 2 ∧ f y * u ^ 3 = f z * u ^ 3 := Point.some.inj h
      have hx := (scaled_x_eq_iff f hu x t).mp hs.1
      have hy : y = z := f.injective ((mul_left_inj' (pow_ne_zero 3 hu)).mp hs.2)
      subst t; subst z
      rfl

/-- Miller's line through the images of two finite points, at `(xp, yp)`.

It is the vertical through the first image when the points are opposite.

Otherwise its slope is the image of the slope times `u`. -/
theorem line_scaledHom_some {x₁ y₁ x₂ y₂ : F} (h₁ : (curve 0 c).Nonsingular x₁ y₁)
    (h₂ : (curve 0 c).Nonsingular x₂ y₂) (xp yp : K) :
    Miller.line (curve 0 d) (scaledHom f hu hc (.some x₁ y₁ h₁))
        (scaledHom f hu hc (.some x₂ y₂ h₂)) xp yp =
      if x₁ = x₂ ∧ y₁ = -y₂ then xp - f x₁ * u ^ 2
      else f ((curve 0 c).slope x₁ x₂ y₁ y₂) * u * (xp - f x₁ * u ^ 2) + f y₁ * u ^ 3 - yp := by
  simp only [scaledHom_apply, scaledPoint, Miller.line, negY_eq, scaled_x_eq_iff f hu,
    scaled_y_neg_eq_iff f hu, scaled_slope f hu c d]

/-- Miller's line through `O` and the image of a finite point is the vertical through it. -/
theorem line_zero_scaledHom_some {x y : F} (h : (curve 0 c).Nonsingular x y) (xp yp : K) :
    Miller.line (curve 0 d) 0 (scaledHom f hu hc (.some x y h)) xp yp = xp - f x * u ^ 2 :=
  rfl

end Scaling

section Inflection

variable {F : Type*} [Field F] [DecidableEq F] {c : F}

/-- A point with `x = 0` doubles to its opposite, so three times it is `O`.

The tangent there is horizontal, and `x = 0` is a double root of `x^3 - (y^2 - c)`. -/
theorem three_nsmul_some_zero {y : F} (h : (curve 0 c).Nonsingular 0 y) :
    3 • (Point.some 0 y h : (curve 0 c).Point) = 0 := by
  have hy : y ≠ (curve 0 c).negY 0 y := by
    rw [nonsingular_iff'] at h
    rw [negY_eq]
    intro hy
    simp only [curve, zero_mul, mul_zero, add_zero, zero_sub, neg_ne_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
    exact (h.2.resolve_left (by simp)) (by linear_combination hy)
  have h2 : (Point.some 0 y h : (curve 0 c).Point) + .some 0 y h = -(.some 0 y h) := by
    rw [Point.add_self_of_Y_ne hy, Point.neg_some, Point.some.injEq]
    have hs : (curve 0 c).slope 0 0 y y = 0 := by
      rw [slope_of_Y_ne rfl hy]
      simp [curve]
    simp only [addX, addY, negAddY, negY, hs]
    simp only [curve]
    constructor <;> ring
  rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, two_nsmul, h2, one_nsmul, neg_add_cancel]

/-- Let `β` be a cube root of unity other than `1`.

Then `(x, y)`, `(β x, y)` and `(β^2 x, y)` lie on the line `Y = y`, so they sum to `O`.

When `x = 0` the three points are one point, of order 3. -/
theorem some_add_some_add_some {β x y : F} (hβ : 1 + β + β ^ 2 = 0) (hβ1 : β ≠ 1)
    (h₁ : (curve 0 c).Nonsingular x y) (h₂ : (curve 0 c).Nonsingular (β * x) y)
    (h₃ : (curve 0 c).Nonsingular (β ^ 2 * x) y) :
    Point.some x y h₁ + Point.some (β * x) y h₂ + Point.some (β ^ 2 * x) y h₃ = 0 := by
  by_cases hx : x = 0
  · subst hx
    have he (t : F) (ht : t = 0) (h : (curve 0 c).Nonsingular t y) :
        (Point.some t y h : (curve 0 c).Point) = .some 0 y h₁ := by
      subst ht
      rfl
    rw [he _ (mul_zero β) h₂, he _ (mul_zero _) h₃, ← two_nsmul, ← succ_nsmul]
    exact three_nsmul_some_zero h₁
  · have hne : x ≠ β * x := by
      intro h
      have : (1 - β) * x = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h' | h'
      · exact hβ1 (by linear_combination -h')
      · exact hx h'
    obtain ⟨h₄, he⟩ := add_of_x_ne h₁ h₂ hne (l := 0) (x3 := β ^ 2 * x) (y3 := -y)
      (by simp) (by linear_combination x * hβ) (by ring)
    rw [he]
    exact add_of_y_eq_neg h₄ h₃ (neg_neg y).symm

end Inflection

end EthLib.Cryptography.ShortWeierstrass
