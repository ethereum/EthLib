module

public import EthLib.Cryptography.Proofs.AltBn128.Fp2
public import EthLib.Cryptography.Proofs.AltBn128.Field
public import EthLib.Cryptography.Proofs.ShortWeierstrass
public import Mathlib.Tactic.Module

/-!
# Proofs: the group law of the twist

[EIP-197](https://eips.ethereum.org/EIPS/eip-197) §"Definition of the groups" puts `G_2` on a twist.

The twist is `y^2 = x^3 + b2` over `Fp2`, with `b2 = 3 / (9 + i)`.

Its addition follows the rule of `G_1`, which is the group law of Mathlib over any field.

Points on the twist and group elements correspond one to one.

The subgroup check of ECPAIRING accepts exactly the points whose order in the group divides `q`.

No theorem here states the order of the group of the twist.
-/

@[expose] public section

namespace EthLib.Cryptography.AltBn128

open WeierstrassCurve WeierstrassCurve.Affine

-- The kernel compares elements of `Fp`, whose modulus has 254 bits, deeper than the default.
set_option maxRecDepth 8000

/-- The twist as a Weierstrass curve over `Fp2`: `y^2 = x^3 + b2`. -/
abbrev twist : WeierstrassCurve.Affine Fp2 := ShortWeierstrass.curve 0 b2

/-- `b2 = 3 / (9 + i)` is not zero, since `3` and `9 + i` are not. -/
theorem b2_ne_zero : b2 ≠ 0 := by
  have h3 : (3 : Fp2) ≠ 0 := fun h => absurd (congrArg Fp2.c0 h) (by decide)
  have h9 : (⟨9, 1⟩ : Fp2) ≠ 0 := fun h => absurd (congrArg Fp2.c1 h) (by decide)
  have hb : b2 = 3 * (⟨9, 1⟩ : Fp2)⁻¹ := rfl
  rw [hb]
  exact mul_ne_zero h3 (inv_ne_zero h9)

/-- The discriminant of the twist is `-432 b2^2`, a unit, so the twist is smooth. -/
instance : twist.IsElliptic := by
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  have h432 : (432 : Fp2) ≠ 0 := fun h => absurd (congrArg Fp2.c0 h) (by decide)
  rw [ShortWeierstrass.discriminant_eq,
    show -16 * (4 * (0 : Fp2) ^ 3 + 27 * b2 ^ 2) = -432 * b2 ^ 2 by ring]
  exact mul_ne_zero (neg_ne_zero.mpr h432) (pow_ne_zero 2 b2_ne_zero)

/-- The equation of the twist. -/
theorem twist_equation_iff (x y : Fp2) : twist.Equation x y ↔ y * y = x * x * x + b2 := by
  rw [ShortWeierstrass.equation_iff, zero_mul, add_zero]

/-- On this smooth curve, every solution of the equation is a nonsingular point. -/
theorem twist_nonsingular_of {x y : Fp2} (h : y * y = x * x * x + b2) : twist.Nonsingular x y :=
  equation_iff_nonsingular.mp ((twist_equation_iff x y).mpr h)

namespace Point2

/-- The group element of a point.

A pair off the twist has none, and goes to `0`: every theorem assumes the point is on the twist. -/
def toPoint : Point2 → twist.Point
  | infinity => 0
  | affine x y => if h : y * y = x * x * x + b2 then .some _ _ (twist_nonsingular_of h) else 0

/-- The twist test, as an equation in `Fp2`. -/
theorem isOnCurve_affine (x y : Fp2) : (affine x y).isOnCurve = true ↔ y * y = x * x * x + b2 := by
  simp only [isOnCurve, beq_iff_eq]

theorem toPoint_affine {x y : Fp2} (h : (affine x y).isOnCurve = true) :
    toPoint (affine x y) = .some _ _ (twist_nonsingular_of ((isOnCurve_affine x y).mp h)) :=
  dite_eq_left ((isOnCurve_affine x y).mp h)

@[simp] theorem toPoint_infinity : toPoint infinity = 0 := rfl

/-! ## Addition -/

/-- A pair whose coordinates are those of a group element is on the twist, and is that element. -/
private theorem affine_of_eq {x3 y3 : Fp2} {P : twist.Point} (h : ∃ h3, P = .some x3 y3 h3) :
    (affine x3 y3).isOnCurve = true ∧ toPoint (affine x3 y3) = P := by
  obtain ⟨h3, rfl⟩ := h
  have hc : (affine x3 y3).isOnCurve = true :=
    (isOnCurve_affine x3 y3).mpr ((twist_equation_iff _ _).mp h3.1)
  exact ⟨hc, toPoint_affine hc⟩

/-- The rule for two points of the twist, both away from infinity. -/
private theorem add_affine {x1 y1 x2 y2 : Fp2} (h1 : (affine x1 y1).isOnCurve = true)
    (h2 : (affine x2 y2).isOnCurve = true) :
    (affine x1 y1 + affine x2 y2).isOnCurve = true
      ∧ toPoint (affine x1 y1 + affine x2 y2)
        = toPoint (affine x1 y1) + toPoint (affine x2 y2) := by
  have e1 := (isOnCurve_affine x1 y1).mp h1
  have e2 := (isOnCurve_affine x2 y2).mp h2
  rw [toPoint_affine h1, toPoint_affine h2]
  show (add (affine x1 y1) (affine x2 y2)).isOnCurve = true
    ∧ toPoint (add (affine x1 y1) (affine x2 y2)) = _
  simp only [add, Fp2.ofFp_two, Fp2.ofFp_three, Fp2.inv_eq_inv]
  by_cases hx : x1 = x2
  · subst hx
    rw [ite_eq_left rfl]
    by_cases hy : y2 = -y1
    · -- Opposite points sum to `O`.
      rw [ite_eq_left hy, ShortWeierstrass.add_of_y_eq_neg _ _ hy]
      exact ⟨rfl, rfl⟩
    · -- Same `x`, not opposite: the points are equal, and the tangent doubles.
      rw [ite_eq_right hy]
      have hy2 : y2 = y1 := by
        have : (y2 - y1) * (y2 + y1) = 0 := by linear_combination e2 - e1
        rcases mul_eq_zero.mp this with h | h
        · exact sub_eq_zero.mp h
        · exact absurd (eq_neg_of_add_eq_zero_left h) hy
      subst hy2
      exact affine_of_eq (ShortWeierstrass.add_self_of_y_ne _ hy (by ring) rfl rfl)
  · -- Different `x`: the chord.
    rw [ite_eq_right hx]
    exact affine_of_eq (ShortWeierstrass.add_of_x_ne _ _ hx rfl rfl rfl)

theorem isOnCurve_add {p q : Point2} (hp : p.isOnCurve = true) (hq : q.isOnCurve = true) :
    (p + q).isOnCurve = true := by
  cases p with
  | infinity => exact hq
  | affine x1 y1 =>
    cases q with
    | infinity => exact hp
    | affine x2 y2 => exact (add_affine hp hq).1

theorem toPoint_add {p q : Point2} (hp : p.isOnCurve = true) (hq : q.isOnCurve = true) :
    toPoint (p + q) = toPoint p + toPoint q := by
  cases p with
  | infinity => exact (zero_add _).symm
  | affine x1 y1 =>
    cases q with
    | infinity => exact (add_zero _).symm
    | affine x2 y2 => exact (add_affine hp hq).2

/-! ## Scalar multiplication -/

theorem isOnCurve_mulBits (fuel k : Nat) {p : Point2} (hp : p.isOnCurve = true) :
    (mulBits fuel k p).isOnCurve = true := by
  induction fuel generalizing k p with
  | zero => rfl
  | succ fuel ih =>
    have hrest := ih (k / 2) (isOnCurve_add hp hp)
    simp only [mulBits]
    split
    · exact isOnCurve_add hp hrest
    · exact hrest

/-- Double and add computes `k P`, when `k < 2^fuel`. -/
theorem toPoint_mulBits (fuel k : Nat) {p : Point2} (hp : p.isOnCurve = true) (hk : k < 2 ^ fuel) :
    toPoint (mulBits fuel k p) = k • toPoint p := by
  induction fuel generalizing k p with
  | zero =>
    obtain rfl : k = 0 := by simpa using hk
    simp [mulBits]
  | succ fuel ih =>
    have hk2 : k / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at hk; omega
    have hrest := ih (k / 2) (isOnCurve_add hp hp) hk2
    rw [toPoint_add hp hp] at hrest
    simp only [mulBits]
    split
    · -- An odd `k` is `2 (k / 2) + 1`.
      rw [toPoint_add hp (isOnCurve_mulBits fuel _ (isOnCurve_add hp hp)), hrest]
      conv_rhs => rw [show k = 2 * (k / 2) + 1 by omega]
      module
    · -- An even `k` is `2 (k / 2)`.
      rw [hrest]
      conv_rhs => rw [show k = 2 * (k / 2) by omega]
      module

/-! ## Points and group elements correspond -/

/-- Two points on the twist with the same group element are equal. -/
theorem toPoint_inj {p q : Point2} (hp : p.isOnCurve = true) (hq : q.isOnCurve = true) :
    toPoint p = toPoint q ↔ p = q := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  cases p with
  | infinity =>
    cases q with
    | infinity => rfl
    | affine x y => rw [toPoint_affine hq] at h; cases h
  | affine x1 y1 =>
    cases q with
    | infinity => rw [toPoint_affine hp] at h; cases h
    | affine x2 y2 =>
      rw [toPoint_affine hp, toPoint_affine hq, Affine.Point.some.injEq] at h
      rw [h.1, h.2]

/-- Only the point at infinity goes to `0`. -/
theorem toPoint_eq_zero {p : Point2} (hp : p.isOnCurve = true) : toPoint p = 0 ↔ p = infinity :=
  toPoint_inj (q := infinity) hp rfl

/-- Every group element is the element of a point on the twist. -/
theorem toPoint_surjective (P : twist.Point) :
    ∃ p : Point2, p.isOnCurve = true ∧ toPoint p = P := by
  cases P with
  | zero => exact ⟨infinity, rfl, rfl⟩
  | some x y h =>
    have hc : (affine x y).isOnCurve = true :=
      (isOnCurve_affine x y).mpr ((twist_equation_iff x y).mp h.1)
    exact ⟨affine x y, hc, toPoint_affine hc⟩

/-! ## The subgroup check of ECPAIRING -/

/-- On the twist, `q Q = O` by double and add exactly when `q` kills the group element of `Q`.

So the subgroup check of ECPAIRING accepts exactly the points whose order divides `q`. -/
theorem mulBits_order_eq_infinity_iff {p : Point2} (hp : p.isOnCurve = true) :
    mulBits 256 Fr.modulus p = infinity ↔ Fr.modulus • toPoint p = 0 := by
  rw [← toPoint_eq_zero (isOnCurve_mulBits _ _ hp), toPoint_mulBits _ _ hp (by decide)]

/-- The same check, as a divisibility of the order. -/
theorem mulBits_order_eq_infinity_iff_addOrderOf_dvd {p : Point2} (hp : p.isOnCurve = true) :
    mulBits 256 Fr.modulus p = infinity ↔ addOrderOf (toPoint p) ∣ Fr.modulus := by
  rw [mulBits_order_eq_infinity_iff hp, addOrderOf_dvd_iff_nsmul_eq_zero]

end Point2

end EthLib.Cryptography.AltBn128
