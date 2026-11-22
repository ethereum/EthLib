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

/-- The identity of `Fp2` keeps the operations, the numerals and the inverse of the rule.

It sends the constants of the twist to `0` and `b2`. -/
theorem embedding : ShortWeierstrass.Embedding (id : Fp2 → Fp2) 0 b2 where
  injective := Function.injective_id
  map_add _ _ := rfl
  map_sub _ _ := rfl
  map_mul _ _ := rfl
  map_neg _ := rfl
  map_zero := rfl
  map_two := rfl
  map_three := rfl
  map_inv _ := rfl
  map_a := rfl
  map_b := rfl

/-- The group element of a point.

A pair off the twist has none, and goes to `0`: every theorem assumes the point is on the twist. -/
abbrev toPoint (p : Point2) : twist.Point := ShortWeierstrass.Point.toPoint 0 b2 id p

/-- The twist test, as an equation in `Fp2`. -/
theorem isOnCurve_affine (x y : Fp2) : (affine x y).isOnCurve = true ↔ y * y = x * x * x + b2 := by
  rw [ShortWeierstrass.Point.isOnCurve_affine embedding, id, id, zero_mul, add_zero]

theorem toPoint_affine {x y : Fp2} (h : (affine x y).isOnCurve = true) :
    toPoint (affine x y) = .some _ _ (twist_nonsingular_of ((isOnCurve_affine x y).mp h)) :=
  ShortWeierstrass.Point.toPoint_affine embedding h

@[simp] theorem toPoint_infinity : toPoint infinity = 0 := rfl

/-! ## Addition -/

theorem isOnCurve_add {p q : Point2} (hp : p.isOnCurve = true) (hq : q.isOnCurve = true) :
    (p + q).isOnCurve = true :=
  ShortWeierstrass.Point.isOnCurve_add embedding hp hq

theorem toPoint_add {p q : Point2} (hp : p.isOnCurve = true) (hq : q.isOnCurve = true) :
    toPoint (p + q) = toPoint p + toPoint q :=
  ShortWeierstrass.Point.toPoint_add embedding hp hq

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
    toPoint p = toPoint q ↔ p = q :=
  ShortWeierstrass.Point.toPoint_inj embedding hp hq

/-- Only the point at infinity goes to `0`. -/
theorem toPoint_eq_zero {p : Point2} (hp : p.isOnCurve = true) : toPoint p = 0 ↔ p = infinity :=
  toPoint_inj (q := infinity) hp rfl

/-- Every group element is the element of a point on the twist. -/
theorem toPoint_surjective (P : twist.Point) :
    ∃ p : Point2, p.isOnCurve = true ∧ toPoint p = P :=
  ShortWeierstrass.Point.toPoint_surjective embedding Function.surjective_id P

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
