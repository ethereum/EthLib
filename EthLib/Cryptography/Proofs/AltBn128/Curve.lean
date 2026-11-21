module

public import EthLib.Cryptography.AltBn128.Curve
public import EthLib.Cryptography.Proofs.AltBn128.Field
public import EthLib.Cryptography.Proofs.ShortWeierstrass
public import EthLib.Cryptography.Proofs.Jacobian

/-!
# Proofs: the group law of alt_bn128

[EIP-196](https://eips.ethereum.org/EIPS/eip-196) §"Specification" defines `y^2 = x^3 + 3`.

Mathlib proves that the points of this curve over `ZMod p` form a commutative group.

The addition rule of SEC 1 v2 §2.2.1 is that group law.

Points on the curve and group elements correspond one to one.

Addition, negation and double and add map to the group operations.

The proofs are those of every short Weierstrass curve, for the map of `Fp` into `ZMod p`.
-/

@[expose] public section

namespace EthLib.Cryptography.AltBn128

open WeierstrassCurve WeierstrassCurve.Affine

/-- alt_bn128 as a Weierstrass curve over `ZMod p`: `y^2 = x^3 + 3`. -/
abbrev curve : WeierstrassCurve.Affine (ZMod Fp.modulus) := ShortWeierstrass.curve 0 3

/-- The discriminant of the curve is `-16 * 27 * 3^2`, a unit mod `p`, so the curve is smooth. -/
instance : curve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by rw [ShortWeierstrass.discriminant_eq]; decide)⟩

/-- The equation of the curve, with `a = 0` and `b = 3`. -/
theorem equation_iff (x y : ZMod Fp.modulus) : curve.Equation x y ↔ y * y = x * x * x + 3 := by
  rw [ShortWeierstrass.equation_iff, zero_mul, add_zero]

/-- On this smooth curve, every solution of the equation is a nonsingular point. -/
theorem nonsingular_of {x y : ZMod Fp.modulus} (h : y * y = x * x * x + 3) : curve.Nonsingular x y :=
  ShortWeierstrass.nonsingular_of_eq (by rwa [zero_mul, add_zero])

/-- The negation of `y` in Mathlib is plain negation here, since `a_1 = a_3 = 0`. -/
@[simp] theorem negY_eq (x y : ZMod Fp.modulus) : curve.negY x y = -y :=
  ShortWeierstrass.negY_eq x y

@[simp] private theorem toZMod_two : Fp.toZMod 2 = 2 := by decide

@[simp] private theorem toZMod_three : Fp.toZMod 3 = 3 := by decide

private theorem toZMod_b : Fp.toZMod b = 3 := by decide

/-- The map of `Fp` into `ZMod p` keeps the operations of the rule, with `a = 0` and `b = 3`. -/
theorem embedding : ShortWeierstrass.Embedding Fp.toZMod (0 : ZMod Fp.modulus) 3 :=
  ⟨Fp.toZMod.injective, map_add _, map_sub _, map_mul _, map_neg _, map_zero _, toZMod_two,
    toZMod_three, Fp.toZMod_inv, map_zero _, toZMod_b⟩

namespace Point

/-- The group element of a point.

A pair off the curve has none, and goes to `0`.

The group-law theorems assume the point is on the curve. -/
def toPoint : Point → curve.Point := ShortWeierstrass.Point.toPoint 0 3 Fp.toZMod

/-- The curve test, as an equation in `ZMod p`. -/
theorem isOnCurve_affine (x y : Fp) :
    (affine x y).isOnCurve = true ↔ Fp.toZMod y * Fp.toZMod y = Fp.toZMod x * Fp.toZMod x * Fp.toZMod x + 3 := by
  rw [ShortWeierstrass.Point.isOnCurve_affine embedding, zero_mul, add_zero]

theorem toPoint_affine {x y : Fp} (h : (affine x y).isOnCurve = true) :
    toPoint (affine x y) = .some _ _ (nonsingular_of ((isOnCurve_affine x y).mp h)) :=
  ShortWeierstrass.Point.toPoint_affine embedding h

@[simp] theorem toPoint_infinity : toPoint infinity = 0 := rfl

/-! ## Negation -/

theorem isOnCurve_neg {p : Point} (h : p.isOnCurve = true) : p.neg.isOnCurve = true :=
  ShortWeierstrass.Point.isOnCurve_neg embedding h

theorem toPoint_neg {p : Point} (h : p.isOnCurve = true) : toPoint p.neg = -toPoint p :=
  ShortWeierstrass.Point.toPoint_neg embedding h

/-! ## Addition -/

theorem isOnCurve_add {p q : Point} (hp : p.isOnCurve = true) (hq : q.isOnCurve = true) :
    (p + q).isOnCurve = true :=
  ShortWeierstrass.Point.isOnCurve_add embedding hp hq

theorem toPoint_add {p q : Point} (hp : p.isOnCurve = true) (hq : q.isOnCurve = true) :
    toPoint (p + q) = toPoint p + toPoint q :=
  ShortWeierstrass.Point.toPoint_add embedding hp hq

/-! ## Scalar multiplication -/

private theorem two_ne_zero' : (2 : ZMod Fp.modulus) ≠ 0 := by decide

private theorem toZ_eq (x : Fp) : Jacobian.toZ x = Fp.toZMod x :=
  ZMod.natCast_zmod_val (Fp.toZMod x)

private theorem toZ_a : Jacobian.toZ (0 : Fp) = 0 := toZ_eq _

/-- A point of the curve has a Jacobian form on the curve, with the same group element. -/
theorem toJacobian_spec {p : Point} (hp : p.isOnCurve = true) :
    Jacobian.OnCurve (0) (3) (toJacobian p) ∧
      (Jacobian.toPoint (0) (3) (toJacobian p) : curve.Point) = toPoint p :=
  ShortWeierstrass.Point.toJacobian_spec embedding toZ_eq hp

/-- A Jacobian form on the curve gives a point of the curve, with the same group element. -/
theorem ofJacobian_spec {p : Jacobian Fp.modulus} (hp : Jacobian.OnCurve (0) (3) p) :
    (ofJacobian p).isOnCurve = true ∧ toPoint (ofJacobian p) = Jacobian.toPoint (0) (3) p :=
  ShortWeierstrass.Point.ofJacobian_spec embedding toZ_eq hp

theorem isOnCurve_mulBits (fuel k : Nat) {p : Point} (hp : p.isOnCurve = true) :
    (mulBits fuel k p).isOnCurve = true :=
  ShortWeierstrass.Point.isOnCurve_mulBits embedding toZ_eq
    ShortWeierstrass.Point.Representation.fin
    toZ_a two_ne_zero' fuel k hp

/-- Double and add computes `k P`, when `k < 2^fuel`. -/
theorem toPoint_mulBits (fuel k : Nat) {p : Point} (hp : p.isOnCurve = true) (hk : k < 2 ^ fuel) :
    toPoint (mulBits fuel k p) = k • toPoint p :=
  ShortWeierstrass.Point.toPoint_mulBits embedding toZ_eq
    ShortWeierstrass.Point.Representation.fin
    toZ_a two_ne_zero' fuel k hp hk

/-! ## Points and group elements correspond -/

/-- Two points on the curve with the same group element are equal. -/
theorem toPoint_inj {p q : Point} (hp : p.isOnCurve = true) (hq : q.isOnCurve = true) :
    toPoint p = toPoint q ↔ p = q :=
  ShortWeierstrass.Point.toPoint_inj embedding hp hq

/-- Only the point at infinity goes to `0`. -/
theorem toPoint_eq_zero {p : Point} (hp : p.isOnCurve = true) : toPoint p = 0 ↔ p = infinity :=
  ShortWeierstrass.Point.toPoint_eq_zero embedding hp

/-- Every group element is the element of a point on the curve. -/
theorem toPoint_surjective (P : curve.Point) : ∃ p : Point, p.isOnCurve = true ∧ toPoint p = P :=
  ShortWeierstrass.Point.toPoint_surjective embedding Fp.toZMod.surjective P

end Point

end EthLib.Cryptography.AltBn128
