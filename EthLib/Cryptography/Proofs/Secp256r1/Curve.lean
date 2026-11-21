module

public import EthLib.Cryptography.Secp256r1.Curve
public import EthLib.Cryptography.Proofs.Secp256r1.Field
public import EthLib.Cryptography.Proofs.ShortWeierstrass
public import EthLib.Cryptography.Proofs.Jacobian

/-!
# Proofs: the group law of secp256r1

The addition rule of SEC 1 v2 §2.2.1 is the group law of `y^2 = x^3 + a x + b` over `ZMod p`.

Each point of the specification maps to an element of that group.

Addition and scalar multiplication commute with that map, which is one to one on the curve.

The proofs are those of every short Weierstrass curve, for the map of `Fp` into `ZMod p`.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256r1

open WeierstrassCurve WeierstrassCurve.Affine

/-- secp256r1 as a Weierstrass curve over `ZMod p`: `y^2 = x^3 + a x + b`. -/
abbrev curve : WeierstrassCurve.Affine (ZMod Fp.modulus) := ShortWeierstrass.curve (Fp.toZMod a) (Fp.toZMod b)

/-- The discriminant `-16 (4 a^3 + 27 b^2)` is a unit mod `p`, so the curve is smooth. -/
instance : curve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by rw [ShortWeierstrass.discriminant_eq]; decide)⟩

/-- On this smooth curve, every solution of the equation is a nonsingular point. -/
theorem nonsingular_of {x y : ZMod Fp.modulus} (h : y * y = x * x * x + Fp.toZMod a * x + Fp.toZMod b) :
    curve.Nonsingular x y :=
  equation_iff_nonsingular.mp ((ShortWeierstrass.equation_iff x y).mpr h)

@[simp] private theorem toZMod_two : Fp.toZMod 2 = 2 := by decide

@[simp] private theorem toZMod_three : Fp.toZMod 3 = 3 := by decide

/-- The map of `Fp` into `ZMod p` keeps the operations of the rule, and the curve's `a` and `b`. -/
theorem embedding : ShortWeierstrass.Embedding Fp.toZMod (Fp.toZMod a) (Fp.toZMod b) :=
  ⟨Fp.toZMod.injective, map_add _, map_sub _, map_mul _, map_neg _, map_zero _, toZMod_two,
    toZMod_three, Fp.toZMod_inv, rfl, rfl⟩

namespace Point

/-- The group element of a point.

A pair off the curve has none, and goes to `0`.

The group-law theorems assume the point is on the curve. -/
def toPoint : Point → curve.Point := ShortWeierstrass.Point.toPoint _ _ Fp.toZMod

/-- The curve test, as an equation in `ZMod p`. -/
theorem isOnCurve_affine (x y : Fp) :
    (affine x y).isOnCurve = true ↔ Fp.toZMod y * Fp.toZMod y
      = Fp.toZMod x * Fp.toZMod x * Fp.toZMod x + Fp.toZMod a * Fp.toZMod x + Fp.toZMod b :=
  ShortWeierstrass.Point.isOnCurve_affine embedding x y

theorem toPoint_affine {x y : Fp} (h : (affine x y).isOnCurve = true) :
    toPoint (affine x y) = .some _ _ (nonsingular_of ((isOnCurve_affine x y).mp h)) :=
  ShortWeierstrass.Point.toPoint_affine embedding h

@[simp] theorem toPoint_infinity : toPoint infinity = 0 := rfl

/-- `(0, 0)` does not lie on the curve.

EIP-7951, Point of Infinity Encoding, encodes the point at infinity as `(0, 0)` for this reason. -/
theorem isOnCurve_affine_zero_zero : (affine 0 0).isOnCurve = false := by
  decide

/-! ## Addition -/

theorem isOnCurve_add {p q : Point} (hp : p.isOnCurve = true) (hq : q.isOnCurve = true) :
    (p + q).isOnCurve = true :=
  ShortWeierstrass.Point.isOnCurve_add embedding hp hq

theorem toPoint_add {p q : Point} (hp : p.isOnCurve = true) (hq : q.isOnCurve = true) :
    toPoint (p + q) = toPoint p + toPoint q :=
  ShortWeierstrass.Point.toPoint_add embedding hp hq

/-! ## Scalar multiplication -/

private theorem toZ_eq (x : Fp) : Jacobian.toZ x = Fp.toZMod x :=
  ZMod.natCast_zmod_val (Fp.toZMod x)

private theorem toZ_a : Jacobian.toZ (a : Fp) = Fp.toZMod a := toZ_eq _

private theorem two_ne_zero' : (2 : ZMod Fp.modulus) ≠ 0 := by decide

/-- A point of the curve has a Jacobian form on the curve, with the same group element. -/
theorem toJacobian_spec {p : Point} (hp : p.isOnCurve = true) :
    Jacobian.OnCurve (Fp.toZMod a) (Fp.toZMod b) (toJacobian p) ∧
      (Jacobian.toPoint (Fp.toZMod a) (Fp.toZMod b) (toJacobian p) : curve.Point) = toPoint p :=
  ShortWeierstrass.Point.toJacobian_spec embedding toZ_eq hp

/-- A Jacobian form on the curve gives a point of the curve, with the same group element. -/
theorem ofJacobian_spec {p : Jacobian Fp.modulus}
    (hp : Jacobian.OnCurve (Fp.toZMod a) (Fp.toZMod b) p) :
    (ofJacobian p).isOnCurve = true ∧
      toPoint (ofJacobian p) = Jacobian.toPoint (Fp.toZMod a) (Fp.toZMod b) p :=
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

theorem isOnCurve_mul (k : Fn) {p : Point} (hp : p.isOnCurve = true) : (mul k p).isOnCurve = true :=
  isOnCurve_mulBits 256 k.val hp

/-- Scalar multiplication computes `k P`, with the value of `k` below `n`. -/
theorem toPoint_mul (k : Fn) {p : Point} (hp : p.isOnCurve = true) :
    toPoint (mul k p) = k.val • toPoint p :=
  toPoint_mulBits 256 k.val hp (Nat.lt_trans k.isLt (by decide))

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

/-! ## Two products with shared doublings -/

theorem isOnCurve_mulAdd (k l : Fn) {p q : Point} (hp : p.isOnCurve = true)
    (hq : q.isOnCurve = true) : (mulAdd k p l q).isOnCurve = true :=
  (ofJacobian_spec (Jacobian.onCurve_mulAdd toZ_a two_ne_zero' 256 k.val l.val
    (toJacobian_spec hp).1 (toJacobian_spec hq).1)).1

/-- The shared chain computes `k P + l Q`, with the values of `k` and `l` below `n`. -/
theorem toPoint_mulAdd (k l : Fn) {p q : Point} (hp : p.isOnCurve = true)
    (hq : q.isOnCurve = true) :
    toPoint (mulAdd k p l q) = k.val • toPoint p + l.val • toPoint q := by
  have hJp := toJacobian_spec hp
  have hJq := toJacobian_spec hq
  rw [mulAdd, (ofJacobian_spec (Jacobian.onCurve_mulAdd toZ_a two_ne_zero' 256 k.val l.val
      hJp.1 hJq.1)).2,
    Jacobian.toPoint_mulAdd toZ_a two_ne_zero' 256 k.val l.val hJp.1 hJq.1
      (Nat.lt_trans k.isLt (by decide)) (Nat.lt_trans l.isLt (by decide))]
  exact congrArg₂ (k.val • · + l.val • ·) hJp.2 hJq.2

/-- On points of the curve, the shared chain gives the sum of the two products. -/
theorem mulAdd_eq (k l : Fn) {p q : Point} (hp : p.isOnCurve = true) (hq : q.isOnCurve = true) :
    mulAdd k p l q = mul k p + mul l q := by
  rw [← toPoint_inj (isOnCurve_mulAdd k l hp hq) (isOnCurve_add (isOnCurve_mul k hp)
    (isOnCurve_mul l hq)), toPoint_mulAdd k l hp hq, toPoint_add (isOnCurve_mul k hp)
    (isOnCurve_mul l hq), toPoint_mul k hp, toPoint_mul l hq]

end Point

end EthLib.Cryptography.Secp256r1
