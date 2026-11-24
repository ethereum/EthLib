module

public import EthLib.Cryptography.Secp256k1.Curve
public import EthLib.Cryptography.Proofs.Secp256k1.Field
public import EthLib.Cryptography.Proofs.Secp256k1.Inverse
public import EthLib.Cryptography.Proofs.Jacobian
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Proofs: the group law of secp256k1

The addition rule of SEC 1 v2 §2.2.1 is the group law of the elliptic curve `y^2 = x^3 + 7`.

Each point of the specification maps to an element of that group.

On the curve, the points and the group elements correspond one to one.

So every fact about the group, such as associativity, holds for the specification's points.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

open WeierstrassCurve WeierstrassCurve.Affine

/-- secp256k1 as a Weierstrass curve over `ZMod p`: `y^2 = x^3 + 7`.

Mathlib proves that the points of this curve form a commutative group. -/
def curve : WeierstrassCurve.Affine (ZMod Fp.modulus) :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 7 }

/-- The discriminant of the curve is `-16 * 27 * 7^2`, a unit mod `p`, so the curve is smooth. -/
instance : curve.IsElliptic := by
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, curve]
  decide

/-- The equation of the curve, with `a = 0` and `b = 7`. -/
theorem equation_iff (x y : ZMod Fp.modulus) : curve.Equation x y ↔ y * y = x * x * x + 7 := by
  rw [Affine.equation_iff]
  simp only [curve]
  constructor <;> intro h <;> linear_combination h

/-- On this smooth curve, every solution of the equation is a nonsingular point. -/
theorem nonsingular_of {x y : ZMod Fp.modulus} (h : y * y = x * x * x + 7) : curve.Nonsingular x y :=
  equation_iff_nonsingular.mp ((equation_iff x y).mpr h)

/-- Mathlib's negation of `y` is plain negation on this curve, since `a_1 = a_3 = 0`. -/
@[simp] theorem negY_eq (x y : ZMod Fp.modulus) : curve.negY x y = -y := by
  simp [Affine.negY, curve]

/-- secp256k1 is the short Weierstrass curve with `a = 0` and `b = 7`. -/
instance : (ShortWeierstrass.curve (0 : ZMod Fp.modulus) 7).IsElliptic :=
  inferInstanceAs curve.IsElliptic

@[simp] private theorem toZMod_two : Fp.toZMod 2 = 2 := by decide

@[simp] private theorem toZMod_three : Fp.toZMod 3 = 3 := by decide

private theorem toZMod_b : Fp.toZMod b = 7 := by decide

/-- The map of `Fp` into `ZMod p` keeps the operations of the rule, with `a = 0` and `b = 7`.

So the proofs of every short Weierstrass curve hold for secp256k1. -/
theorem embedding : ShortWeierstrass.Embedding Fp.toZMod (0 : ZMod Fp.modulus) 7 :=
  ⟨Fp.toZMod.injective, map_add _, map_sub _, map_mul _, map_neg _, map_zero _, toZMod_two,
    toZMod_three, Fp.toZMod_inv, map_zero _, toZMod_b⟩

namespace Point

/-- The group element of a point.

A pair off the curve has none, and goes to `0`.

The group-law theorems assume the point is on the curve. -/
def toPoint : Point → curve.Point := ShortWeierstrass.Point.toPoint 0 7 Fp.toZMod

/-- The curve test, as an equation in `ZMod p`. -/
theorem isOnCurve_affine (x y : Fp) :
    (affine x y).isOnCurve = true ↔ Fp.toZMod y * Fp.toZMod y = Fp.toZMod x * Fp.toZMod x * Fp.toZMod x + 7 := by
  rw [ShortWeierstrass.Point.isOnCurve_affine embedding, zero_mul, add_zero]

theorem toPoint_affine {x y : Fp} (h : (affine x y).isOnCurve = true) :
    toPoint (affine x y) = .some _ _ (nonsingular_of ((isOnCurve_affine x y).mp h)) :=
  ShortWeierstrass.Point.toPoint_affine embedding h

@[simp] theorem toPoint_infinity : toPoint infinity = 0 := rfl

/-! ## Negation

Negation is the group's, and stays on the curve.
-/

theorem isOnCurve_neg {p : Point} (h : p.isOnCurve = true) : (-p).isOnCurve = true :=
  ShortWeierstrass.Point.isOnCurve_neg embedding h

theorem toPoint_neg {p : Point} (h : p.isOnCurve = true) : toPoint (-p) = -toPoint p :=
  ShortWeierstrass.Point.toPoint_neg embedding h

/-! ## Addition

Addition is the group's, and stays on the curve.
-/

theorem isOnCurve_add {p q : Point} (hp : p.isOnCurve = true) (hq : q.isOnCurve = true) :
    (p + q).isOnCurve = true :=
  ShortWeierstrass.Point.isOnCurve_add embedding hp hq

theorem toPoint_add {p q : Point} (hp : p.isOnCurve = true) (hq : q.isOnCurve = true) :
    toPoint (p + q) = toPoint p + toPoint q :=
  ShortWeierstrass.Point.toPoint_add embedding hp hq

/-! ## Scalar multiplication

Double and add computes `k P`, and stays on the curve.
-/

private theorem toZ_eq (x : Fp) : Jacobian.toZ x = Fp.toZMod x :=
  ZMod.natCast_zmod_val (Fp.toZMod x)

private theorem two_ne_zero' : (2 : ZMod Fp.modulus) ≠ 0 := by decide

/-- A point of the curve has a Jacobian form on the curve, with the same group element. -/
theorem toJacobian_spec {p : Point} (hp : p.isOnCurve = true) :
    Jacobian.OnCurve 0 7 (toJacobian p) ∧
      (Jacobian.toPoint 0 7 (toJacobian p) : curve.Point) = toPoint p :=
  ShortWeierstrass.Point.toJacobian_spec embedding toZ_eq hp

/-- The point of a Jacobian form is its affine point, or the point at infinity. -/
theorem ofJacobian_eq (p : Jacobian Fp.modulus) :
    ofJacobian p = match p.toAffine with
      | none => infinity
      | some (x, y) => affine x y := by
  rw [ShortWeierstrass.Point.ofJacobian_eq]
  cases p.toAffine <;> rfl

/-- A Jacobian form on the curve gives a point of the curve, with the same group element. -/
theorem ofJacobian_spec {p : Jacobian Fp.modulus} (hp : Jacobian.OnCurve 0 7 p) :
    (ofJacobian p).isOnCurve = true ∧ toPoint (ofJacobian p) = Jacobian.toPoint 0 7 p :=
  ShortWeierstrass.Point.ofJacobian_spec embedding toZ_eq hp

/-- Reading the Montgomery form back is a change of field representation. -/
theorem toFin_embedding : Jacobian.Coords.Embedding (Montgomery.toFin : Fp.Montgomery → Fp) :=
  ⟨Montgomery.toFin_zero, Montgomery.toFin_one, Montgomery.toFin_add, Montgomery.toFin_sub,
    Montgomery.toFin_mul, Montgomery.toFin_injective⟩

/-- Normalizing in another representation gives the point of the form read back into `Fp`.

It needs the inverse of that representation to read as the inverse of `Fp`. -/
theorem ofCoords_map {F : Type} [OfNat F 0] [OfNat F 1] [Add F] [Sub F] [Mul F] [DecidableEq F]
    {f : F → Fp} (hf : Jacobian.Coords.Embedding f) {inv : F → F}
    (hinv : ∀ x, f (inv x) = Fin.inverse (f x)) (q : Jacobian.Coords F) :
    ofCoords inv f q = ofCoords Fin.inverse id (q.map f) :=
  ShortWeierstrass.Point.ofCoords_map hf hinv q

/-- Normalizing in Montgomery form gives the point of the form read back into `Fp`. -/
theorem ofMontgomeryCoords_eq (q : Jacobian.Coords Fp.Montgomery) :
    ofMontgomeryCoords q = ofJacobian (Jacobian.ofCoords (q.map Montgomery.toFin)) := by
  exact ofCoords_map toFin_embedding (fun x => Montgomery.toFin_inv x) q

/-- Reading back the Montgomery form of a point gives its Jacobian form. -/
theorem map_toMontgomeryCoords (p : Point) :
    (toMontgomeryCoords p).map Montgomery.toFin = (toJacobian p).toCoords := by
  show Jacobian.Coords.mk _ _ _ = Jacobian.Coords.mk _ _ _
  congr 1 <;> exact Montgomery.toFin_ofFin _

/-- The Montgomery form is a representation of `Fp` for double and add. -/
private theorem montgomery :
    ShortWeierstrass.Point.Representation Montgomery.ofFin Montgomery.inv Montgomery.toFin :=
  ⟨toFin_embedding, Montgomery.toFin_inv, Montgomery.toFin_ofFin⟩

private theorem toZ_a : Jacobian.toZ (Montgomery.toFin (0 : Fp.Montgomery)) = 0 := by
  rw [toFin_embedding.map_zero, toZ_eq, map_zero]

/-- Double and add in Montgomery form is double and add on `Fp`, for every input. -/
theorem mulBits_eq_jacobian (fuel k : Nat) (p : Point) :
    mulBits fuel k p = ofJacobian (Jacobian.mulBits 0 fuel k (toJacobian p)) := by
  rw [mulBits, ShortWeierstrass.Point.mulBits_eq_jacobian montgomery, toFin_embedding.map_zero]

theorem isOnCurve_mulBits (fuel k : Nat) {p : Point} (hp : p.isOnCurve = true) :
    (mulBits fuel k p).isOnCurve = true :=
  ShortWeierstrass.Point.isOnCurve_mulBits embedding toZ_eq montgomery toZ_a two_ne_zero' fuel k hp

/-- Double and add computes `k P`, when `k < 2^fuel`. -/
theorem toPoint_mulBits (fuel k : Nat) {p : Point} (hp : p.isOnCurve = true) (hk : k < 2 ^ fuel) :
    toPoint (mulBits fuel k p) = k • toPoint p :=
  ShortWeierstrass.Point.toPoint_mulBits embedding toZ_eq montgomery toZ_a two_ne_zero' fuel k hp hk

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

/-- A pair off the curve goes to `0`. -/
theorem toPoint_eq_zero_of_isOnCurve_eq_false {p : Point} (hp : p.isOnCurve = false) :
    toPoint p = 0 :=
  ShortWeierstrass.Point.toPoint_eq_zero_of_isOnCurve_eq_false embedding hp

/-- Every group element is the element of a point on the curve. -/
theorem toPoint_surjective (P : curve.Point) : ∃ p : Point, p.isOnCurve = true ∧ toPoint p = P :=
  ShortWeierstrass.Point.toPoint_surjective embedding Fp.toZMod.surjective P

end Point

end EthLib.Cryptography.Secp256k1
