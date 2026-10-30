import EthLib.Cryptography.Secp256k1.Curve
import EthLib.Cryptography.Proofs.Secp256k1.Field
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Proofs: the group law of secp256k1

The addition rule of SEC 1 v2 §2.2.1 is the group law of the elliptic curve `y^2 = x^3 + 7`.

Mathlib defines that curve over the field `ZMod p`, proves its points form a commutative group, and calls it `curve.Point`.

`toPoint` sends a point of the specification to that group.

- `toPoint_add`, `toPoint_neg`: addition and negation are the group's.
- `toPoint_mulBits`, `toPoint_mul`: double and add computes `k P`.
- `isOnCurve_add`, `isOnCurve_neg`, `isOnCurve_mul`: each operation stays on the curve.
- `toPoint_inj`, `toPoint_surjective`: points on the curve and group elements correspond one to one.

So every fact about the group, such as associativity, holds for the specification's points.
-/

namespace EthLib.Cryptography.Secp256k1

open WeierstrassCurve WeierstrassCurve.Affine

/-- secp256k1 as a Weierstrass curve over `ZMod p`: `y^2 = x^3 + 7`. -/
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

/-- `negY` on this curve is plain negation, since `a_1 = a_3 = 0`. -/
@[simp] theorem negY_eq (x y : ZMod Fp.modulus) : curve.negY x y = -y := by
  simp [Affine.negY, curve]

namespace Point

/-- The group element of a point.

A pair off the curve has none, and goes to `0`: every theorem assumes the point is on the curve. -/
def toPoint : Point → curve.Point
  | infinity => 0
  | affine x y =>
    if h : Fp.toZMod y * Fp.toZMod y = Fp.toZMod x * Fp.toZMod x * Fp.toZMod x + 7 then
      .some _ _ (nonsingular_of h)
    else 0

/-- The test `isOnCurve`, as an equation in `ZMod p`. -/
theorem isOnCurve_affine (x y : Fp) :
    (affine x y).isOnCurve = true ↔ Fp.toZMod y * Fp.toZMod y = Fp.toZMod x * Fp.toZMod x * Fp.toZMod x + 7 := by
  simp only [isOnCurve, beq_iff_eq]
  exact ⟨fun h => by rw [← map_mul, h]; rfl, fun h => Fp.toZMod.injective (by rw [map_mul, h]; rfl)⟩

theorem toPoint_affine {x y : Fp} (h : (affine x y).isOnCurve = true) :
    toPoint (affine x y) = .some _ _ (nonsingular_of ((isOnCurve_affine x y).mp h)) :=
  dite_eq_left ((isOnCurve_affine x y).mp h)

@[simp] theorem toPoint_infinity : toPoint infinity = 0 := rfl

/-! ## Negation -/

theorem isOnCurve_neg {p : Point} (h : p.isOnCurve = true) : (-p).isOnCurve = true := by
  cases p with
  | infinity => rfl
  | affine x y =>
    show (affine x (-y)).isOnCurve = true
    rw [isOnCurve_affine] at h ⊢
    simp only [Fp.toZMod_neg, neg_mul_neg]
    exact h

theorem toPoint_neg {p : Point} (h : p.isOnCurve = true) : toPoint (-p) = -toPoint p := by
  cases p with
  | infinity => simp [toPoint_infinity, show (-infinity : Point) = infinity from rfl]
  | affine x y =>
    show toPoint (affine x (-y)) = _
    rw [toPoint_affine h, toPoint_affine (isOnCurve_neg h), Affine.Point.neg_some]
    simp [curve]

/-! ## Addition -/

/-- Two points of the curve with the same `x` are equal or opposite. -/
private theorem y_eq_or_eq_neg {x y1 y2 : ZMod Fp.modulus} (h1 : y1 * y1 = x * x * x + 7)
    (h2 : y2 * y2 = x * x * x + 7) : y2 = y1 ∨ y2 = -y1 :=
  Fp.eq_or_eq_neg_of_mul_self (h2.trans h1.symm)

/-- A pair whose coordinates are those of a group element is on the curve, and is that element. -/
private theorem affine_of_eq {x3 y3 : Fp} {X Y : ZMod Fp.modulus} (hX : Fp.toZMod x3 = X)
    (hY : Fp.toZMod y3 = Y) (h : curve.Nonsingular X Y) :
    (affine x3 y3).isOnCurve = true ∧ toPoint (affine x3 y3) = .some X Y h := by
  subst hX hY
  have hc : (affine x3 y3).isOnCurve = true := (isOnCurve_affine x3 y3).mpr ((equation_iff _ _).mp h.1)
  exact ⟨hc, toPoint_affine hc⟩

@[simp] private theorem toZMod_two : Fp.toZMod 2 = 2 := by decide

@[simp] private theorem toZMod_three : Fp.toZMod 3 = 3 := by decide

private theorem two_ne_zero' : (2 : ZMod Fp.modulus) ≠ 0 := by decide

/-- The rule for two points of the curve, both away from infinity. -/
private theorem add_affine {x1 y1 x2 y2 : Fp} (h1 : (affine x1 y1).isOnCurve = true)
    (h2 : (affine x2 y2).isOnCurve = true) :
    (affine x1 y1 + affine x2 y2).isOnCurve = true
      ∧ toPoint (affine x1 y1 + affine x2 y2) = toPoint (affine x1 y1) + toPoint (affine x2 y2) := by
  have e1 := (isOnCurve_affine x1 y1).mp h1
  have e2 := (isOnCurve_affine x2 y2).mp h2
  rw [toPoint_affine h1, toPoint_affine h2]
  show (add (affine x1 y1) (affine x2 y2)).isOnCurve = true ∧ toPoint (add (affine x1 y1) (affine x2 y2)) = _
  simp only [add]
  by_cases hx : x1 = x2
  · subst hx
    rw [ite_eq_left rfl]
    by_cases hy : y2 = -y1
    · -- Rule 3: opposite points sum to `O`.
      rw [ite_eq_left hy, Affine.Point.add_of_Y_eq rfl (by rw [negY_eq, hy, Fp.toZMod_neg, neg_neg])]
      exact ⟨rfl, rfl⟩
    · -- Same `x`, not opposite: the points are equal, and rule 5 doubles.
      rw [ite_eq_right hy]
      have hy2 : y2 = y1 := by
        rcases y_eq_or_eq_neg e1 (e2.trans (by rfl)) with h | h
        · exact Fp.toZMod.injective h
        · exact absurd (Fp.toZMod.injective (h.trans (Fp.toZMod_neg y1).symm)) hy
      subst hy2
      have hne : Fp.toZMod y2 ≠ curve.negY (Fp.toZMod x1) (Fp.toZMod y2) := fun h =>
        hy (Fp.toZMod.injective (by rw [Fp.toZMod_neg]; rw [negY_eq] at h; exact h))
      have h2y : 2 * Fp.toZMod y2 ≠ 0 := fun h => hne (by rw [negY_eq]; linear_combination h)
      rw [Affine.Point.add_self_of_Y_ne hne]
      refine affine_of_eq ?_ ?_ _ <;>
        simp only [map_mul, map_sub, Fp.toZMod_inv, toZMod_two, toZMod_three, Affine.addX, Affine.addY,
          Affine.negAddY, negY_eq, Affine.slope_of_Y_ne rfl hne] <;>
        simp only [curve] <;> field_simp <;> ring
  · -- Rule 4: different `x`, the chord.
    rw [ite_eq_right hx]
    have hX : Fp.toZMod x1 ≠ Fp.toZMod x2 := fun h => hx (Fp.toZMod.injective h)
    have hX' : Fp.toZMod x2 - Fp.toZMod x1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hX)
    have hX'' : Fp.toZMod x1 - Fp.toZMod x2 ≠ 0 := sub_ne_zero.mpr hX
    rw [Affine.Point.add_of_X_ne hX]
    refine affine_of_eq ?_ ?_ _ <;>
      simp only [map_mul, map_sub, Fp.toZMod_inv, Affine.addX, Affine.addY, Affine.negAddY, negY_eq,
        Affine.slope_of_X_ne hX] <;>
      simp only [curve] <;> field_simp <;> ring

theorem isOnCurve_add {p q : Point} (hp : p.isOnCurve = true) (hq : q.isOnCurve = true) :
    (p + q).isOnCurve = true := by
  cases p with
  | infinity => exact hq
  | affine x1 y1 =>
    cases q with
    | infinity => exact hp
    | affine x2 y2 => exact (add_affine hp hq).1

theorem toPoint_add {p q : Point} (hp : p.isOnCurve = true) (hq : q.isOnCurve = true) :
    toPoint (p + q) = toPoint p + toPoint q := by
  cases p with
  | infinity => exact (zero_add _).symm
  | affine x1 y1 =>
    cases q with
    | infinity => exact (add_zero _).symm
    | affine x2 y2 => exact (add_affine hp hq).2

/-! ## Scalar multiplication -/

theorem isOnCurve_mulBits (fuel k : Nat) {p : Point} (hp : p.isOnCurve = true) :
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
theorem toPoint_mulBits (fuel k : Nat) {p : Point} (hp : p.isOnCurve = true) (hk : k < 2 ^ fuel) :
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

theorem isOnCurve_mul (k : Fn) {p : Point} (hp : p.isOnCurve = true) : (mul k p).isOnCurve = true :=
  isOnCurve_mulBits 256 k.val hp

/-- `mul k P` is `k P`, with the value of `k` below `n`. -/
theorem toPoint_mul (k : Fn) {p : Point} (hp : p.isOnCurve = true) :
    toPoint (mul k p) = k.val • toPoint p :=
  toPoint_mulBits 256 k.val hp (Nat.lt_trans k.isLt (by decide))

/-! ## Points and group elements correspond -/

/-- Two points on the curve with the same group element are equal. -/
theorem toPoint_inj {p q : Point} (hp : p.isOnCurve = true) (hq : q.isOnCurve = true) :
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
      rw [Fp.toZMod.injective h.1, Fp.toZMod.injective h.2]

/-- Only the point at infinity goes to `0`. -/
theorem toPoint_eq_zero {p : Point} (hp : p.isOnCurve = true) : toPoint p = 0 ↔ p = infinity :=
  toPoint_inj (q := infinity) hp rfl

/-- Every group element is the element of a point on the curve. -/
theorem toPoint_surjective (P : curve.Point) : ∃ p : Point, p.isOnCurve = true ∧ toPoint p = P := by
  cases P with
  | zero => exact ⟨infinity, rfl, rfl⟩
  | some x y h =>
    have hc : (affine x y).isOnCurve = true := (isOnCurve_affine x y).mpr ((equation_iff x y).mp h.1)
    exact ⟨affine x y, hc, toPoint_affine hc⟩

end Point

end EthLib.Cryptography.Secp256k1
