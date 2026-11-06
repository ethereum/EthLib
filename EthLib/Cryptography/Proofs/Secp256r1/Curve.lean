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

namespace Point

/-- The group element of a point.

A pair off the curve has none, and goes to `0`: every theorem assumes the point is on the curve. -/
def toPoint : Point → curve.Point
  | infinity => 0
  | affine x y =>
    if h : Fp.toZMod y * Fp.toZMod y = Fp.toZMod x * Fp.toZMod x * Fp.toZMod x + Fp.toZMod a * Fp.toZMod x
        + Fp.toZMod b then
      .some _ _ (nonsingular_of h)
    else 0

/-- The curve test, as an equation in `ZMod p`. -/
theorem isOnCurve_affine (x y : Fp) :
    (affine x y).isOnCurve = true ↔ Fp.toZMod y * Fp.toZMod y
      = Fp.toZMod x * Fp.toZMod x * Fp.toZMod x + Fp.toZMod a * Fp.toZMod x + Fp.toZMod b := by
  simp only [isOnCurve, beq_iff_eq]
  exact ⟨fun h => by simpa only [map_add, map_mul] using congrArg Fp.toZMod h,
    fun h => Fp.toZMod.injective (by simpa only [map_add, map_mul] using h)⟩

theorem toPoint_affine {x y : Fp} (h : (affine x y).isOnCurve = true) :
    toPoint (affine x y) = .some _ _ (nonsingular_of ((isOnCurve_affine x y).mp h)) :=
  dite_eq_left ((isOnCurve_affine x y).mp h)

@[simp] theorem toPoint_infinity : toPoint infinity = 0 := rfl

/-- `(0, 0)` does not lie on the curve.

EIP-7951, Point of Infinity Encoding, encodes the point at infinity as `(0, 0)` for this reason. -/
theorem isOnCurve_affine_zero_zero : (affine 0 0).isOnCurve = false := by
  decide

/-! ## Addition -/

/-- A pair whose coordinates are those of a group element is on the curve, and is that element. -/
private theorem affine_of_eq {x3 y3 : Fp} {P : curve.Point}
    (h : ∃ h3, P = .some (Fp.toZMod x3) (Fp.toZMod y3) h3) :
    (affine x3 y3).isOnCurve = true ∧ toPoint (affine x3 y3) = P := by
  obtain ⟨h3, rfl⟩ := h
  have hc : (affine x3 y3).isOnCurve = true :=
    (isOnCurve_affine x3 y3).mpr ((ShortWeierstrass.equation_iff _ _).mp h3.1)
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
    · -- Rule 3: opposite points sum to `0`.
      rw [ite_eq_left hy, ShortWeierstrass.add_of_y_eq_neg _ _ (by rw [hy, Fp.toZMod_neg])]
      exact ⟨rfl, rfl⟩
    · -- Same `x`, not opposite: the points are equal, and rule 5 doubles.
      rw [ite_eq_right hy]
      have hy2 : y2 = y1 := by
        rcases ShortWeierstrass.y_eq_or_eq_neg e1 e2 with h | h
        · exact Fp.toZMod.injective h
        · exact absurd (Fp.toZMod.injective (h.trans (Fp.toZMod_neg y1).symm)) hy
      subst hy2
      have hne : Fp.toZMod y2 ≠ -Fp.toZMod y2 := fun h =>
        hy (Fp.toZMod.injective (by rw [Fp.toZMod_neg]; exact h))
      refine affine_of_eq (ShortWeierstrass.add_self_of_y_ne _ hne rfl ?_ ?_) <;>
        simp only [map_mul, map_sub, map_add, Fp.toZMod_inv, toZMod_two, toZMod_three]
  · -- Rule 4: different `x`, the chord.
    rw [ite_eq_right hx]
    have hX : Fp.toZMod x1 ≠ Fp.toZMod x2 := fun h => hx (Fp.toZMod.injective h)
    refine affine_of_eq (ShortWeierstrass.add_of_x_ne _ _ hX rfl ?_ ?_) <;>
      simp only [map_mul, map_sub, Fp.toZMod_inv]

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

private theorem toZ_eq (x : Fp) : Jacobian.toZ x = Fp.toZMod x :=
  ZMod.natCast_zmod_val (Fp.toZMod x)

private theorem toZ_a : Jacobian.toZ (a : Fp) = Fp.toZMod a := toZ_eq _

/-- A point of the curve has a Jacobian form on the curve, with the same group element. -/
theorem toJacobian_spec {p : Point} (hp : p.isOnCurve = true) :
    Jacobian.OnCurve (Fp.toZMod a) (Fp.toZMod b) (toJacobian p) ∧
      (Jacobian.toPoint (Fp.toZMod a) (Fp.toZMod b) (toJacobian p) : curve.Point) = toPoint p := by
  cases p with
  | infinity => exact ⟨Jacobian.onCurve_infinity, Jacobian.toPoint_of_z_eq_zero rfl⟩
  | affine x y =>
    have h := (isOnCurve_affine x y).mp hp
    have hx : Jacobian.affX (Jacobian.ofAffine x y) = Fp.toZMod x := by
      simp [Jacobian.affX, Jacobian.ofAffine, toZ_eq]
    have hy : Jacobian.affY (Jacobian.ofAffine x y) = Fp.toZMod y := by
      simp [Jacobian.affY, Jacobian.ofAffine, toZ_eq]
    have hz : (Jacobian.ofAffine x y).z ≠ 0 :=
      Jacobian.toZ_eq_zero.not.mp (by simp [Jacobian.ofAffine])
    have hs := Jacobian.spec_of_eq (A := Fp.toZMod a) (B := Fp.toZMod b) (nonsingular_of h) hz hx hy
    exact ⟨hs.1, hs.2.trans (toPoint_affine hp).symm⟩

/-- A Jacobian form on the curve gives a point of the curve, with the same group element. -/
theorem ofJacobian_spec {p : Jacobian Fp.modulus}
    (hp : Jacobian.OnCurve (Fp.toZMod a) (Fp.toZMod b) p) :
    (ofJacobian p).isOnCurve = true ∧
      toPoint (ofJacobian p) = Jacobian.toPoint (Fp.toZMod a) (Fp.toZMod b) p := by
  by_cases hz : p.z = 0
  · simp only [ofJacobian, Jacobian.toAffine_of_z_eq_zero hz]
    exact ⟨rfl, (Jacobian.toPoint_of_z_eq_zero hz).symm⟩
  · obtain ⟨x, y, h, hx, hy⟩ := Jacobian.toAffine_of_z_ne_zero hz
    rw [toZ_eq] at hx hy
    have he := hp hz
    rw [← hx, ← hy] at he
    have hon : (affine x y).isOnCurve = true :=
      (isOnCurve_affine x y).mpr (by linear_combination he)
    simp only [ofJacobian, h]
    refine ⟨hon, ?_⟩
    rw [toPoint_affine hon, Jacobian.toPoint_of_z_ne_zero hp hz]
    simp only [hx, hy]

theorem isOnCurve_mulBits (fuel k : Nat) {p : Point} (hp : p.isOnCurve = true) :
    (mulBits fuel k p).isOnCurve = true :=
  (ofJacobian_spec (Jacobian.onCurve_mulBits toZ_a two_ne_zero' fuel k
    (toJacobian_spec hp).1)).1

/-- Double and add computes `k P`, when `k < 2^fuel`. -/
theorem toPoint_mulBits (fuel k : Nat) {p : Point} (hp : p.isOnCurve = true) (hk : k < 2 ^ fuel) :
    toPoint (mulBits fuel k p) = k • toPoint p := by
  have hJ := toJacobian_spec hp
  rw [mulBits, (ofJacobian_spec (Jacobian.onCurve_mulBits toZ_a two_ne_zero' fuel k hJ.1)).2,
    Jacobian.toPoint_mulBits toZ_a two_ne_zero' fuel k hJ.1 hk]
  exact congrArg (k • ·) hJ.2

theorem isOnCurve_mul (k : Fn) {p : Point} (hp : p.isOnCurve = true) : (mul k p).isOnCurve = true :=
  isOnCurve_mulBits 256 k.val hp

/-- Scalar multiplication computes `k P`, with the value of `k` below `n`. -/
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
    have hc : (affine x y).isOnCurve = true :=
      (isOnCurve_affine x y).mpr ((ShortWeierstrass.equation_iff x y).mp h.1)
    exact ⟨affine x y, hc, toPoint_affine hc⟩

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
