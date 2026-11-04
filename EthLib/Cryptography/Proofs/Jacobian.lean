module

public import EthLib.Cryptography.Jacobian
public import EthLib.Cryptography.Proofs.Inverse
public import EthLib.Cryptography.Proofs.ShortWeierstrass

/-!
# Proofs: Jacobian coordinates follow the group law

Each Jacobian form `(X, Y, Z)` with `Z != 0` gives the affine point `(X / Z^2, Y / Z^3)`.

Doubling and addition of forms give the forms of the group's sums.

So double and add on forms computes `k P`.

The proofs map each coordinate to the field `ZMod m`, for a prime `m != 2`.
-/

@[expose] public section

namespace EthLib.Cryptography.Jacobian

open WeierstrassCurve WeierstrassCurve.Affine

variable {m : Nat}

/-! ## Coordinates in `ZMod m` -/

/-- The value of an element of `Fin m` in `ZMod m`. -/
def toZ (x : Fin m) : ZMod m := (x.val : ZMod m)

@[simp] theorem toZ_add (x y : Fin m) : toZ (x + y) = toZ x + toZ y := by
  simp [toZ, Fin.val_add]

@[simp] theorem toZ_mul (x y : Fin m) : toZ (x * y) = toZ x * toZ y := by
  simp [toZ, Fin.val_mul]

@[simp] theorem toZ_sub (x y : Fin m) : toZ (x - y) = toZ x - toZ y := by
  rw [toZ, Fin.sub_def]
  simp only [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub y.isLt.le, ZMod.natCast_self]
  simp [toZ]
  ring

@[simp] theorem toZ_zero [NeZero m] : toZ (0 : Fin m) = 0 := by
  simp [toZ]

@[simp] theorem toZ_one [NeZero m] : toZ (1 : Fin m) = 1 := by
  simp [toZ]

theorem toZ_ofNat [NeZero m] (n : Nat) : toZ (Fin.ofNat m n) = (n : ZMod m) := by
  simp [toZ]

-- The numerals of the formulas.
@[simp] theorem toZ_two [NeZero m] : toZ (2 : Fin m) = 2 := toZ_ofNat 2
@[simp] theorem toZ_three [NeZero m] : toZ (3 : Fin m) = 3 := toZ_ofNat 3
@[simp] theorem toZ_four [NeZero m] : toZ (4 : Fin m) = 4 := toZ_ofNat 4
@[simp] theorem toZ_eight [NeZero m] : toZ (8 : Fin m) = 8 := toZ_ofNat 8

theorem toZ_eq_zero [NeZero m] {x : Fin m} : toZ x = 0 ↔ x = 0 := by
  rw [toZ, ZMod.natCast_eq_zero_iff]
  constructor
  · intro h
    exact Fin.ext (Nat.eq_zero_of_dvd_of_lt h x.isLt)
  · rintro rfl
    simp

theorem toZ_injective : Function.Injective (toZ (m := m)) := by
  intro x y h
  rw [toZ, toZ, ZMod.natCast_eq_natCast_iff'] at h
  exact Fin.ext (by rwa [Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] at h)

@[simp] theorem toZ_inverse [NeZero m] [Fact m.Prime] (x : Fin m) :
    toZ (Fin.inverse x) = (toZ x)⁻¹ :=
  Fin.inverse_val x

/-! ## The point of a form -/

variable [NeZero m] [Fact m.Prime] {A B : ZMod m} [(ShortWeierstrass.curve A B).IsElliptic]

/-- The affine `x` of a form, `X / Z^2`. -/
def affX (p : Jacobian m) : ZMod m := toZ p.x / toZ p.z ^ 2

/-- The affine `y` of a form, `Y / Z^3`. -/
def affY (p : Jacobian m) : ZMod m := toZ p.y / toZ p.z ^ 3

variable (A B) in
/-- A form is on the curve when `Z = 0`, or when its affine point satisfies the equation. -/
def OnCurve (p : Jacobian m) : Prop :=
  p.z ≠ 0 → affY p * affY p = affX p * affX p * affX p + A * affX p + B

omit [NeZero m] in
theorem nonsingular {x y : ZMod m} (h : y * y = x * x * x + A * x + B) :
    (ShortWeierstrass.curve A B).Nonsingular x y :=
  equation_iff_nonsingular.mp ((ShortWeierstrass.equation_iff x y).mpr h)

variable (A B) in
/-- The group element of a form: `0` at infinity, and the affine point otherwise.

A form off the curve goes to `0`: every theorem assumes the form is on the curve. -/
noncomputable def toPoint (p : Jacobian m) : (ShortWeierstrass.curve A B).Point :=
  if h : p.z ≠ 0 ∧ affY p * affY p = affX p * affX p * affX p + A * affX p + B then
    .some _ _ (nonsingular h.2)
  else 0

theorem toPoint_of_z_eq_zero {p : Jacobian m} (hz : p.z = 0) : toPoint A B p = 0 := by
  simp [toPoint, hz]

theorem toPoint_of_z_ne_zero {p : Jacobian m} (hp : OnCurve A B p) (hz : p.z ≠ 0) :
    toPoint A B p = .some _ _ (nonsingular (hp hz)) :=
  dite_eq_left ⟨hz, hp hz⟩

omit [(ShortWeierstrass.curve A B).IsElliptic] in
theorem onCurve_infinity : OnCurve A B (infinity : Jacobian m) := fun h => absurd rfl h

/-- A form with `Z != 0` and the affine point `(x, y)` is on the curve and maps to that point. -/
theorem spec_of_eq {r : Jacobian m} {x y : ZMod m}
    (h : (ShortWeierstrass.curve A B).Nonsingular x y) (hz : r.z ≠ 0)
    (hx : affX r = x) (hy : affY r = y) :
    OnCurve A B r ∧ toPoint A B r = .some x y h := by
  have he : affY r * affY r = affX r * affX r * affX r + A * affX r + B := by
    rw [hx, hy]
    exact (ShortWeierstrass.equation_iff _ _).mp h.1
  exact ⟨fun _ => he, by rw [toPoint_of_z_ne_zero (fun _ => he) hz]; simp [hx, hy]⟩

theorem toZ_z_ne_zero {p : Jacobian m} (hz : p.z ≠ 0) : toZ p.z ≠ 0 :=
  fun h => hz (toZ_eq_zero.mp h)

/-! ## Back to affine coordinates -/

omit [Fact m.Prime] [(ShortWeierstrass.curve A B).IsElliptic] in
theorem toAffine_of_z_eq_zero {p : Jacobian m} (hz : p.z = 0) : p.toAffine = none := by
  simp [toAffine, hz]

omit [(ShortWeierstrass.curve A B).IsElliptic] in
/-- A form with `Z != 0` gives the affine point `(X / Z^2, Y / Z^3)`. -/
theorem toAffine_of_z_ne_zero {p : Jacobian m} (hz : p.z ≠ 0) :
    ∃ x y, p.toAffine = some (x, y) ∧ toZ x = affX p ∧ toZ y = affY p := by
  refine ⟨p.x * (Fin.inverse p.z * Fin.inverse p.z),
    p.y * (Fin.inverse p.z * Fin.inverse p.z) * Fin.inverse p.z,
    by simp [toAffine, hz], ?_, ?_⟩ <;>
    simp [affX, affY, div_eq_mul_inv, pow_succ, mul_assoc]

/-! ## Doubling -/

variable {a : Fin m} (ha : toZ a = A) (h2 : (2 : ZMod m) ≠ 0)
include ha h2

/-- Doubling a form on the curve gives a form on the curve, with twice the group element.

The formula must use the curve's `a`, and `2 != 0` in the field. -/
theorem double_spec {p : Jacobian m} (hp : OnCurve A B p) :
    OnCurve A B (double a p) ∧ toPoint A B (double a p) = toPoint A B p + toPoint A B p := by
  have hz3 : toZ (double a p).z = 2 * toZ p.y * toZ p.z := by simp [double]
  by_cases hz : p.z = 0
  · -- At infinity, the double is at infinity.
    have hz3' : (double a p).z = 0 := toZ_eq_zero.mp (by rw [hz3, hz, toZ_zero, mul_zero])
    refine ⟨fun h => absurd hz3' h, ?_⟩
    rw [toPoint_of_z_eq_zero hz3', toPoint_of_z_eq_zero hz, add_zero]
  have hZ := toZ_z_ne_zero hz
  rw [toPoint_of_z_ne_zero hp hz]
  by_cases hy : toZ p.y = 0
  · -- `y = 0`, so `P = -P` and `2 P = 0`.
    have hz3' : (double a p).z = 0 := toZ_eq_zero.mp (by rw [hz3, hy, mul_zero, zero_mul])
    refine ⟨fun h => absurd hz3' h, ?_⟩
    rw [toPoint_of_z_eq_zero hz3', ShortWeierstrass.add_of_y_eq_neg _ _ (by simp [affY, hy])]
  · have hY : affY p ≠ -affY p := by
      intro h
      have : 2 * affY p = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h' | h'
      · exact h2 h'
      · simp [affY, hy, hZ] at h'
    have hz3' : (double a p).z ≠ 0 := fun h => by
      have := congrArg toZ h
      rw [hz3, toZ_zero] at this
      simp [h2, hy, hZ] at this
    obtain ⟨h3, hsum⟩ := ShortWeierstrass.add_self_of_y_ne (nonsingular (hp hz)) hY
      (l := (3 * affX p * affX p + A) * (2 * affY p)⁻¹) rfl rfl rfl
    refine (spec_of_eq h3 hz3' ?_ ?_).imp id fun e => e.trans hsum.symm
    all_goals
      have hX : toZ p.x = affX p * toZ p.z ^ 2 := by simp only [affX]; field_simp
      have hY' : toZ p.y = affY p * toZ p.z ^ 3 := by simp only [affY]; field_simp
      have hy0 : affY p ≠ 0 := fun h => hy (by rw [hY', h, zero_mul])
      clear hsum h3 hY
      generalize affX p = x at *
      generalize affY p = y at *
      simp only [affX, affY, double, toZ_add, toZ_sub, toZ_mul, toZ_two, toZ_three, toZ_four,
        toZ_eight, ha]
      rw [hX, hY']
      field_simp
      ring

/-! ## Addition -/

/-- Adding two forms on the curve gives a form on the curve, with the sum of the elements. -/
theorem add_spec {p q : Jacobian m} (hp : OnCurve A B p) (hq : OnCurve A B q) :
    OnCurve A B (add a p q) ∧ toPoint A B (add a p q) = toPoint A B p + toPoint A B q := by
  by_cases hzp : p.z = 0
  · simp only [add, hzp, ↓reduceIte]
    exact ⟨hq, by rw [toPoint_of_z_eq_zero hzp, zero_add]⟩
  by_cases hzq : q.z = 0
  · simp only [add, hzp, hzq, ↓reduceIte]
    exact ⟨hp, by rw [toPoint_of_z_eq_zero hzq, add_zero]⟩
  have hZ1 := toZ_z_ne_zero hzp
  have hZ2 := toZ_z_ne_zero hzq
  have e1 := hp hzp
  have e2 := hq hzq
  rw [toPoint_of_z_ne_zero hp hzp, toPoint_of_z_ne_zero hq hzq]
  -- `h = Z1^2 Z2^2 (x2 - x1)` and `r = Z1^3 Z2^3 (y2 - y1)`.
  have hh : toZ (q.x * (p.z * p.z) - p.x * (q.z * q.z))
      = toZ p.z ^ 2 * toZ q.z ^ 2 * (affX q - affX p) := by
    simp only [affX, toZ_sub, toZ_mul]
    field_simp
  have hr : toZ (q.y * p.z * (p.z * p.z) - p.y * q.z * (q.z * q.z))
      = toZ p.z ^ 3 * toZ q.z ^ 3 * (affY q - affY p) := by
    simp only [affY, toZ_sub, toZ_mul]
    field_simp
  simp only [add, hzp, hzq, ↓reduceIte]
  split_ifs with hx hy
  · -- One point twice.
    have hx' : affX q = affX p := by
      have := congrArg toZ hx
      rw [hh, toZ_zero] at this
      simpa [hZ1, hZ2, sub_eq_zero] using this
    have hy' : affY q = affY p := by
      have := congrArg toZ hy
      rw [hr, toZ_zero] at this
      simpa [hZ1, hZ2, sub_eq_zero] using this
    obtain ⟨hon, hdbl⟩ := double_spec ha h2 hp
    refine ⟨hon, ?_⟩
    rw [hdbl, toPoint_of_z_ne_zero hp hzp]
    simp [hx', hy']
  · -- Opposite points.
    have hx' : affX q = affX p := by
      have := congrArg toZ hx
      rw [hh, toZ_zero] at this
      simpa [hZ1, hZ2, sub_eq_zero] using this
    have hy' : affY q ≠ affY p := by
      intro h
      apply hy
      apply toZ_injective
      rw [hr, toZ_zero, h, sub_self, mul_zero]
    have hneg : affY q = -affY p := by
      rcases ShortWeierstrass.y_eq_or_eq_neg e1 (by rw [← hx']; exact e2) with h | h
      · exact absurd h hy'
      · exact h
    refine ⟨fun h => absurd rfl h, ?_⟩
    rw [toPoint_of_z_eq_zero (rfl : (infinity : Jacobian m).z = 0)]
    have e2' : affY q * affY q = affX p * affX p * affX p + A * affX p + B := by
      rw [← hx']; exact e2
    have hq' : (Point.some _ _ (nonsingular e2) : (ShortWeierstrass.curve A B).Point)
        = Point.some _ _ (nonsingular e2') := by simp [hx']
    rw [hq', ShortWeierstrass.add_of_y_eq_neg _ _ hneg]
  · -- Different `x`: the chord.
    have hx' : affX p ≠ affX q := by
      intro h
      apply hx
      apply toZ_injective
      rw [hh, toZ_zero, h, sub_self, mul_zero]
    have hz3' : p.z * q.z * (q.x * (p.z * p.z) - p.x * (q.z * q.z)) ≠ 0 := fun h => by
      have := congrArg toZ h
      rw [toZ_mul, toZ_mul, hh, toZ_zero] at this
      simp [hZ1, hZ2, sub_eq_zero, Ne.symm hx'] at this
    obtain ⟨h3, hsum⟩ := ShortWeierstrass.add_of_x_ne (nonsingular e1) (nonsingular e2) hx'
      (l := (affY q - affY p) * (affX q - affX p)⁻¹) rfl rfl rfl
    refine (spec_of_eq h3 hz3' ?_ ?_).imp id fun e => e.trans hsum.symm
    all_goals
      have hd : affX q - affX p ≠ 0 := sub_ne_zero.mpr (Ne.symm hx')
      have hX1 : toZ p.x = affX p * toZ p.z ^ 2 := by simp only [affX]; field_simp
      have hX2 : toZ q.x = affX q * toZ q.z ^ 2 := by simp only [affX]; field_simp
      have hY1 : toZ p.y = affY p * toZ p.z ^ 3 := by simp only [affY]; field_simp
      have hY2 : toZ q.y = affY q * toZ q.z ^ 3 := by simp only [affY]; field_simp
      clear hsum h3
      generalize affX p = x1, affX q = x2, affY p = y1, affY q = y2 at *
      simp only [affX, affY, toZ_sub, toZ_mul, toZ_two]
      rw [hX1, hX2, hY1, hY2]
      field_simp
      ring


/-! ## Scalar multiplication -/

/-- Double and add on forms stays on the curve. -/
theorem onCurve_mulBits (fuel k : Nat) {p : Jacobian m} (hp : OnCurve A B p) :
    OnCurve A B (mulBits a fuel k p) := by
  induction fuel generalizing k p with
  | zero => exact onCurve_infinity
  | succ fuel ih =>
    have hrest := ih (k / 2) (double_spec ha h2 hp).1
    simp only [mulBits]
    split
    · exact (add_spec ha h2 hp hrest).1
    · exact hrest

/-- Double and add on forms computes `k P`, when `k < 2^fuel`. -/
theorem toPoint_mulBits (fuel k : Nat) {p : Jacobian m} (hp : OnCurve A B p) (hk : k < 2 ^ fuel) :
    toPoint A B (mulBits a fuel k p) = k • toPoint A B p := by
  induction fuel generalizing k p with
  | zero =>
    obtain rfl : k = 0 := by simpa using hk
    simp [mulBits, toPoint_of_z_eq_zero (rfl : (infinity : Jacobian m).z = 0)]
  | succ fuel ih =>
    have hk2 : k / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at hk; omega
    obtain ⟨hd, hdp⟩ := double_spec ha h2 hp
    have hrest := ih (k / 2) hd hk2
    rw [hdp] at hrest
    simp only [mulBits]
    split
    · -- An odd `k` is `2 (k / 2) + 1`.
      rw [(add_spec ha h2 hp (onCurve_mulBits ha h2 fuel _ hd)).2, hrest]
      conv_rhs => rw [show k = 2 * (k / 2) + 1 by omega]
      module
    · -- An even `k` is `2 (k / 2)`.
      rw [hrest]
      conv_rhs => rw [show k = 2 * (k / 2) by omega]
      module

end EthLib.Cryptography.Jacobian
