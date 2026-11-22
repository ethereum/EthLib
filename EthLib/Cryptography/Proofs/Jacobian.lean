module

public import EthLib.Cryptography.Jacobian
public import EthLib.Cryptography.Proofs.Inverse
public import EthLib.Cryptography.Proofs.ShortWeierstrass

/-!
# Proofs: Jacobian coordinates follow the group law

Each Jacobian form `(X, Y, Z)` with a nonzero `Z` gives the affine point `(X / Z^2, Y / Z^3)`.

Doubling and addition of forms give the forms of the group's sums.

So double and add on forms computes `k P`, and one shared chain of doublings computes `k P + l Q`.

The proofs hold over any field of characteristic other than 2.

A change of field representation commutes with every formula, on every form.

It commutes with the conversion back too, when it keeps the inverse.

So forms mod a prime `m` other than 2 follow the law through their values in `ZMod m`.

A point of a short Weierstrass curve converts to a form and back.

So double and add on points computes `k P`, in any representation of any such field.
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

/-! ## The steps of scalar multiplication -/

namespace Coords

section Steps

variable {F : Type} [OfNat F 0] [OfNat F 1] [Add F] [Sub F] [Mul F] [DecidableEq F]

/-- The scalar `0` gives the point at infinity, whatever the fuel. -/
theorem mulBits_scalar_zero (a : F) (fuel : Nat) (p : Coords F) :
    mulBits a fuel 0 p = infinity := by
  cases fuel <;> simp [mulBits]

/-- `k P = (k mod 2) P + (k / 2) (2 P)`, also when `k` is `0` and the chain stops early. -/
theorem mulBits_succ (a : F) (fuel k : Nat) (p : Coords F) :
    mulBits a (fuel + 1) k p =
      let rest := mulBits a fuel (k / 2) (double a p)
      if k % 2 = 1 then add a p rest else rest := by
  by_cases hk : k = 0
  · subst hk
    simp [mulBits, mulBits_scalar_zero]
  · simp [mulBits, hk]

end Steps

/-! ## A change of field representation -/

/-- A map between two representations of one field.

It is injective, and it keeps `0`, `1`, `+`, `-` and `*`. -/
structure Embedding {F G : Type} [OfNat F 0] [OfNat F 1] [Add F] [Sub F] [Mul F]
    [OfNat G 0] [OfNat G 1] [Add G] [Sub G] [Mul G] (f : F → G) : Prop where
  /-- `0` maps to `0`. -/
  map_zero : f 0 = 0
  /-- `1` maps to `1`. -/
  map_one : f 1 = 1
  /-- Sums are kept. -/
  map_add : ∀ x y, f (x + y) = f x + f y
  /-- Differences are kept. -/
  map_sub : ∀ x y, f (x - y) = f x - f y
  /-- Products are kept. -/
  map_mul : ∀ x y, f (x * y) = f x * f y
  /-- Distinct elements stay distinct. -/
  injective : Function.Injective f

/-- The identity is a change of representation, from a field to itself. -/
theorem Embedding.id {F : Type} [OfNat F 0] [OfNat F 1] [Add F] [Sub F] [Mul F] :
    Embedding (id : F → F) :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, Function.injective_id⟩

variable {F G : Type}
  [OfNat F 0] [OfNat F 1] [Add F] [Sub F] [Mul F] [DecidableEq F]
  [OfNat G 0] [OfNat G 1] [Add G] [Sub G] [Mul G] [DecidableEq G]
  {f : F → G} (hf : Embedding f)
include hf

omit [DecidableEq F] [DecidableEq G] in
/-- Only `0` maps to `0`. -/
theorem Embedding.map_eq_zero_iff (x : F) : f x = 0 ↔ x = 0 := by
  rw [← hf.map_zero, hf.injective.eq_iff]

omit [DecidableEq F] [DecidableEq G] in
/-- Only `1` maps to `1`. -/
theorem Embedding.map_eq_one_iff (x : F) : f x = 1 ↔ x = 1 := by
  rw [← hf.map_one, hf.injective.eq_iff]

omit [DecidableEq F] [DecidableEq G] in
/-- The point at infinity reads as the point at infinity. -/
theorem map_infinity : (infinity : Coords F).map f = infinity := by
  simp only [infinity, map, hf.map_zero, hf.map_one]

/-- Doubling commutes with the change of representation, on every form. -/
theorem map_double (a : F) (p : Coords F) : (double a p).map f = double (f a) (p.map f) := by
  have hzero := hf.map_eq_zero_iff
  simp only [double, map, hzero]
  split_ifs <;> simp only [hf.map_add, hf.map_sub, hf.map_mul]

/-- Addition commutes with the change of representation, with its exceptional cases. -/
theorem map_add (a : F) (p q : Coords F) :
    (add a p q).map f = add (f a) (p.map f) (q.map f) := by
  have hzero := hf.map_eq_zero_iff
  have hone := hf.map_eq_one_iff
  have mx (r : Coords F) : (r.map f).x = f r.x := rfl
  have my (r : Coords F) : (r.map f).y = f r.y := rfl
  have mz (r : Coords F) : (r.map f).z = f r.z := rfl
  by_cases hp : p.z = 0
  · simp only [add, mz, hzero, hp, ite_true]
  by_cases hq : q.z = 0
  · simp only [add, mz, hzero, hp, hq, ite_true, ite_false]
  simp only [add, mx, my, mz, hzero, hp, hq, ite_false]
  by_cases hq1 : q.z = 1
  all_goals
    simp only [hone, hq1, ite_true, ite_false]
    simp only [← hf.map_mul, ← hf.map_sub, ← hf.map_add, hzero]
    split_ifs
    · exact map_double hf a p
    · exact map_infinity hf
    · simp only [map, hf.map_mul, hf.map_sub, hf.map_add]

/-- The same bits select the same steps in both representations. -/
theorem map_mulBits (a : F) (fuel k : Nat) (p : Coords F) :
    (mulBits a fuel k p).map f = mulBits (f a) fuel k (p.map f) := by
  induction fuel generalizing k p with
  | zero => exact map_infinity hf
  | succ fuel ih =>
    simp only [mulBits_succ]
    split <;> simp only [map_add hf, map_double hf, ih]

/-- The simultaneous chain commutes with the change of representation, for every bit. -/
theorem map_mulAddAux (a : F) (p q pq : Coords F) (fuel k l : Nat) :
    (mulAddAux a p q pq fuel k l).map f =
      mulAddAux (f a) (p.map f) (q.map f) (pq.map f) fuel k l := by
  induction fuel generalizing k l with
  | zero => exact map_infinity hf
  | succ fuel ih =>
    simp only [mulAddAux]
    split_ifs <;> simp only [map_add hf, map_double hf, ih]

/-- Two products with shared doublings commute with the change of representation. -/
theorem map_mulAdd (a : F) (fuel k : Nat) (p : Coords F) (l : Nat) (q : Coords F) :
    (mulAdd a fuel k p l q).map f = mulAdd (f a) fuel k (p.map f) l (q.map f) := by
  simp only [mulAdd, map_mulAddAux hf, map_add hf]

/-- Normalizing and then reading the result is normalizing the read form, given the inverse. -/
theorem map_toAffine {inv : F → F} {inv' : G → G} (hinv : ∀ x, f (inv x) = inv' (f x))
    (p : Coords F) :
    (p.toAffine inv).map (fun r => (f r.1, f r.2)) = (p.map f).toAffine inv' := by
  have hzero := hf.map_eq_zero_iff
  simp only [toAffine, map, hzero]
  split_ifs <;> simp only [Option.map_none, Option.map_some, hf.map_mul, hinv]

end Coords

/-! ## The formulas on `Fin m` -/

/-- The point at infinity is `(1, 1, 0)`. -/
theorem infinity_eq [NeZero m] : (infinity : Jacobian m) = ⟨1, 1, 0⟩ := rfl

/-- The affine point of a form, by the one inverse of `Z`. -/
theorem toAffine_eq [NeZero m] (p : Jacobian m) :
    p.toAffine =
      if p.z = 0 then none
      else
        let zi := Fin.inverse p.z
        let zi2 := zi * zi
        some (p.x * zi2, p.y * zi2 * zi) := rfl

/-- Doubling on `Fin m` is formula (6) of Cohen, Miyaji and Ono, for every input.

Each small multiple is a product. -/
theorem double_eq_formula [NeZero m] (a : Fin m) (p : Jacobian m) :
    double a p =
    let xx := p.x * p.x
    let yy := p.y * p.y
    let zz := p.z * p.z
    let s := 4 * p.x * yy
    let l := 3 * xx + a * zz * zz
    let t := l * l - 2 * s
    ⟨t, l * (s - t) - 8 * yy * yy, 2 * p.y * p.z⟩ := by
  have hl : (if a = 0 then p.x * p.x + p.x * p.x + p.x * p.x else
      p.x * p.x + p.x * p.x + p.x * p.x + a * (p.z * p.z) * (p.z * p.z)) =
      3 * (p.x * p.x) + a * (p.z * p.z) * (p.z * p.z) := by
    apply toZ_injective
    by_cases ha : a = 0
    · simp only [ha, ite_true, toZ_add, toZ_mul, toZ_three, toZ_zero]
      ring
    · simp only [ha, ite_false, toZ_add, toZ_mul, toZ_three]
      ring
  dsimp only [double, Coords.double, ofCoords, toCoords]
  rw [hl]
  congr 1 <;> apply toZ_injective <;>
    simp only [toZ_add, toZ_sub, toZ_mul, toZ_two, toZ_three, toZ_four, toZ_eight] <;>
    ring

/-- Addition on `Fin m` is formula (5) of Cohen, Miyaji and Ono, for every input.

It has no shortcut for `Z = 1`. -/
theorem add_eq_formula [NeZero m] (a : Fin m) (p q : Jacobian m) :
    add a p q =
    if p.z = 0 then q
    else if q.z = 0 then p
    else
      let z1z1 := p.z * p.z
      let z2z2 := q.z * q.z
      let u1 := p.x * z2z2
      let u2 := q.x * z1z1
      let s1 := p.y * q.z * z2z2
      let s2 := q.y * p.z * z1z1
      let h := u2 - u1
      let r := s2 - s1
      if h = 0 then
        -- One `x`: the same point, or opposite points.
        if r = 0 then double a p else infinity
      else
        let hh := h * h
        let hhh := h * hh
        let v := u1 * hh
        let x3 := r * r - hhh - 2 * v
        ⟨x3, r * (v - x3) - s1 * hhh, p.z * q.z * h⟩ := by
  have hmixed : (if q.z = 1 then (p.x, p.y, p.z) else
      let z2z2 := q.z * q.z
      (p.x * z2z2, p.y * q.z * z2z2, p.z * q.z)) =
        (p.x * (q.z * q.z), p.y * q.z * (q.z * q.z), p.z * q.z) := by
    by_cases hz : q.z = 1 <;> simp [hz]
  have htwo (v : Fin m) : v + v = 2 * v := by
    apply toZ_injective
    simp only [toZ_add, toZ_mul, toZ_two]
    ring
  simp only [add, Coords.add, hmixed, htwo]
  split_ifs <;> rfl

/-- No bits leave the point at infinity. -/
theorem mulBits_zero [NeZero m] (a : Fin m) (k : Nat) (p : Jacobian m) :
    mulBits a 0 k p = infinity := rfl

/-- `k P = (k mod 2) P + (k / 2) (2 P)`. -/
theorem mulBits_succ [NeZero m] (a : Fin m) (fuel k : Nat) (p : Jacobian m) :
    mulBits a (fuel + 1) k p =
      let rest := mulBits a fuel (k / 2) (double a p)
      if k % 2 = 1 then add a p rest else rest := by
  simp only [mulBits, Coords.mulBits_succ]
  split <;> rfl

/-- No bits leave the point at infinity. -/
theorem mulAddAux_zero [NeZero m] (a : Fin m) (p q pq : Jacobian m) (k l : Nat) :
    mulAddAux a p q pq 0 k l = infinity := rfl

/-- `k P + l Q = 2 ((k / 2) P + (l / 2) Q) + (k mod 2) P + (l mod 2) Q`. -/
theorem mulAddAux_succ [NeZero m] (a : Fin m) (p q pq : Jacobian m) (fuel k l : Nat) :
    mulAddAux a p q pq (fuel + 1) k l =
      let acc := double a (mulAddAux a p q pq fuel (k / 2) (l / 2))
      if k % 2 = 1 then
        if l % 2 = 1 then add a acc pq else add a acc p
      else if l % 2 = 1 then add a acc q else acc := by
  simp only [mulAddAux, Coords.mulAddAux]
  split_ifs <;> rfl

/-- The chain starts from `P + Q`. -/
theorem mulAdd_eq [NeZero m] (a : Fin m) (fuel k : Nat) (p : Jacobian m) (l : Nat)
    (q : Jacobian m) : mulAdd a fuel k p l q = mulAddAux a p q (add a p q) fuel k l := rfl

/-! ## The point of a form over a field -/

namespace Coords

section Field

variable {K : Type} [Field K] [DecidableEq K] {A B : K}

/-- The affine `x` of a form, `X / Z^2`. -/
def affX (p : Coords K) : K := p.x / p.z ^ 2

/-- The affine `y` of a form, `Y / Z^3`. -/
def affY (p : Coords K) : K := p.y / p.z ^ 3

variable (A B) in
/-- A form is on the curve when `Z = 0`, or when its affine point satisfies the equation. -/
def OnCurve (p : Coords K) : Prop :=
  p.z ≠ 0 → affY p * affY p = affX p * affX p * affX p + A * affX p + B

variable [(ShortWeierstrass.curve A B).IsElliptic]

variable (A B) in
/-- The group element of a form: `0` at infinity, and the affine point otherwise.

A form off the curve goes to `0`: every theorem assumes the form is on the curve. -/
noncomputable def toPoint (p : Coords K) : (ShortWeierstrass.curve A B).Point :=
  if h : p.z ≠ 0 ∧ affY p * affY p = affX p * affX p * affX p + A * affX p + B then
    .some _ _ (ShortWeierstrass.nonsingular_of_eq h.2)
  else 0

theorem toPoint_of_z_eq_zero {p : Coords K} (hz : p.z = 0) : toPoint A B p = 0 := by
  simp [toPoint, hz]

theorem toPoint_of_z_ne_zero {p : Coords K} (hp : OnCurve A B p) (hz : p.z ≠ 0) :
    toPoint A B p = .some _ _ (ShortWeierstrass.nonsingular_of_eq (hp hz)) :=
  dite_eq_left ⟨hz, hp hz⟩

omit [DecidableEq K] [(ShortWeierstrass.curve A B).IsElliptic] in
theorem onCurve_infinity : OnCurve A B (infinity : Coords K) := fun h => absurd rfl h

/-- A form with a nonzero `Z` and affine values `(x, y)` is on the curve and maps to `(x, y)`. -/
theorem spec_of_eq {r : Coords K} {x y : K} (h : (ShortWeierstrass.curve A B).Nonsingular x y)
    (hz : r.z ≠ 0) (hx : affX r = x) (hy : affY r = y) :
    OnCurve A B r ∧ toPoint A B r = .some x y h := by
  have he : affY r * affY r = affX r * affX r * affX r + A * affX r + B := by
    rw [hx, hy]
    exact (ShortWeierstrass.equation_iff _ _).mp h.1
  exact ⟨fun _ => he, by rw [toPoint_of_z_ne_zero (fun _ => he) hz]; simp [hx, hy]⟩

omit [(ShortWeierstrass.curve A B).IsElliptic] in
/-- Doubling over a field is formula (6) of Cohen, Miyaji and Ono, for every input.

Each small multiple is a product. -/
theorem double_eq_formula (a : K) (p : Coords K) :
    double a p =
    let xx := p.x * p.x
    let yy := p.y * p.y
    let zz := p.z * p.z
    let s := 4 * p.x * yy
    let l := 3 * xx + a * zz * zz
    let t := l * l - 2 * s
    ⟨t, l * (s - t) - 8 * yy * yy, 2 * p.y * p.z⟩ := by
  have hl : (if a = 0 then p.x * p.x + p.x * p.x + p.x * p.x else
      p.x * p.x + p.x * p.x + p.x * p.x + a * (p.z * p.z) * (p.z * p.z)) =
      3 * (p.x * p.x) + a * (p.z * p.z) * (p.z * p.z) := by
    split_ifs with ha
    · rw [ha]
      ring
    · ring
  dsimp only [double]
  rw [hl]
  congr 1 <;> ring

omit [(ShortWeierstrass.curve A B).IsElliptic] in
/-- Addition over a field is formula (5) of Cohen, Miyaji and Ono, for every input.

It has no shortcut for `Z = 1`. -/
theorem add_eq_formula (a : K) (p q : Coords K) :
    add a p q =
    if p.z = 0 then q
    else if q.z = 0 then p
    else
      let z1z1 := p.z * p.z
      let z2z2 := q.z * q.z
      let u1 := p.x * z2z2
      let u2 := q.x * z1z1
      let s1 := p.y * q.z * z2z2
      let s2 := q.y * p.z * z1z1
      let h := u2 - u1
      let r := s2 - s1
      if h = 0 then
        -- One `x`: the same point, or opposite points.
        if r = 0 then double a p else infinity
      else
        let hh := h * h
        let hhh := h * hh
        let v := u1 * hh
        let x3 := r * r - hhh - 2 * v
        ⟨x3, r * (v - x3) - s1 * hhh, p.z * q.z * h⟩ := by
  have hmixed : (if q.z = 1 then (p.x, p.y, p.z) else
      let z2z2 := q.z * q.z
      (p.x * z2z2, p.y * q.z * z2z2, p.z * q.z)) =
        (p.x * (q.z * q.z), p.y * q.z * (q.z * q.z), p.z * q.z) := by
    by_cases hz : q.z = 1 <;> simp [hz]
  have htwo (v : K) : v + v = 2 * v := by ring
  simp only [add, hmixed, htwo]

variable (h2 : (2 : K) ≠ 0)
include h2

/-- Doubling a form on the curve gives a form on the curve, with twice the group element.

The formula must use the curve's `a`, and 2 must be nonzero in the field. -/
theorem double_spec {p : Coords K} (hp : OnCurve A B p) :
    OnCurve A B (double A p) ∧ toPoint A B (double A p) = toPoint A B p + toPoint A B p := by
  have hz3 : (double A p).z = 2 * p.y * p.z := by
    rw [double_eq_formula]
  by_cases hz : p.z = 0
  · -- At infinity, the double is at infinity.
    have hz3' : (double A p).z = 0 := by rw [hz3, hz, mul_zero]
    refine ⟨fun h => absurd hz3' h, ?_⟩
    rw [toPoint_of_z_eq_zero hz3', toPoint_of_z_eq_zero hz, add_zero]
  rw [toPoint_of_z_ne_zero hp hz]
  by_cases hy : p.y = 0
  · -- `y = 0`, so `P = -P` and `2 P = 0`.
    have hz3' : (double A p).z = 0 := by rw [hz3, hy, mul_zero, zero_mul]
    refine ⟨fun h => absurd hz3' h, ?_⟩
    rw [toPoint_of_z_eq_zero hz3', ShortWeierstrass.add_of_y_eq_neg _ _ (by simp [affY, hy])]
  · have hY : affY p ≠ -affY p := by
      intro h
      have : 2 * affY p = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h' | h'
      · exact h2 h'
      · simp [affY, hy, hz] at h'
    have hz3' : (double A p).z ≠ 0 := by
      rw [hz3]
      exact mul_ne_zero (mul_ne_zero h2 hy) hz
    obtain ⟨h3, hsum⟩ := ShortWeierstrass.add_self_of_y_ne
      (ShortWeierstrass.nonsingular_of_eq (hp hz)) hY
      (l := (3 * affX p * affX p + A) * (2 * affY p)⁻¹) rfl rfl rfl
    refine (spec_of_eq h3 hz3' ?_ ?_).imp id fun e => e.trans hsum.symm
    all_goals
      have hX : p.x = affX p * p.z ^ 2 := by simp only [affX]; field_simp
      have hY' : p.y = affY p * p.z ^ 3 := by simp only [affY]; field_simp
      have hy0 : affY p ≠ 0 := fun h => hy (by rw [hY', h, zero_mul])
      clear hsum h3 hY
      generalize affX p = x at *
      generalize affY p = y at *
      rw [double_eq_formula]
      simp only [affX, affY]
      rw [hX, hY']
      field_simp
      ring

/-- Adding two forms on the curve gives a form on the curve, with the sum of the elements. -/
theorem add_spec {p q : Coords K} (hp : OnCurve A B p) (hq : OnCurve A B q) :
    OnCurve A B (add A p q) ∧ toPoint A B (add A p q) = toPoint A B p + toPoint A B q := by
  by_cases hzp : p.z = 0
  · simp only [add, hzp, ↓reduceIte]
    exact ⟨hq, by rw [toPoint_of_z_eq_zero hzp, zero_add]⟩
  by_cases hzq : q.z = 0
  · simp only [add, hzp, hzq, ↓reduceIte]
    exact ⟨hp, by rw [toPoint_of_z_eq_zero hzq, add_zero]⟩
  have e1 := hp hzp
  have e2 := hq hzq
  rw [toPoint_of_z_ne_zero hp hzp, toPoint_of_z_ne_zero hq hzq]
  -- `h = Z1^2 Z2^2 (x2 - x1)` and `r = Z1^3 Z2^3 (y2 - y1)`.
  have hh : q.x * (p.z * p.z) - p.x * (q.z * q.z) = p.z ^ 2 * q.z ^ 2 * (affX q - affX p) := by
    simp only [affX]
    field_simp
  have hr : q.y * p.z * (p.z * p.z) - p.y * q.z * (q.z * q.z)
      = p.z ^ 3 * q.z ^ 3 * (affY q - affY p) := by
    simp only [affY]
    field_simp
  rw [add_eq_formula]
  simp only [hzp, hzq, ↓reduceIte]
  split_ifs with hx hy
  · -- One point twice.
    have hx' : affX q = affX p := by
      rw [hh] at hx
      simpa [hzp, hzq, sub_eq_zero] using hx
    have hy' : affY q = affY p := by
      rw [hr] at hy
      simpa [hzp, hzq, sub_eq_zero] using hy
    obtain ⟨hon, hdbl⟩ := double_spec h2 hp
    refine ⟨hon, ?_⟩
    rw [hdbl, toPoint_of_z_ne_zero hp hzp]
    simp [hx', hy']
  · -- Opposite points.
    have hx' : affX q = affX p := by
      rw [hh] at hx
      simpa [hzp, hzq, sub_eq_zero] using hx
    have hy' : affY q ≠ affY p := by
      intro h
      apply hy
      rw [hr, h, sub_self, mul_zero]
    have hneg : affY q = -affY p := by
      rcases ShortWeierstrass.y_eq_or_eq_neg e1 (by rw [← hx']; exact e2) with h | h
      · exact absurd h hy'
      · exact h
    refine ⟨fun h => absurd rfl h, ?_⟩
    rw [toPoint_of_z_eq_zero (rfl : (infinity : Coords K).z = 0)]
    have e2' : affY q * affY q = affX p * affX p * affX p + A * affX p + B := by
      rw [← hx']; exact e2
    have hq' : (Point.some _ _ (ShortWeierstrass.nonsingular_of_eq e2) :
        (ShortWeierstrass.curve A B).Point)
        = Point.some _ _ (ShortWeierstrass.nonsingular_of_eq e2') := by simp [hx']
    rw [hq', ShortWeierstrass.add_of_y_eq_neg _ _ hneg]
  · -- Different `x`: the chord.
    have hx' : affX p ≠ affX q := by
      intro h
      apply hx
      rw [hh, h, sub_self, mul_zero]
    have hz3' : p.z * q.z * (q.x * (p.z * p.z) - p.x * (q.z * q.z)) ≠ 0 := by
      rw [hh]
      exact mul_ne_zero (mul_ne_zero hzp hzq) (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hzp)
        (pow_ne_zero _ hzq)) (sub_ne_zero.mpr (Ne.symm hx')))
    obtain ⟨h3, hsum⟩ := ShortWeierstrass.add_of_x_ne (ShortWeierstrass.nonsingular_of_eq e1)
      (ShortWeierstrass.nonsingular_of_eq e2) hx'
      (l := (affY q - affY p) * (affX q - affX p)⁻¹) rfl rfl rfl
    refine (spec_of_eq h3 hz3' ?_ ?_).imp id fun e => e.trans hsum.symm
    all_goals
      have hd : affX q - affX p ≠ 0 := sub_ne_zero.mpr (Ne.symm hx')
      have hX1 : p.x = affX p * p.z ^ 2 := by simp only [affX]; field_simp
      have hX2 : q.x = affX q * q.z ^ 2 := by simp only [affX]; field_simp
      have hY1 : p.y = affY p * p.z ^ 3 := by simp only [affY]; field_simp
      have hY2 : q.y = affY q * q.z ^ 3 := by simp only [affY]; field_simp
      clear hsum h3
      generalize affX p = x1, affX q = x2, affY p = y1, affY q = y2 at *
      simp only [affX, affY]
      rw [hX1, hX2, hY1, hY2]
      field_simp
      ring

/-- Double and add on forms stays on the curve. -/
theorem onCurve_mulBits (fuel k : Nat) {p : Coords K} (hp : OnCurve A B p) :
    OnCurve A B (mulBits A fuel k p) := by
  induction fuel generalizing k p with
  | zero => exact onCurve_infinity
  | succ fuel ih =>
    have hrest := ih (k / 2) (double_spec h2 hp).1
    rw [mulBits_succ]
    split
    · exact (add_spec h2 hp hrest).1
    · exact hrest

/-- Double and add on forms computes `k P`, when `k < 2^fuel`. -/
theorem toPoint_mulBits (fuel k : Nat) {p : Coords K} (hp : OnCurve A B p) (hk : k < 2 ^ fuel) :
    toPoint A B (mulBits A fuel k p) = k • toPoint A B p := by
  induction fuel generalizing k p with
  | zero =>
    obtain rfl : k = 0 := by simpa using hk
    simp [mulBits, toPoint_of_z_eq_zero (rfl : (infinity : Coords K).z = 0)]
  | succ fuel ih =>
    have hk2 : k / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at hk; omega
    obtain ⟨hd, hdp⟩ := double_spec h2 hp
    have hrest := ih (k / 2) hd hk2
    rw [hdp] at hrest
    rw [mulBits_succ]
    split
    · -- An odd `k` is `2 (k / 2) + 1`.
      rw [(add_spec h2 hp (onCurve_mulBits h2 fuel _ hd)).2, hrest]
      conv_rhs => rw [show k = 2 * (k / 2) + 1 by omega]
      module
    · -- An even `k` is `2 (k / 2)`.
      rw [hrest]
      conv_rhs => rw [show k = 2 * (k / 2) by omega]
      module

/-- The joint chain stays on the curve. -/
theorem onCurve_mulAddAux {p q pq : Coords K} (hp : OnCurve A B p) (hq : OnCurve A B q)
    (hpq : OnCurve A B pq) (fuel k l : Nat) : OnCurve A B (mulAddAux A p q pq fuel k l) := by
  induction fuel generalizing k l with
  | zero => exact onCurve_infinity
  | succ fuel ih =>
    have hacc := (double_spec h2 (ih (k / 2) (l / 2))).1
    simp only [mulAddAux]
    split_ifs
    · exact (add_spec h2 hacc hpq).1
    · exact (add_spec h2 hacc hp).1
    · exact (add_spec h2 hacc hq).1
    · exact hacc

/-- The joint chain computes `k P + l Q`, when `pq` is `P + Q` and `k, l < 2^fuel`. -/
theorem toPoint_mulAddAux {p q pq : Coords K} (hp : OnCurve A B p) (hq : OnCurve A B q)
    (hpq : OnCurve A B pq) (hsum : toPoint A B pq = toPoint A B p + toPoint A B q)
    (fuel k l : Nat) (hk : k < 2 ^ fuel) (hl : l < 2 ^ fuel) :
    toPoint A B (mulAddAux A p q pq fuel k l) = k • toPoint A B p + l • toPoint A B q := by
  induction fuel generalizing k l with
  | zero =>
    obtain rfl : k = 0 := by simpa using hk
    obtain rfl : l = 0 := by simpa using hl
    simp [mulAddAux, toPoint_of_z_eq_zero (rfl : (infinity : Coords K).z = 0)]
  | succ fuel ih =>
    have hk2 : k / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at hk; omega
    have hl2 : l / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at hl; omega
    have hrest := onCurve_mulAddAux h2 hp hq hpq fuel (k / 2) (l / 2)
    obtain ⟨hacc, hdbl⟩ := double_spec h2 hrest
    rw [ih (k / 2) (l / 2) hk2 hl2] at hdbl
    -- `k = 2 (k / 2) + k mod 2`, and likewise for `l`.
    have ek := Nat.div_add_mod k 2
    have el := Nat.div_add_mod l 2
    simp only [mulAddAux]
    split_ifs with hk1 hl1 hl1
    · rw [(add_spec h2 hacc hpq).2, hdbl, hsum]
      conv_rhs => rw [← ek, ← el, hk1, hl1]
      module
    · rw [(add_spec h2 hacc hp).2, hdbl]
      conv_rhs => rw [← ek, ← el, hk1, show l % 2 = 0 by omega]
      module
    · rw [(add_spec h2 hacc hq).2, hdbl]
      conv_rhs => rw [← ek, ← el, show k % 2 = 0 by omega, hl1]
      module
    · rw [hdbl]
      conv_rhs => rw [← ek, ← el, show k % 2 = 0 by omega, show l % 2 = 0 by omega]
      module

/-- Simultaneous multiplication stays on the curve. -/
theorem onCurve_mulAdd (fuel k l : Nat) {p q : Coords K} (hp : OnCurve A B p)
    (hq : OnCurve A B q) : OnCurve A B (mulAdd A fuel k p l q) :=
  onCurve_mulAddAux h2 hp hq (add_spec h2 hp hq).1 fuel k l

/-- Simultaneous multiplication computes `k P + l Q`, when `k, l < 2^fuel`. -/
theorem toPoint_mulAdd (fuel k l : Nat) {p q : Coords K} (hp : OnCurve A B p)
    (hq : OnCurve A B q) (hk : k < 2 ^ fuel) (hl : l < 2 ^ fuel) :
    toPoint A B (mulAdd A fuel k p l q) = k • toPoint A B p + l • toPoint A B q :=
  toPoint_mulAddAux h2 hp hq (add_spec h2 hp hq).1 (add_spec h2 hp hq).2 fuel k l hk hl

end Field

end Coords

/-! ## The point of a form over the integers mod `m` -/

/-- The value in `ZMod m` is a change of representation. -/
theorem toZ_embedding [NeZero m] : Coords.Embedding (toZ (m := m)) :=
  ⟨toZ_zero, toZ_one, toZ_add, toZ_sub, toZ_mul, toZ_injective⟩

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
  ShortWeierstrass.nonsingular_of_eq h

variable (A B) in
/-- The group element of a form: `0` at infinity, and the affine point otherwise.

A form off the curve goes to `0`: every theorem assumes the form is on the curve. -/
noncomputable def toPoint (p : Jacobian m) : (ShortWeierstrass.curve A B).Point :=
  if h : p.z ≠ 0 ∧ affY p * affY p = affX p * affX p * affX p + A * affX p + B then
    .some _ _ (nonsingular h.2)
  else 0

theorem toZ_z_ne_zero {p : Jacobian m} (hz : p.z ≠ 0) : toZ p.z ≠ 0 :=
  fun h => hz (toZ_eq_zero.mp h)

omit [NeZero m] [(ShortWeierstrass.curve A B).IsElliptic] in
/-- The affine `x` of a form is that of its coordinates in `ZMod m`. -/
theorem affX_eq (p : Jacobian m) : affX p = Coords.affX (p.toCoords.map toZ) := rfl

omit [NeZero m] [(ShortWeierstrass.curve A B).IsElliptic] in
/-- The affine `y` of a form is that of its coordinates in `ZMod m`. -/
theorem affY_eq (p : Jacobian m) : affY p = Coords.affY (p.toCoords.map toZ) := rfl

omit [(ShortWeierstrass.curve A B).IsElliptic] in
/-- A form is on the curve exactly when its coordinates in `ZMod m` are. -/
theorem onCurve_iff {p : Jacobian m} : OnCurve A B p ↔ Coords.OnCurve A B (p.toCoords.map toZ) :=
  imp_congr_left toZ_eq_zero.not.symm

/-- A form has the group element of its coordinates in `ZMod m`. -/
theorem toPoint_eq (p : Jacobian m) : toPoint A B p = Coords.toPoint A B (p.toCoords.map toZ) := by
  unfold toPoint Coords.toPoint
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ⟨toZ_z_ne_zero h1.1, h1.2⟩ h2
  · exact absurd ⟨fun hz => h2.1 (by rw [← toZ_zero]; exact congrArg toZ hz), h2.2⟩ h1
  · rfl

theorem toPoint_of_z_eq_zero {p : Jacobian m} (hz : p.z = 0) : toPoint A B p = 0 := by
  rw [toPoint_eq]
  exact Coords.toPoint_of_z_eq_zero (show toZ p.z = 0 by rw [hz, toZ_zero])

theorem toPoint_of_z_ne_zero {p : Jacobian m} (hp : OnCurve A B p) (hz : p.z ≠ 0) :
    toPoint A B p = .some _ _ (nonsingular (hp hz)) := by
  rw [toPoint_eq, Coords.toPoint_of_z_ne_zero (onCurve_iff.mp hp) (toZ_z_ne_zero hz)]
  rfl

omit [(ShortWeierstrass.curve A B).IsElliptic] in
theorem onCurve_infinity : OnCurve A B (infinity : Jacobian m) := fun h => absurd rfl h

/-- A form with a nonzero `Z` and affine values `(x, y)` is on the curve and maps to `(x, y)`. -/
theorem spec_of_eq {r : Jacobian m} {x y : ZMod m}
    (h : (ShortWeierstrass.curve A B).Nonsingular x y) (hz : r.z ≠ 0)
    (hx : affX r = x) (hy : affY r = y) :
    OnCurve A B r ∧ toPoint A B r = .some x y h := by
  rw [onCurve_iff, toPoint_eq]
  exact Coords.spec_of_eq h (toZ_z_ne_zero hz) hx hy

/-! ## Back to affine coordinates -/

omit [Fact m.Prime] [(ShortWeierstrass.curve A B).IsElliptic] in
theorem toAffine_of_z_eq_zero {p : Jacobian m} (hz : p.z = 0) : p.toAffine = none := by
  simp [toAffine, Coords.toAffine, hz]

omit [(ShortWeierstrass.curve A B).IsElliptic] in
/-- A form with a nonzero `Z` gives the affine point `(X / Z^2, Y / Z^3)`. -/
theorem toAffine_of_z_ne_zero {p : Jacobian m} (hz : p.z ≠ 0) :
    ∃ x y, p.toAffine = some (x, y) ∧ toZ x = affX p ∧ toZ y = affY p := by
  refine ⟨p.x * (Fin.inverse p.z * Fin.inverse p.z),
    p.y * (Fin.inverse p.z * Fin.inverse p.z) * Fin.inverse p.z,
    by simp [toAffine, Coords.toAffine, hz], ?_, ?_⟩ <;>
    simp [affX, affY, div_eq_mul_inv, pow_succ, mul_assoc]

/-! ## The group law, from the coordinates in `ZMod m` -/

section Law

variable {a : Fin m} (ha : toZ a = A) (h2 : (2 : ZMod m) ≠ 0)

omit [(ShortWeierstrass.curve A B).IsElliptic] in
include ha in
/-- Doubling commutes with the value in `ZMod m`. -/
theorem map_double (p : Jacobian m) :
    (double a p).toCoords.map toZ = Coords.double A (p.toCoords.map toZ) := by
  rw [← ha]
  exact Coords.map_double toZ_embedding a p.toCoords

omit [(ShortWeierstrass.curve A B).IsElliptic] in
include ha in
/-- Addition commutes with the value in `ZMod m`. -/
theorem map_add (p q : Jacobian m) :
    (add a p q).toCoords.map toZ =
      Coords.add A (p.toCoords.map toZ) (q.toCoords.map toZ) := by
  rw [← ha]
  exact Coords.map_add toZ_embedding a p.toCoords q.toCoords

omit [(ShortWeierstrass.curve A B).IsElliptic] in
include ha in
/-- Double and add commutes with the value in `ZMod m`. -/
theorem map_mulBits (fuel k : Nat) (p : Jacobian m) :
    (mulBits a fuel k p).toCoords.map toZ = Coords.mulBits A fuel k (p.toCoords.map toZ) := by
  rw [← ha]
  exact Coords.map_mulBits toZ_embedding a fuel k p.toCoords

omit [(ShortWeierstrass.curve A B).IsElliptic] in
include ha in
/-- The joint chain commutes with the value in `ZMod m`. -/
theorem map_mulAddAux (p q pq : Jacobian m) (fuel k l : Nat) :
    (mulAddAux a p q pq fuel k l).toCoords.map toZ =
      Coords.mulAddAux A (p.toCoords.map toZ) (q.toCoords.map toZ) (pq.toCoords.map toZ)
        fuel k l := by
  rw [← ha]
  exact Coords.map_mulAddAux toZ_embedding a p.toCoords q.toCoords pq.toCoords fuel k l

include ha h2

/-- Doubling a form on the curve gives a form on the curve, with twice the group element.

The formula must use the curve's `a`, and 2 must be nonzero in the field. -/
theorem double_spec {p : Jacobian m} (hp : OnCurve A B p) :
    OnCurve A B (double a p) ∧ toPoint A B (double a p) = toPoint A B p + toPoint A B p := by
  rw [onCurve_iff, toPoint_eq, toPoint_eq, map_double ha]
  exact Coords.double_spec h2 (onCurve_iff.mp hp)

/-- Adding two forms on the curve gives a form on the curve, with the sum of the elements. -/
theorem add_spec {p q : Jacobian m} (hp : OnCurve A B p) (hq : OnCurve A B q) :
    OnCurve A B (add a p q) ∧ toPoint A B (add a p q) = toPoint A B p + toPoint A B q := by
  rw [onCurve_iff, toPoint_eq, toPoint_eq, toPoint_eq, map_add ha]
  exact Coords.add_spec h2 (onCurve_iff.mp hp) (onCurve_iff.mp hq)

/-! ## Scalar multiplication -/

/-- Double and add on forms stays on the curve. -/
theorem onCurve_mulBits (fuel k : Nat) {p : Jacobian m} (hp : OnCurve A B p) :
    OnCurve A B (mulBits a fuel k p) := by
  rw [onCurve_iff, map_mulBits ha]
  exact Coords.onCurve_mulBits h2 fuel k (onCurve_iff.mp hp)

/-- Double and add on forms computes `k P`, when `k < 2^fuel`. -/
theorem toPoint_mulBits (fuel k : Nat) {p : Jacobian m} (hp : OnCurve A B p) (hk : k < 2 ^ fuel) :
    toPoint A B (mulBits a fuel k p) = k • toPoint A B p := by
  rw [toPoint_eq, toPoint_eq, map_mulBits ha]
  exact Coords.toPoint_mulBits h2 fuel k (onCurve_iff.mp hp) hk

/-! ## Two scalar multiplications with shared doublings -/

/-- The joint chain stays on the curve. -/
theorem onCurve_mulAddAux {p q pq : Jacobian m} (hp : OnCurve A B p) (hq : OnCurve A B q)
    (hpq : OnCurve A B pq) (fuel k l : Nat) : OnCurve A B (mulAddAux a p q pq fuel k l) := by
  rw [onCurve_iff, map_mulAddAux ha]
  exact Coords.onCurve_mulAddAux h2 (onCurve_iff.mp hp) (onCurve_iff.mp hq) (onCurve_iff.mp hpq)
    fuel k l

/-- The joint chain computes `k P + l Q`, when `pq` is `P + Q` and `k, l < 2^fuel`. -/
theorem toPoint_mulAddAux {p q pq : Jacobian m} (hp : OnCurve A B p) (hq : OnCurve A B q)
    (hpq : OnCurve A B pq) (hsum : toPoint A B pq = toPoint A B p + toPoint A B q)
    (fuel k l : Nat) (hk : k < 2 ^ fuel) (hl : l < 2 ^ fuel) :
    toPoint A B (mulAddAux a p q pq fuel k l) = k • toPoint A B p + l • toPoint A B q := by
  rw [toPoint_eq, toPoint_eq, toPoint_eq, map_mulAddAux ha]
  rw [toPoint_eq, toPoint_eq, toPoint_eq] at hsum
  exact Coords.toPoint_mulAddAux h2 (onCurve_iff.mp hp) (onCurve_iff.mp hq) (onCurve_iff.mp hpq)
    hsum fuel k l hk hl

/-- Simultaneous multiplication stays on the curve. -/
theorem onCurve_mulAdd (fuel k l : Nat) {p q : Jacobian m} (hp : OnCurve A B p)
    (hq : OnCurve A B q) : OnCurve A B (mulAdd a fuel k p l q) :=
  onCurve_mulAddAux ha h2 hp hq (add_spec ha h2 hp hq).1 fuel k l

/-- Simultaneous multiplication computes `k P + l Q`, when `k, l < 2^fuel`. -/
theorem toPoint_mulAdd (fuel k l : Nat) {p q : Jacobian m} (hp : OnCurve A B p)
    (hq : OnCurve A B q) (hk : k < 2 ^ fuel) (hl : l < 2 ^ fuel) :
    toPoint A B (mulAdd a fuel k p l q) = k • toPoint A B p + l • toPoint A B q :=
  toPoint_mulAddAux ha h2 hp hq (add_spec ha h2 hp hq).1 (add_spec ha h2 hp hq).2 fuel k l hk hl

end Law

end EthLib.Cryptography.Jacobian

namespace EthLib.Cryptography.ShortWeierstrass.Point

open Jacobian (toZ)

/-! ## Points of a curve as forms, over a field -/

section Field

variable {F : Type} [Add F] [Sub F] [Mul F] [Neg F] [OfNat F 0] [OfNat F 1] [OfNat F 2]
  [OfNat F 3] [DecidableEq F] [Params F] {K : Type} [Field K] [DecidableEq K] {A B : K}
  [(curve A B).IsElliptic] {f : F → K}

/-- A point of the curve has a Jacobian form on the curve, with the same group element.

The map into the field must send `1` to `1`. -/
theorem toCoords_spec (hf : Embedding f A B) (hone : f 1 = 1) {p : Point F}
    (hp : p.isOnCurve = true) :
    Jacobian.Coords.OnCurve A B (p.toCoords.map f) ∧
      Jacobian.Coords.toPoint A B (p.toCoords.map f) = toPoint A B f p := by
  cases p with
  | infinity =>
    have hz : ((infinity : Point F).toCoords.map f).z = 0 := hf.map_zero
    exact ⟨fun h => absurd hz h, Jacobian.Coords.toPoint_of_z_eq_zero hz⟩
  | affine x y =>
    have h := (isOnCurve_affine hf x y).mp hp
    have hz : ((affine x y).toCoords.map f).z = 1 := hone
    have hx : Jacobian.Coords.affX ((affine x y).toCoords.map f) = f x := by
      simp only [Jacobian.Coords.affX, hz, one_pow, div_one]
      rfl
    have hy : Jacobian.Coords.affY ((affine x y).toCoords.map f) = f y := by
      simp only [Jacobian.Coords.affY, hz, one_pow, div_one]
      rfl
    have hs := Jacobian.Coords.spec_of_eq (nonsingular_of_eq h) (by rw [hz]; exact one_ne_zero)
      hx hy
    exact ⟨hs.1, hs.2.trans (toPoint_affine hf hp).symm⟩

variable {G : Type} [OfNat G 0] [OfNat G 1] [Add G] [Sub G] [Mul G] [DecidableEq G]
  {encode : F → G} {inverse : G → G} {read : G → F} {a : G}

/-- A Jacobian form on the curve, in a representation, gives a point with the same element.

Reading back must keep the operations, and the inverse must read as the inverse of the field. -/
theorem ofCoords_spec (hf : Embedding f A B) (hr : Jacobian.Coords.Embedding read)
    (hinv : ∀ x, f (read (inverse x)) = (f (read x))⁻¹) {q : Jacobian.Coords G}
    (hq : Jacobian.Coords.OnCurve A B (q.map fun x => f (read x))) :
    (ofCoords inverse read q).isOnCurve = true ∧
      toPoint A B f (ofCoords inverse read q) =
        Jacobian.Coords.toPoint A B (q.map fun x => f (read x)) := by
  by_cases hz : q.z = 0
  · have hz' : (q.map fun x => f (read x)).z = 0 := by
      show f (read q.z) = 0
      rw [hz, hr.map_zero, hf.map_zero]
    simp only [ofCoords, Jacobian.Coords.toAffine, hz, ↓reduceIte]
    exact ⟨rfl, (Jacobian.Coords.toPoint_of_z_eq_zero hz').symm⟩
  · have hz' : (q.map fun x => f (read x)).z ≠ 0 := by
      show f (read q.z) ≠ 0
      rw [← hf.map_zero, hf.injective.ne_iff, ← hr.map_zero, hr.injective.ne_iff]
      exact hz
    have he := hq hz'
    simp only [ofCoords, Jacobian.Coords.toAffine, hz, ↓reduceIte]
    have hx : f (read (q.x * (inverse q.z * inverse q.z))) =
        Jacobian.Coords.affX (q.map fun x => f (read x)) := by
      simp only [Jacobian.Coords.affX, Jacobian.Coords.map, hr.map_mul, hf.map_mul, hinv]
      ring
    have hy : f (read (q.y * (inverse q.z * inverse q.z) * inverse q.z)) =
        Jacobian.Coords.affY (q.map fun x => f (read x)) := by
      simp only [Jacobian.Coords.affY, Jacobian.Coords.map, hr.map_mul, hf.map_mul, hinv]
      ring
    rw [← hx, ← hy] at he
    have hon := (isOnCurve_affine hf _ _).mpr he
    refine ⟨hon, ?_⟩
    rw [toPoint_affine hf hon, Jacobian.Coords.toPoint_of_z_ne_zero hq hz']
    simp only [hx, hy]

omit [DecidableEq F] [DecidableEq K] [(curve A B).IsElliptic] [DecidableEq G] in
/-- Reading back is a map into the field when the map from the specification is one. -/
private theorem embedding_comp (hf : Embedding f A B) (hone : f 1 = 1)
    (hr : Jacobian.Coords.Embedding read) : Jacobian.Coords.Embedding fun x => f (read x) :=
  ⟨by simp only [hr.map_zero, hf.map_zero], by simp only [hr.map_one, hone],
    fun x y => by simp only [hr.map_add, hf.map_add],
    fun x y => by simp only [hr.map_sub, hf.map_sub],
    fun x y => by simp only [hr.map_mul, hf.map_mul],
    hf.injective.comp hr.injective⟩

omit [Add F] [Sub F] [Mul F] [Neg F] [OfNat F 2] [OfNat F 3] [DecidableEq F] [Params F]
  [Field K] [DecidableEq K] [(curve A B).IsElliptic] [OfNat G 0] [OfNat G 1] [Add G] [Sub G]
  [Mul G] [DecidableEq G] in
/-- Reading back an encoded form gives the form of the point. -/
private theorem map_encode (henc : ∀ x, read (encode x) = x) (p : Point F) :
    (p.toCoords.map encode).map (fun x => f (read x)) = p.toCoords.map f := by
  cases p <;> simp only [toCoords, Jacobian.Coords.infinity, Jacobian.Coords.map, henc]

/-- Double and add stays on the curve, in any representation of any field.

Reading back must keep the operations and undo the encoding.

The inverse must read as the inverse of the field.

The representation must hold the curve's `a`, and 2 must be nonzero. -/
theorem isOnCurve_mulBits_field (hf : Embedding f A B) (hone : f 1 = 1)
    (hr : Jacobian.Coords.Embedding read) (hinv : ∀ x, f (read (inverse x)) = (f (read x))⁻¹)
    (henc : ∀ x, read (encode x) = x) (ha : f (read a) = A) (h2 : (2 : K) ≠ 0)
    (fuel k : Nat) {p : Point F} (hp : p.isOnCurve = true) :
    (mulBits encode inverse read a fuel k p).isOnCurve = true := by
  have hon : Jacobian.Coords.OnCurve A B
      ((Jacobian.Coords.mulBits a fuel k (p.toCoords.map encode)).map fun x => f (read x)) := by
    simp only [Jacobian.Coords.map_mulBits (embedding_comp hf hone hr), ha, map_encode henc]
    exact Jacobian.Coords.onCurve_mulBits h2 fuel k (toCoords_spec hf hone hp).1
  exact (ofCoords_spec hf hr hinv hon).1

/-- Double and add computes `k P`, when `k < 2^fuel`, in any representation of any field.

Reading back must keep the operations and undo the encoding.

The inverse must read as the inverse of the field.

The representation must hold the curve's `a`, and 2 must be nonzero. -/
theorem toPoint_mulBits_field (hf : Embedding f A B) (hone : f 1 = 1)
    (hr : Jacobian.Coords.Embedding read) (hinv : ∀ x, f (read (inverse x)) = (f (read x))⁻¹)
    (henc : ∀ x, read (encode x) = x) (ha : f (read a) = A) (h2 : (2 : K) ≠ 0)
    (fuel k : Nat) {p : Point F} (hp : p.isOnCurve = true) (hk : k < 2 ^ fuel) :
    toPoint A B f (mulBits encode inverse read a fuel k p) = k • toPoint A B f p := by
  have hJ := toCoords_spec hf hone hp
  have hmap : (Jacobian.Coords.mulBits a fuel k (p.toCoords.map encode)).map
      (fun x => f (read x)) = Jacobian.Coords.mulBits A fuel k (p.toCoords.map f) := by
    simp only [Jacobian.Coords.map_mulBits (embedding_comp hf hone hr), ha, map_encode henc]
  have hon : Jacobian.Coords.OnCurve A B
      ((Jacobian.Coords.mulBits a fuel k (p.toCoords.map encode)).map fun x => f (read x)) := by
    rw [hmap]
    exact Jacobian.Coords.onCurve_mulBits h2 fuel k hJ.1
  rw [mulBits, (ofCoords_spec hf hr hinv hon).2, hmap,
    Jacobian.Coords.toPoint_mulBits h2 fuel k hJ.1 hk, hJ.2]

end Field

/-! ## Points of a curve as forms over the integers mod `m` -/

section Representation

variable {m : Nat} [NeZero m] {G : Type} [OfNat G 0] [OfNat G 1] [Add G] [Sub G] [Mul G]
  [DecidableEq G]

/-- A representation of `Fin m` for double and add, with its maps in and out, and its inverse.

Reading back is a change of representation, it keeps the inverse, and it undoes the encoding. -/
structure Representation (encode : Fin m → G) (inverse : G → G) (read : G → Fin m) : Prop where
  /-- Reading back keeps the operations, and distinct elements stay distinct. -/
  embedding : Jacobian.Coords.Embedding read
  /-- The inverse reads back as the inverse of `Fin m`. -/
  read_inverse : ∀ x, read (inverse x) = Fin.inverse (read x)
  /-- Reading back an encoded element gives that element. -/
  read_encode : ∀ x, read (encode x) = x

omit [DecidableEq G] in
/-- `Fin m` itself is a representation, with no conversion. -/
theorem Representation.fin : Representation (m := m) id Fin.inverse id :=
  ⟨Jacobian.Coords.Embedding.id, fun _ => rfl, fun _ => rfl⟩

/-- The point of a Jacobian form is its affine point, or the point at infinity. -/
theorem ofJacobian_eq (p : Jacobian m) :
    ofJacobian p = match p.toAffine with
      | none => infinity
      | some (x, y) => affine x y := by
  unfold ofJacobian ofCoords Jacobian.toAffine
  cases Jacobian.Coords.toAffine Fin.inverse p.toCoords <;> rfl

/-- Normalizing in another representation gives the point of the form read back into `Fin m`.

It needs the inverse of that representation to read as the inverse of `Fin m`. -/
theorem ofCoords_map {read : G → Fin m} (hf : Jacobian.Coords.Embedding read) {inv : G → G}
    (hinv : ∀ x, read (inv x) = Fin.inverse (read x)) (q : Jacobian.Coords G) :
    ofCoords inv read q = ofCoords Fin.inverse id (q.map read) := by
  unfold ofCoords
  rw [← Jacobian.Coords.map_toAffine hf hinv q]
  cases q.toAffine inv <;> rfl

/-- Double and add in a representation is double and add on `Fin m`, for every input. -/
theorem mulBits_eq_jacobian {encode : Fin m → G} {inverse : G → G} {read : G → Fin m}
    (hr : Representation encode inverse read) (a : G) (fuel k : Nat) (p : Point (Fin m)) :
    mulBits encode inverse read a fuel k p =
      ofJacobian (Jacobian.mulBits (read a) fuel k (toJacobian p)) := by
  rw [mulBits, ofCoords_map hr.embedding hr.read_inverse,
    Jacobian.Coords.map_mulBits hr.embedding]
  -- Reading back the encoded form of the point gives the form itself.
  have h : (p.toCoords.map encode).map read = p.toCoords := by
    simp only [Jacobian.Coords.map, hr.read_encode]
  rw [h]
  rfl

end Representation

variable {m : Nat} [NeZero m] [Fact m.Prime] [Params (Fin m)] {A B : ZMod m}
  [(curve A B).IsElliptic] {f : Fin m → ZMod m}

/-- A point of the curve has a Jacobian form on the curve, with the same group element.

The map into `ZMod m` must be the value of each element. -/
theorem toJacobian_spec (hf : Embedding f A B) (hz : ∀ x, toZ x = f x) {p : Point (Fin m)}
    (hp : p.isOnCurve = true) :
    Jacobian.OnCurve A B (toJacobian p) ∧
      Jacobian.toPoint A B (toJacobian p) = toPoint A B f p := by
  have hmap : (toJacobian p).toCoords.map toZ = p.toCoords.map f := by
    show p.toCoords.map toZ = _
    simp only [Jacobian.Coords.map, hz]
  rw [Jacobian.onCurve_iff, Jacobian.toPoint_eq, hmap]
  exact toCoords_spec hf ((hz 1).symm.trans Jacobian.toZ_one) hp

/-- A Jacobian form on the curve gives a point of the curve, with the same group element. -/
theorem ofJacobian_spec (hf : Embedding f A B) (hz : ∀ x, toZ x = f x) {p : Jacobian m}
    (hp : Jacobian.OnCurve A B p) :
    (ofJacobian p).isOnCurve = true ∧ toPoint A B f (ofJacobian p) = Jacobian.toPoint A B p := by
  have hmap : (p.toCoords.map fun x => f (id x)) = p.toCoords.map toZ := by
    simp only [Jacobian.Coords.map, id, hz]
  have hinv (x : Fin m) : f (id (Fin.inverse x)) = (f (id x))⁻¹ := by
    simp only [id, ← hz, Jacobian.toZ_inverse]
  rw [Jacobian.onCurve_iff, ← hmap] at hp
  rw [Jacobian.toPoint_eq, ← hmap]
  exact ofCoords_spec hf Representation.fin.embedding hinv hp

variable {G : Type} [OfNat G 0] [OfNat G 1] [Add G] [Sub G] [Mul G] [DecidableEq G]
  {encode : Fin m → G} {inverse : G → G} {read : G → Fin m} {a : G}

omit [Params (Fin m)] [DecidableEq G] in
/-- In a representation of `Fin m`, the inverse reads as the inverse of `ZMod m`. -/
private theorem read_inverse_field (hz : ∀ x, toZ x = f x)
    (hr : Representation encode inverse read) (x : G) :
    f (read (inverse x)) = (f (read x))⁻¹ := by
  rw [hr.read_inverse, ← hz, ← hz, Jacobian.toZ_inverse]

/-- Double and add stays on the curve.

The representation must hold the curve's `a`, and 2 must be nonzero in `ZMod m`. -/
theorem isOnCurve_mulBits (hf : Embedding f A B) (hz : ∀ x, toZ x = f x)
    (hr : Representation encode inverse read) (ha : toZ (read a) = A) (h2 : (2 : ZMod m) ≠ 0)
    (fuel k : Nat) {p : Point (Fin m)} (hp : p.isOnCurve = true) :
    (mulBits encode inverse read a fuel k p).isOnCurve = true :=
  isOnCurve_mulBits_field hf ((hz 1).symm.trans Jacobian.toZ_one) hr.embedding
    (read_inverse_field hz hr) hr.read_encode ((hz _).symm.trans ha) h2 fuel k hp

/-- Double and add computes `k P`, when `k < 2^fuel`. -/
theorem toPoint_mulBits (hf : Embedding f A B) (hz : ∀ x, toZ x = f x)
    (hr : Representation encode inverse read) (ha : toZ (read a) = A) (h2 : (2 : ZMod m) ≠ 0)
    (fuel k : Nat) {p : Point (Fin m)} (hp : p.isOnCurve = true) (hk : k < 2 ^ fuel) :
    toPoint A B f (mulBits encode inverse read a fuel k p) = k • toPoint A B f p :=
  toPoint_mulBits_field hf ((hz 1).symm.trans Jacobian.toZ_one) hr.embedding
    (read_inverse_field hz hr) hr.read_encode ((hz _).symm.trans ha) h2 fuel k hp hk

end EthLib.Cryptography.ShortWeierstrass.Point
