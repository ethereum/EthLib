module

public import EthLib.Cryptography.ShortWeierstrass
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Proofs: short Weierstrass curves

Mathlib proves a group law for every Weierstrass curve.

This file restates it for `y^2 = x^3 + a x + b`, case by case as SEC 1 v2 §2.2.1 states it.

Over `ZMod p`, it also counts the points.

The points of the specification map into that group, through a map of their field into a field.
-/

@[expose] public section

namespace EthLib.Cryptography.ShortWeierstrass

open WeierstrassCurve WeierstrassCurve.Affine

section Field

variable {F : Type*} [Field F]

/-- The curve `y^2 = x^3 + a x + b`, as a Weierstrass curve with `a_1 = a_2 = a_3 = 0`. -/
def curve (a b : F) : WeierstrassCurve.Affine F :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := a, a₆ := b }

variable {a b : F}

/-- The discriminant of the curve is `-16 (4 a^3 + 27 b^2)`. -/
theorem discriminant_eq (a b : F) : (curve a b).Δ = -16 * (4 * a ^ 3 + 27 * b ^ 2) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, curve]
  ring

/-- The equation of the curve. -/
theorem equation_iff (x y : F) : (curve a b).Equation x y ↔ y * y = x * x * x + a * x + b := by
  rw [Affine.equation_iff]
  simp only [curve]
  constructor <;> intro h <;> linear_combination h

/-- On a smooth curve, every solution of the equation is a nonsingular point. -/
theorem nonsingular_of_eq [(curve a b).IsElliptic] {x y : F}
    (h : y * y = x * x * x + a * x + b) : (curve a b).Nonsingular x y :=
  equation_iff_nonsingular.mp ((equation_iff x y).mpr h)

/-- The negation of a point negates `y`, since `a_1 = a_3 = 0`. -/
@[simp] theorem negY_eq (x y : F) : (curve a b).negY x y = -y := by
  simp [Affine.negY, curve]

/-- Two points of the curve with the same `x` are equal or opposite. -/
theorem y_eq_or_eq_neg {x y1 y2 : F} (h1 : y1 * y1 = x * x * x + a * x + b)
    (h2 : y2 * y2 = x * x * x + a * x + b) : y2 = y1 ∨ y2 = -y1 := by
  have : (y2 - y1) * (y2 + y1) = 0 := by linear_combination h2 - h1
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

variable [DecidableEq F]

/-- Rule 3: opposite points sum to `0`. -/
theorem add_of_y_eq_neg {x y1 y2 : F} (h1 : (curve a b).Nonsingular x y1) (h2 : (curve a b).Nonsingular x y2)
    (hy : y2 = -y1) : Point.some _ _ h1 + Point.some _ _ h2 = 0 :=
  Point.add_of_Y_eq rfl (by rw [negY_eq, hy, neg_neg])

/-- Rule 4: two points with different `x` add along the chord.

Its slope is `l = (y2 - y1) / (x2 - x1)`. -/
theorem add_of_x_ne {x1 y1 x2 y2 : F} (h1 : (curve a b).Nonsingular x1 y1) (h2 : (curve a b).Nonsingular x2 y2)
    (hx : x1 ≠ x2) {l x3 y3 : F} (hl : l = (y2 - y1) * (x2 - x1)⁻¹) (hx3 : x3 = l * l - x1 - x2)
    (hy3 : y3 = l * (x1 - x3) - y1) : ∃ h3, Point.some _ _ h1 + Point.some _ _ h2 = Point.some x3 y3 h3 := by
  have hslope : (curve a b).slope x1 x2 y1 y2 = l := by
    rw [slope_of_X_ne hx, hl, div_eq_mul_inv, ← neg_sub x2 x1, inv_neg, ← neg_sub y2 y1]
    ring
  have hX : x3 = (curve a b).addX x1 x2 ((curve a b).slope x1 x2 y1 y2) := by
    rw [hslope, hx3]
    simp only [Affine.addX, curve]
    ring
  have hY : y3 = (curve a b).addY x1 x2 y1 ((curve a b).slope x1 x2 y1 y2) := by
    rw [Affine.addY, Affine.negAddY, negY_eq, ← hX, hy3, hslope]
    ring
  subst hX hY
  exact ⟨_, Point.add_of_X_ne hx⟩

/-- Rule 5: a point whose `y` differs from `-y` doubles along the tangent.

Its slope is `l = (3 x^2 + a) / (2 y)`. -/
theorem add_self_of_y_ne {x y : F} (h : (curve a b).Nonsingular x y) (hy : y ≠ -y) {l x3 y3 : F}
    (hl : l = (3 * x * x + a) * (2 * y)⁻¹) (hx3 : x3 = l * l - x - x) (hy3 : y3 = l * (x - x3) - y) :
    ∃ h3, Point.some _ _ h + Point.some _ _ h = Point.some x3 y3 h3 := by
  have hne : y ≠ (curve a b).negY x y := by rwa [negY_eq]
  have hslope : (curve a b).slope x x y y = l := by
    rw [slope_of_Y_ne rfl hne, hl, negY_eq]
    simp only [curve]
    ring
  have hX : x3 = (curve a b).addX x x ((curve a b).slope x x y y) := by
    rw [hslope, hx3]
    simp only [Affine.addX, curve]
    ring
  have hY : y3 = (curve a b).addY x x y ((curve a b).slope x x y y) := by
    rw [Affine.addY, Affine.negAddY, negY_eq, ← hX, hy3, hslope]
    ring
  subst hX hY
  exact ⟨_, Point.add_self_of_Y_ne hne⟩

/-- A point of order 2 is `(x, 0)`, so `x` is a root of `x^3 + a x + b`. -/
theorem addOrderOf_ne_two (h2 : (2 : F) ≠ 0) (hroot : ∀ x : F, x * x * x + a * x + b ≠ 0)
    (X : (curve a b).Point) : addOrderOf X ≠ 2 := by
  intro h
  have h2X : (2 : Nat) • X = 0 := h ▸ addOrderOf_nsmul_eq_zero X
  cases X with
  | zero => rw [← Point.zero_def, addOrderOf_zero] at h; omega
  | some x y hn =>
    -- `2 X = 0` makes `X = -X`, so `y = -y`, so `y = 0`.
    have hneg : Point.some x y hn = -Point.some x y hn := by
      rw [two_nsmul] at h2X
      exact eq_neg_of_add_eq_zero_left h2X
    rw [Point.neg_some, Point.some.injEq, negY_eq] at hneg
    have hy : y = 0 := by
      have : 2 * y = 0 := by linear_combination hneg.2
      exact (mul_eq_zero.mp this).resolve_left h2
    have he := (equation_iff x y).mp hn.1
    rw [hy] at he
    exact hroot x (by linear_combination -he)

end Field

/-! ## The number of points over `ZMod p` -/

section ZMod

variable {p : Nat} [Fact p.Prime] {a b : ZMod p}

/-- `y` and `-y` have opposite parities, unless `y = 0`, since `p` is odd. -/
theorem val_neg_mod_two (hp : p % 2 = 1) {y : ZMod p} (hy : y ≠ 0) : (-y).val % 2 ≠ y.val % 2 := by
  rw [ZMod.neg_val, ite_eq_right hy]
  have hlt := ZMod.val_lt y
  omega

/-- A group element as its `x` and the parity of its `y`, or `none` for `0`. -/
def pointCode : (curve a b).Point → Option (ZMod p × Bool)
  | 0 => none
  | .some x y _ => some (x, decide (y.val % 2 = 1))

/-- A point is fixed by its `x` and the parity of its `y`. -/
theorem pointCode_injective (hp : p % 2 = 1) : Function.Injective (pointCode (a := a) (b := b)) := by
  intro P Q h
  cases P with
  | zero => cases Q with
    | zero => rfl
    | some => cases h
  | some x1 y1 h1 => cases Q with
    | zero => cases h
    | some x2 y2 h2 =>
      simp only [pointCode, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, hb⟩ := h
      have hpar : y1.val % 2 = y2.val % 2 := by
        have := decide_eq_decide.mp hb
        omega
      have hy : y1 = y2 := by
        rcases y_eq_or_eq_neg ((equation_iff _ _).mp h1.1) ((equation_iff _ _).mp h2.1) with h | h
        · exact h.symm
        · by_cases hy : y1 = 0
          · rw [h, hy, neg_zero]
          · exact absurd (h ▸ hpar.symm) (val_neg_mod_two hp hy)
      subst hy
      rfl

instance : Finite (curve a b).Point :=
  -- A point is `0` or its two coordinates.
  Finite.of_injective (fun P : (curve a b).Point => match P with
    | 0 => (none : Option (ZMod p × ZMod p))
    | .some x y _ => some (x, y)) (by
    intro P Q h
    cases P <;> cases Q <;> simp_all)

/-- At most `2 p + 1` points: `0`, and at most two for each `x`. -/
theorem card_point_le (hp : p % 2 = 1) : Nat.card (curve a b).Point ≤ 2 * p + 1 := by
  have := Nat.card_le_card_of_injective _ (pointCode_injective (a := a) (b := b) hp)
  rwa [Finite.card_option, Nat.card_prod, Nat.card_zmod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
    mul_comm] at this

/-- The group has `n` points, if a point has order `n`, `2 p + 1 < 3 n` and the cubic has no root.

The order `n` divides the number of points, which is then `n` or `2 n`.

A group of `2 n` points has a point of order 2, which is a root of the cubic. -/
theorem card_point_eq (hp : p % 2 = 1) (hroot : ∀ x : ZMod p, x * x * x + a * x + b ≠ 0) {n : Nat}
    {G : (curve a b).Point} (hG : addOrderOf G = n) (hlt : 2 * p + 1 < 3 * n) :
    Nat.card (curve a b).Point = n := by
  obtain ⟨m, hm⟩ : n ∣ Nat.card (curve a b).Point := hG ▸ addOrderOf_dvd_natCard _
  have hle := card_point_le (a := a) (b := b) hp
  have hpos : 0 < Nat.card (curve a b).Point := Nat.card_pos
  have hm2 : m ≤ 2 := by
    by_contra hc
    have : n * 3 ≤ n * m := Nat.mul_le_mul_left _ (by omega)
    omega
  have hm0 : m ≠ 0 := by
    rintro rfl
    omega
  rcases (show m = 1 ∨ m = 2 by omega) with rfl | rfl
  · simpa using hm
  · -- `m = 2` gives a point of order 2.
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h
      have hdvd := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
      have := Nat.le_of_dvd (by norm_num) hdvd
      have := (Fact.out : p.Prime).two_le
      interval_cases p
      simp at hp
    obtain ⟨X, hX⟩ := exists_prime_addOrderOf_dvd_card' 2 (hm ▸ dvd_mul_left 2 _)
    exact absurd hX (addOrderOf_ne_two h2 hroot X)

end ZMod

/-! ## The points of the specification

Addition and negation are the group's, and points on the curve and group elements correspond.

So the group law is proved once, and each curve gives only its map.
-/

section Points

variable {F : Type} [Add F] [Sub F] [Mul F] [Neg F] [OfNat F 0] [OfNat F 2] [OfNat F 3]
  [DecidableEq F] [Params F] {K : Type} [Field K]

/-- A map from the field of a specification into a field, for the curve with coefficients `A, B`.

It is injective, and it keeps the operations and the numerals of the addition rule.

It sends the inverse of the specification to the inverse of the field, and `a, b` to `A, B`. -/
structure Embedding (f : F → K) (A B : K) : Prop where
  /-- Distinct elements stay distinct. -/
  injective : Function.Injective f
  /-- Sums are kept. -/
  map_add : ∀ x y, f (x + y) = f x + f y
  /-- Differences are kept. -/
  map_sub : ∀ x y, f (x - y) = f x - f y
  /-- Products are kept. -/
  map_mul : ∀ x y, f (x * y) = f x * f y
  /-- Negations are kept. -/
  map_neg : ∀ x, f (-x) = -f x
  /-- `0` maps to `0`. -/
  map_zero : f 0 = 0
  /-- `2` maps to `2`. -/
  map_two : f 2 = 2
  /-- `3` maps to `3`. -/
  map_three : f 3 = 3
  /-- The inverse of the specification is the inverse of the field. -/
  map_inv : ∀ x, f (Params.inv x) = (f x)⁻¹
  /-- The coefficient `a` maps to `A`. -/
  map_a : f Params.a = A
  /-- The constant term `b` maps to `B`. -/
  map_b : f Params.b = B

namespace Point

variable {A B : K} {f : F → K}

variable (A B f) in
/-- The group element of a point, through a map of its field.

A pair off the curve has none, and goes to `0`.

The group-law theorems assume the point is on the curve. -/
def toPoint [DecidableEq K] [(curve A B).IsElliptic] : Point F → (curve A B).Point
  | infinity => 0
  | affine x y =>
    if h : f y * f y = f x * f x * f x + A * f x + B then .some _ _ (nonsingular_of_eq h) else 0

/-- The curve test, as an equation in the field. -/
theorem isOnCurve_affine (hf : Embedding f A B) (x y : F) :
    (affine x y).isOnCurve = true ↔ f y * f y = f x * f x * f x + A * f x + B := by
  simp only [isOnCurve, beq_iff_eq]
  rw [← hf.injective.eq_iff]
  split_ifs with ha
  · -- When `a = 0`, the rule skips the term `a x`, which is `0` in the field.
    rw [← hf.map_a, ha, hf.map_zero, zero_mul, add_zero]
    simp only [hf.map_add, hf.map_mul, hf.map_b]
  · simp only [hf.map_add, hf.map_mul, hf.map_a, hf.map_b]

theorem isOnCurve_neg (hf : Embedding f A B) {p : Point F} (h : p.isOnCurve = true) :
    (-p).isOnCurve = true := by
  cases p with
  | infinity => rfl
  | affine x y =>
    show (affine x (-y)).isOnCurve = true
    rw [isOnCurve_affine hf] at h ⊢
    rw [hf.map_neg, neg_mul_neg]
    exact h

variable [DecidableEq K] [(curve A B).IsElliptic]

theorem toPoint_affine (hf : Embedding f A B) {x y : F} (h : (affine x y).isOnCurve = true) :
    toPoint A B f (affine x y) =
      .some _ _ (nonsingular_of_eq ((isOnCurve_affine hf x y).mp h)) :=
  dite_eq_left ((isOnCurve_affine hf x y).mp h)

omit [Add F] [Sub F] [Mul F] [Neg F] [OfNat F 0] [OfNat F 2] [OfNat F 3] [DecidableEq F]
  [Params F] in
@[simp] theorem toPoint_infinity : toPoint A B f infinity = 0 := rfl

theorem toPoint_neg (hf : Embedding f A B) {p : Point F} (h : p.isOnCurve = true) :
    toPoint A B f (-p) = -toPoint A B f p := by
  cases p with
  | infinity => exact neg_zero.symm
  | affine x y =>
    show toPoint A B f (affine x (-y)) = _
    rw [toPoint_affine hf h, toPoint_affine hf (isOnCurve_neg hf h), Affine.Point.neg_some]
    simp only [negY_eq, hf.map_neg]

/-! ### Addition -/

/-- A pair that maps to the coordinates of a group element is on the curve, and is that element. -/
private theorem affine_of_eq (hf : Embedding f A B) {x3 y3 : F} {P : (curve A B).Point}
    (h : ∃ h3, P = .some (f x3) (f y3) h3) :
    (affine x3 y3).isOnCurve = true ∧ toPoint A B f (affine x3 y3) = P := by
  obtain ⟨h3, rfl⟩ := h
  have hc : (affine x3 y3).isOnCurve = true :=
    (isOnCurve_affine hf x3 y3).mpr ((equation_iff _ _).mp h3.1)
  exact ⟨hc, toPoint_affine hf hc⟩

/-- The rule for two points of the curve, both away from infinity. -/
private theorem add_affine (hf : Embedding f A B) {x1 y1 x2 y2 : F}
    (h1 : (affine x1 y1).isOnCurve = true) (h2 : (affine x2 y2).isOnCurve = true) :
    (affine x1 y1 + affine x2 y2).isOnCurve = true ∧
      toPoint A B f (affine x1 y1 + affine x2 y2) =
        toPoint A B f (affine x1 y1) + toPoint A B f (affine x2 y2) := by
  have e1 := (isOnCurve_affine hf x1 y1).mp h1
  have e2 := (isOnCurve_affine hf x2 y2).mp h2
  rw [toPoint_affine hf h1, toPoint_affine hf h2]
  show (add (affine x1 y1) (affine x2 y2)).isOnCurve = true ∧
    toPoint A B f (add (affine x1 y1) (affine x2 y2)) = _
  simp only [add]
  by_cases hx : x1 = x2
  · subst hx
    rw [ite_eq_left rfl]
    by_cases hy : y2 = -y1
    · -- Rule 3: opposite points sum to `O`.
      rw [ite_eq_left hy, add_of_y_eq_neg _ _ (by rw [hy, hf.map_neg])]
      exact ⟨rfl, rfl⟩
    · -- Same `x`, not opposite: the points are equal, and rule 5 doubles.
      rw [ite_eq_right hy]
      have hy2 : y2 = y1 := by
        rcases y_eq_or_eq_neg e1 e2 with h | h
        · exact hf.injective h
        · exact absurd (hf.injective (h.trans (hf.map_neg y1).symm)) hy
      subst hy2
      have hne : f y2 ≠ -f y2 := fun h => hy (hf.injective (by rw [hf.map_neg]; exact h))
      -- The numerator of the tangent's slope maps to `3 x^2 + A`, also when the rule skips `a`.
      have hn : f (if (Params.a : F) = 0 then 3 * x1 * x1 else 3 * x1 * x1 + Params.a) =
          3 * f x1 * f x1 + A := by
        split_ifs with ha
        · rw [← hf.map_a, ha, hf.map_zero, add_zero, hf.map_mul, hf.map_mul, hf.map_three]
        · rw [hf.map_add, hf.map_mul, hf.map_mul, hf.map_three, hf.map_a]
      refine affine_of_eq hf (add_self_of_y_ne (l := f ((if (Params.a : F) = 0 then 3 * x1 * x1
        else 3 * x1 * x1 + Params.a) * Params.inv (2 * y2))) _ hne ?_ ?_ ?_)
      · rw [hf.map_mul, hn, hf.map_inv, hf.map_mul, hf.map_two]
      all_goals simp only [hf.map_mul, hf.map_sub]
  · -- Rule 4: different `x`, the chord.
    rw [ite_eq_right hx]
    have hX : f x1 ≠ f x2 := fun h => hx (hf.injective h)
    refine affine_of_eq hf
      (add_of_x_ne (l := f ((y2 - y1) * Params.inv (x2 - x1))) _ _ hX ?_ ?_ ?_)
    · rw [hf.map_mul, hf.map_inv, hf.map_sub, hf.map_sub]
    all_goals simp only [hf.map_mul, hf.map_sub]

theorem isOnCurve_add (hf : Embedding f A B) {p q : Point F} (hp : p.isOnCurve = true)
    (hq : q.isOnCurve = true) : (p + q).isOnCurve = true := by
  cases p with
  | infinity => exact hq
  | affine x1 y1 =>
    cases q with
    | infinity => exact hp
    | affine x2 y2 => exact (add_affine hf hp hq).1

theorem toPoint_add (hf : Embedding f A B) {p q : Point F} (hp : p.isOnCurve = true)
    (hq : q.isOnCurve = true) : toPoint A B f (p + q) = toPoint A B f p + toPoint A B f q := by
  cases p with
  | infinity => exact (zero_add _).symm
  | affine x1 y1 =>
    cases q with
    | infinity => exact (add_zero _).symm
    | affine x2 y2 => exact (add_affine hf hp hq).2

/-! ### Points and group elements correspond -/

/-- Two points on the curve with the same group element are equal. -/
theorem toPoint_inj (hf : Embedding f A B) {p q : Point F} (hp : p.isOnCurve = true)
    (hq : q.isOnCurve = true) : toPoint A B f p = toPoint A B f q ↔ p = q := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  cases p with
  | infinity =>
    cases q with
    | infinity => rfl
    | affine x y => rw [toPoint_affine hf hq] at h; cases h
  | affine x1 y1 =>
    cases q with
    | infinity => rw [toPoint_affine hf hp] at h; cases h
    | affine x2 y2 =>
      rw [toPoint_affine hf hp, toPoint_affine hf hq, Affine.Point.some.injEq] at h
      rw [hf.injective h.1, hf.injective h.2]

/-- Only the point at infinity goes to `0`. -/
theorem toPoint_eq_zero (hf : Embedding f A B) {p : Point F} (hp : p.isOnCurve = true) :
    toPoint A B f p = 0 ↔ p = infinity :=
  toPoint_inj hf (q := infinity) hp rfl

/-- A pair off the curve goes to `0`. -/
theorem toPoint_eq_zero_of_isOnCurve_eq_false (hf : Embedding f A B) {p : Point F}
    (hp : p.isOnCurve = false) : toPoint A B f p = 0 := by
  cases p with
  | infinity => cases hp
  | affine x y =>
    have h : ¬(f y * f y = f x * f x * f x + A * f x + B) :=
      fun h => by simp [(isOnCurve_affine hf x y).mpr h] at hp
    exact dite_eq_right_iff.mpr fun h0 => absurd h0 h

/-- Every group element is the element of a point on the curve, when the map is onto. -/
theorem toPoint_surjective (hf : Embedding f A B) (hs : Function.Surjective f)
    (P : (curve A B).Point) : ∃ p : Point F, p.isOnCurve = true ∧ toPoint A B f p = P := by
  cases P with
  | zero => exact ⟨infinity, rfl, rfl⟩
  | some x y h =>
    obtain ⟨x, rfl⟩ := hs x
    obtain ⟨y, rfl⟩ := hs y
    have hc : (affine x y).isOnCurve = true :=
      (isOnCurve_affine hf x y).mpr ((equation_iff _ _).mp h.1)
    exact ⟨affine x y, hc, toPoint_affine hf hc⟩

end Point

end Points

end EthLib.Cryptography.ShortWeierstrass
