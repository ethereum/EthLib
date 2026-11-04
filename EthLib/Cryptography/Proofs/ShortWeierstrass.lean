module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Proofs: short Weierstrass curves

Mathlib proves a group law for every Weierstrass curve.

This file restates it for `y^2 = x^3 + a x + b`, case by case as SEC 1 v2 §2.2.1 states it.

Over `ZMod p`, it also counts the points.
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

/-- Rule 5: a point with `y != -y` doubles along the tangent.

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

end EthLib.Cryptography.ShortWeierstrass
