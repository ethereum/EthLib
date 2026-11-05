module

public import EthLib.Cryptography.Proofs.MillerLines

/-!
# Proofs: Weil reciprocity for products of lines

Weil reciprocity says that `f(div g) = g(div f)` for two functions `f` and `g` on a curve.

Miller states it for two functions whose divisors have disjoint supports.

Here `f` and `g` are quotients of products of lines.

Every line has its only pole at `O`, so `O` may lie in both supports.

At `O`, each line takes the value 1, the leading coefficient of its expansion there.

Then `f(div g) = (-1)^(m n) g(div f)`, where `m` and `n` are the multiplicities of `O`.

The divisors are the formal sums given to the lines, and `m` and `n` are read from them.

The proof is direct.

For two lines, both sides are products over the points where each line meets the curve.

The cubic that a line cuts out of the curve gives the identity, for every pair of lines.

The law for quotients follows when the lines of `f` and of `g` share no finite point.

See Miller, "The Weil Pairing, and Its Efficient Calculation", J. Cryptology 17 (2004).

Its Section 4 defines the value at a divisor (Definition 2).

It states Weil reciprocity as Proposition 1.

Its Section 4.1 gives the divisor of a line (Proposition 2).
-/

@[expose] public section

namespace EthLib.Cryptography.Miller

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}

/-! ## The value and the zeros of a line -/

/-- The value of the line through two points at a point of the curve, with 1 at `O`. -/
noncomputable def lineAt (l : W.Point × W.Point) : W.Point → F
  | .zero => 1
  | .some x y _ => line W l.1 l.2 x y

/-- The points where the line through `T` and `S` meets the curve: `T`, `S` and `-(T + S)`.

A vertical meets the curve at `O` as well.

The constant line through `O` and `O` meets it only at `O`, three times. -/
def lineZeros (l : W.Point × W.Point) : Multiset W.Point := {l.1, l.2, -(l.1 + l.2)}

@[simp] theorem lineAt_zero (l : W.Point × W.Point) : lineAt l 0 = 1 := rfl

/-- The multiplicity of a point in the divisor of a line.

It is the count of the point among the zeros of the line, less 3 at `O`. -/
theorem lineDivisor_apply (T S R : W.Point) :
    lineDivisor W T S R = ((lineZeros (T, S)).count R : ℤ) - if R = 0 then 3 else 0 := by
  rw [lineDivisor, Finsupp.sub_apply, Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_apply,
    Finsupp.single_apply, Finsupp.single_apply, Finsupp.single_apply, lineZeros,
    Multiset.insert_eq_cons, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_cons,
    Multiset.count_singleton]
  simp only [eq_comm (a := T), eq_comm (a := S), eq_comm (a := -(T + S)),
    eq_comm (a := (0 : W.Point))]
  split_ifs <;> omega

/-! ## The three kinds of line -/

/-- A line is the constant 1, a vertical `x - a`, or a line `l(x) - y` through three points. -/
private inductive Shape (l : W.Point × W.Point) : Prop
  | one : lineZeros l = {0, 0, 0} → (∀ R, lineAt l R = 1) → Shape l
  | vertical (a b : F) (h : W.Nonsingular a b) :
      lineZeros l = {.some a b h, -.some a b h, 0} →
      (∀ x y (h' : W.Nonsingular x y), lineAt l (.some x y h') = x - a) → Shape l
  | slope (x₁ y₁ ℓ x₂ y₂ x₃ y₃ : F) (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
      (h₃ : W.Nonsingular x₃ y₃) :
      lineZeros l = {.some x₁ y₁ h₁, .some x₂ y₂ h₂, .some x₃ y₃ h₃} →
      (∀ x y (h' : W.Nonsingular x y),
        lineAt l (.some x y h') = (linePolynomial x₁ y₁ ℓ).eval x - y) →
      (linePolynomial x₁ y₁ ℓ).eval x₂ = y₂ → (linePolynomial x₁ y₁ ℓ).eval x₃ = y₃ →
      W.addPolynomial x₁ y₁ ℓ = -((X - C x₁) * (X - C x₂) * (X - C x₃)) → Shape l

private theorem shape (l : W.Point × W.Point) : Shape l := by
  obtain ⟨T, S⟩ := l
  rcases T with _ | ⟨x₁, y₁, h₁⟩ <;> rcases S with _ | ⟨x₂, y₂, h₂⟩
  · exact .one (by simp [lineZeros, ← Point.zero_def]) fun R => by cases R <;> rfl
  · refine .vertical x₂ y₂ h₂ ?_ fun x y h' => rfl
    simp only [lineZeros, ← Point.zero_def, zero_add, Multiset.insert_eq_cons]
    rw [Multiset.cons_swap, ← Multiset.singleton_add, ← Multiset.singleton_add,
      ← Multiset.singleton_add, ← Multiset.singleton_add]
    abel
  · refine .vertical x₁ y₁ h₁ ?_ fun x y h' => rfl
    simp only [lineZeros, ← Point.zero_def, add_zero, Multiset.insert_eq_cons]
    rw [Multiset.cons_inj_right]
    exact Multiset.pair_comm _ _
  · by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
    · refine .vertical x₁ y₁ h₁ ?_ fun x y h' => by simp [lineAt, line, hxy]
      obtain ⟨rfl, rfl⟩ := hxy
      simp only [lineZeros, Point.add_of_Y_eq rfl rfl, neg_zero, Point.neg_some, negY_negY]
    · have h₃ := nonsingular_negAdd h₁ h₂ hxy
      refine .slope x₁ y₁ (W.slope x₁ x₂ y₁ y₂) x₂ y₂ _ _ h₁ h₂ h₃ ?_ ?_ ?_ ?_
        (addPolynomial_slope h₁.1 h₂.1 hxy)
      · simp only [lineZeros, Point.add_some hxy, Point.neg_some, addY, negY_negY]
      · intro x y h'
        simp only [lineAt, line, hxy, ite_false, linePolynomial, eval_add, eval_mul, eval_C,
          eval_sub, eval_X]
      · simp only [linePolynomial, eval_add, eval_mul, eval_C, eval_sub, eval_X]
        by_cases hx : x₁ = x₂
        · have hy : y₁ ≠ W.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
          rw [Y_eq_of_Y_ne h₁.1 h₂.1 hx hy, hx, sub_self, mul_zero, zero_add]
        · rw [slope_of_X_ne hx]
          field_simp [sub_ne_zero.mpr hx]
          ring
      · simp only [linePolynomial, negAddY, eval_add, eval_mul, eval_C, eval_sub, eval_X]

omit [DecidableEq F] in
/-- The cubic that the line `y = l(x)` cuts out of the curve, at `x`. -/
private theorem eval_addPolynomial (x₁ y₁ ℓ x : F) :
    (W.addPolynomial x₁ y₁ ℓ).eval x =
      ((linePolynomial x₁ y₁ ℓ).eval x) ^ 2 + W.a₁ * x * (linePolynomial x₁ y₁ ℓ).eval x +
        W.a₃ * (linePolynomial x₁ y₁ ℓ).eval x - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by
  rw [addPolynomial, WeierstrassCurve.Affine.polynomial]
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  ring

/-! ## Where a line vanishes -/

/-- The value of a line at a finite point of the curve is the value that the loop uses. -/
theorem lineAt_some (l : W.Point × W.Point) {x y : F} (h : W.Nonsingular x y) :
    lineAt l (.some x y h) = line W l.1 l.2 x y := rfl

/-- A line vanishes at a point of the curve only where it meets the curve. -/
theorem mem_lineZeros_of_lineAt_eq_zero {l : W.Point × W.Point} {R : W.Point}
    (h : lineAt l R = 0) : R ∈ lineZeros l := by
  rcases R with _ | ⟨x, y, hR⟩
  · exact absurd h one_ne_zero
  rcases shape l with ⟨hz, hv⟩ | ⟨a, b, hab, hz, hv⟩ |
    ⟨x₁, y₁, ℓ, x₂, y₂, x₃, y₃, h₁, h₂, h₃, hz, hv, e₂, e₃, hp⟩
  · rw [hv] at h
    exact absurd h one_ne_zero
  · rw [hv, sub_eq_zero] at h
    rw [hz]
    subst h
    rcases Y_eq_of_X_eq hR.1 hab.1 rfl with rfl | rfl
    · simp
    · simp [Point.neg_some]
  · rw [hv, sub_eq_zero] at h
    have he := hR.1
    rw [equation_iff, ← h] at he
    have hx := congrArg (eval x) hp
    rw [eval_addPolynomial] at hx
    simp only [eval_neg, eval_mul, eval_sub, eval_X, eval_C] at hx
    have h0 : (x - x₁) * (x - x₂) * (x - x₃) = 0 := by linear_combination hx - he
    have e₁ : (linePolynomial x₁ y₁ ℓ).eval x₁ = y₁ := by simp [linePolynomial]
    rw [hz]
    rcases mul_eq_zero.mp h0 with h0 | h0
    · rcases mul_eq_zero.mp h0 with h0 | h0 <;> rw [sub_eq_zero] at h0 <;> subst h0
      · rw [e₁] at h
        subst h
        simp
      · rw [e₂] at h
        subst h
        simp
    · rw [sub_eq_zero] at h0
      subst h0
      rw [e₃] at h
      subst h
      simp

/-! ## Reciprocity for two lines -/

omit [DecidableEq F] in
/-- Reciprocity between a vertical `x - a` and a line `y = l(x)` through three points. -/
private theorem vertical_slope (a b x₁ y₁ ℓ u₁ u₂ u₃ : F) (hab : W.Equation a b)
    (hp : W.addPolynomial x₁ y₁ ℓ = -((X - C u₁) * (X - C u₂) * (X - C u₃))) :
    (u₁ - a) * (u₂ - a) * (u₃ - a) =
      ((linePolynomial x₁ y₁ ℓ).eval a - b) *
        ((linePolynomial x₁ y₁ ℓ).eval a - (-b - W.a₁ * a - W.a₃)) := by
  have hx := congrArg (eval a) hp
  rw [eval_addPolynomial] at hx
  simp only [eval_neg, eval_mul, eval_sub, eval_X, eval_C] at hx
  rw [equation_iff] at hab
  linear_combination -hx + hab

/-- Reciprocity between two lines `y = l(x)` and `y = m(x)`, each through three points. -/
private theorem slope_slope (x₁ y₁ ℓ x₂ y₂ x₃ y₃ u₁ v₁ μ u₂ v₂ u₃ v₃ : F)
    (e₂ : (linePolynomial x₁ y₁ ℓ).eval x₂ = y₂) (e₃ : (linePolynomial x₁ y₁ ℓ).eval x₃ = y₃)
    (f₂ : (linePolynomial u₁ v₁ μ).eval u₂ = v₂) (f₃ : (linePolynomial u₁ v₁ μ).eval u₃ = v₃)
    (hp : W.addPolynomial x₁ y₁ ℓ = -((X - C x₁) * (X - C x₂) * (X - C x₃)))
    (hq : W.addPolynomial u₁ v₁ μ = -((X - C u₁) * (X - C u₂) * (X - C u₃))) :
    ((linePolynomial x₁ y₁ ℓ).eval u₁ - v₁) * ((linePolynomial x₁ y₁ ℓ).eval u₂ - v₂) *
        ((linePolynomial x₁ y₁ ℓ).eval u₃ - v₃) =
      -(((linePolynomial u₁ v₁ μ).eval x₁ - y₁) * ((linePolynomial u₁ v₁ μ).eval x₂ - y₂) *
        ((linePolynomial u₁ v₁ μ).eval x₃ - y₃)) := by
  simp only [linePolynomial, eval_add, eval_mul, eval_C, eval_sub, eval_X] at e₂ e₃ f₂ f₃ ⊢
  rw [← e₂, ← e₃, ← f₂, ← f₃]
  by_cases hα : ℓ = μ
  · subst hα
    ring
  set c := ((v₁ - μ * u₁) - (y₁ - ℓ * x₁)) / (ℓ - μ)
  have hα' : ℓ - μ ≠ 0 := sub_ne_zero.mpr hα
  have hd (t : F) : ℓ * (t - x₁) + y₁ - (μ * (t - u₁) + v₁) = (ℓ - μ) * (t - c) := by
    simp only [c]
    field_simp
    ring
  have hc : ℓ * (c - x₁) + y₁ = μ * (c - u₁) + v₁ := by
    have := hd c
    rwa [sub_self, mul_zero, sub_eq_zero] at this
  have hpc := congrArg (eval c) hp
  have hqc := congrArg (eval c) hq
  rw [eval_addPolynomial] at hpc hqc
  simp only [linePolynomial, eval_neg, eval_mul, eval_sub, eval_X, eval_C, eval_add] at hpc hqc
  rw [hc] at hpc
  have hd' (t : F) : μ * (t - u₁) + v₁ - (ℓ * (t - x₁) + y₁) = -((ℓ - μ) * (t - c)) := by
    rw [← hd]
    ring
  have g₁ : ℓ * (u₁ - x₁) + y₁ - v₁ = (ℓ - μ) * (u₁ - c) := by
    rw [← hd]
    ring
  have g₁' : μ * (x₁ - u₁) + v₁ - y₁ = -((ℓ - μ) * (x₁ - c)) := by
    rw [← neg_sub, ← hd]
    ring
  rw [g₁, g₁', hd, hd, hd', hd']
  linear_combination (ℓ - μ) ^ 3 * (hpc - hqc)

omit [DecidableEq F] in
/-- If `A = ε B` with `ε = ±1`, then `B = ε A`. -/
private theorem eq_neg_one_zpow_mul_symm {A B : F} {k : ℤ} (h : A = (-1) ^ k * B) :
    B = (-1) ^ k * A := by
  have hε : ((-1 : F) ^ k) * (-1) ^ k = 1 := by
    rw [← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]
    norm_num
  rw [h, ← mul_assoc, hε, one_mul]

/-- Reciprocity for two lines, when the first has at most as many finite zeros. -/
private theorem prod_lineAt_lineZeros_of_le (T S U V : W.Point)
    (hle : lineDivisor W U V 0 ≤ lineDivisor W T S 0) :
    ((lineZeros (U, V)).map (lineAt (T, S))).prod =
      (-1) ^ (lineDivisor W T S 0 * lineDivisor W U V 0) *
        ((lineZeros (T, S)).map (lineAt (U, V))).prod := by
  rw [lineDivisor_apply, lineDivisor_apply] at hle ⊢
  rcases shape (T, S) with ⟨hz, hv⟩ | ⟨a, b, hab, hz, hv⟩ |
    ⟨x₁, y₁, ℓ, x₂, y₂, x₃, y₃, h₁, h₂, h₃, hz, hv, e₂, e₃, hp⟩ <;>
  rcases shape (U, V) with ⟨hz', hv'⟩ | ⟨c, d, hcd, hz', hv'⟩ |
    ⟨u₁, v₁, μ, u₂, v₂, u₃, v₃, k₁, k₂, k₃, hz', hv', f₂, f₃, hq⟩ <;>
  rw [hz, hz'] at hle ⊢ <;>
  simp [Point.neg_some, hv, hv'] at hle ⊢
  case vertical.vertical => ring
  case vertical.slope =>
    norm_num
    linear_combination vertical_slope a b u₁ v₁ μ u₁ u₂ u₃ hab.1 hq
  case slope.slope =>
    norm_num
    linear_combination slope_slope x₁ y₁ ℓ x₂ y₂ x₃ y₃ u₁ v₁ μ u₂ v₂ u₃ v₃ e₂ e₃ f₂ f₃ hp hq

/-- Weil reciprocity for two lines.

Take the product of the values of the first line at the zeros of the second.

It equals the product of the values of the second line at the zeros of the first, up to a sign.

The sign is -1 to the product of the multiplicities of `O` in the two divisors.

So it is -1 exactly when neither line is vertical or constant. -/
theorem prod_lineAt_lineZeros (m n : W.Point × W.Point) :
    ((lineZeros n).map (lineAt m)).prod =
      (-1) ^ (lineDivisor W m.1 m.2 0 * lineDivisor W n.1 n.2 0) *
        ((lineZeros m).map (lineAt n)).prod := by
  obtain ⟨T, S⟩ := m
  obtain ⟨U, V⟩ := n
  rcases le_total (lineDivisor W U V 0) (lineDivisor W T S 0) with h | h
  · exact prod_lineAt_lineZeros_of_le T S U V h
  · rw [mul_comm (lineDivisor W T S 0)]
    exact eq_neg_one_zpow_mul_symm (prod_lineAt_lineZeros_of_le U V T S h)

/-! ## Products of lines -/

/-- The value of a product of lines at a point of the curve, with 1 at `O`. -/
noncomputable def linesAt (M : Multiset (W.Point × W.Point)) (R : W.Point) : F :=
  (M.map fun l => lineAt l R).prod

/-- The zeros of the lines of a multiset, with multiplicity. -/
def linesZeros (M : Multiset (W.Point × W.Point)) : Multiset W.Point := M.bind lineZeros

@[simp] theorem linesAt_zero (M : Multiset (W.Point × W.Point)) : linesAt M 0 = 1 := by
  simp [linesAt]

/-- The empty product of lines is the constant 1. -/
@[simp] theorem linesAt_empty : linesAt (0 : Multiset (W.Point × W.Point)) = fun _ => (1 : F) :=
  funext fun _ => by simp [linesAt]

/-- At a finite point, the value of a product of lines is the value that the loop uses. -/
theorem linesAt_some (M : Multiset (W.Point × W.Point)) {x y : F} (h : W.Nonsingular x y) :
    linesAt M (.some x y h) = linesValue W M x y := rfl

/-- At a finite point, Miller's algorithm is a quotient of two values of products of lines. -/
theorem loop_eq_linesAt (s : ℕ) (Q : W.Point) {xp yp : F} (h : W.Nonsingular xp yp) :
    loop W s Q xp yp =
      linesAt (lines W s Q).1 (.some xp yp h) / linesAt (lines W s Q).2 (.some xp yp h) :=
  loop_eq_linesValue s Q xp yp

/-- One more line multiplies the value by the value of that line. -/
theorem linesAt_cons (l : W.Point × W.Point) (M : Multiset (W.Point × W.Point)) (R : W.Point) :
    linesAt (l ::ₘ M) R = lineAt l R * linesAt M R := by
  rw [linesAt, Multiset.map_cons, Multiset.prod_cons, linesAt]

/-- One more line adds its three zeros. -/
theorem linesZeros_cons (l : W.Point × W.Point) (M : Multiset (W.Point × W.Point)) :
    linesZeros (l ::ₘ M) = lineZeros l + linesZeros M :=
  Multiset.cons_bind _ _ _

/-- The zeros of a union are the zeros of the two parts. -/
theorem linesZeros_add (M N : Multiset (W.Point × W.Point)) :
    linesZeros (M + N) = linesZeros M + linesZeros N :=
  Multiset.add_bind _ _ _

/-- The multiplicity of a point in the divisor of a product of lines.

It is the count of the point among the zeros, less 3 for each line at `O`. -/
theorem linesDivisor_apply (M : Multiset (W.Point × W.Point)) (R : W.Point) :
    linesDivisor W M R =
      ((linesZeros M).count R : ℤ) - if R = 0 then 3 * (M.card : ℤ) else 0 := by
  induction M using Multiset.induction with
  | empty => simp [linesDivisor, linesZeros]
  | cons l M ih =>
    rw [← Multiset.insert_eq_cons, linesDivisor_insert, Finsupp.add_apply, ih, lineDivisor_apply,
      Multiset.insert_eq_cons, linesZeros_cons, Multiset.count_add, Multiset.card_cons]
    split_ifs <;> push_cast <;> ring

/-- A product of lines vanishes at a point of the curve only at a zero of one of its lines. -/
theorem mem_linesZeros_of_linesAt_eq_zero {M : Multiset (W.Point × W.Point)} {R : W.Point}
    (h : linesAt M R = 0) : R ∈ linesZeros M := by
  obtain ⟨l, hl, hl0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp h)
  exact Multiset.mem_bind.mpr ⟨l, hl, mem_lineZeros_of_lineAt_eq_zero hl0⟩

/-- Reciprocity between one line and a product of lines. -/
private theorem prod_lineAt_linesZeros (m : W.Point × W.Point) (N : Multiset (W.Point × W.Point)) :
    ((linesZeros N).map (lineAt m)).prod =
      (-1) ^ (lineDivisor W m.1 m.2 0 * linesDivisor W N 0) *
        ((lineZeros m).map (linesAt N)).prod := by
  induction N using Multiset.induction with
  | empty => simp [linesZeros, linesAt, linesDivisor]
  | cons n N ih =>
    have e : linesAt (n ::ₘ N) = fun R => lineAt n R * linesAt N R := funext (linesAt_cons n N)
    rw [linesZeros_cons, Multiset.map_add, Multiset.prod_add, ih, prod_lineAt_lineZeros, e,
      Multiset.prod_map_mul, ← Multiset.insert_eq_cons, linesDivisor_insert, Finsupp.add_apply,
      mul_add, zpow_add₀ (by norm_num)]
    ring

/-- Weil reciprocity for two products of lines.

The sign is -1 to the product of the multiplicities of `O` in the two divisors. -/
theorem prod_linesAt_linesZeros (M N : Multiset (W.Point × W.Point)) :
    ((linesZeros N).map (linesAt M)).prod =
      (-1) ^ (linesDivisor W M 0 * linesDivisor W N 0) *
        ((linesZeros M).map (linesAt N)).prod := by
  induction M using Multiset.induction with
  | empty => simp [linesZeros, linesDivisor]
  | cons m M ih =>
    have e : linesAt (m ::ₘ M) = fun R => lineAt m R * linesAt M R := funext (linesAt_cons m M)
    rw [e, Multiset.prod_map_mul, ih, prod_lineAt_linesZeros, linesZeros_cons, Multiset.map_add,
      Multiset.prod_add, ← Multiset.insert_eq_cons, linesDivisor_insert, Finsupp.add_apply,
      add_mul, zpow_add₀ (by norm_num)]
    ring

/-! ## Values at divisors -/

/-- The value of a function at a divisor: the product of `φ(R)^n` over the points `R`.

Here `n` is the multiplicity of `R` in the divisor.

This extends Definition 2 of Miller (2004), Section 4, to every function and divisor. -/
noncomputable def evalDivisor (φ : W.Point → F) (D : W.Point →₀ ℤ) : F :=
  D.prod fun R n => φ R ^ n

/-- The value at the divisor of a quotient of products of lines.

Take a function worth 1 at `O` and not zero at the zeros of the lines.

At the divisor, it takes its product over the zeros of the numerator, over that of the denominator.
-/
theorem evalDivisor_sub_linesDivisor {φ : W.Point → F} (h0 : φ 0 = 1)
    {N D : Multiset (W.Point × W.Point)} (hφ : ∀ R ∈ linesZeros N + linesZeros D, φ R ≠ 0) :
    evalDivisor φ (linesDivisor W N - linesDivisor W D) =
      ((linesZeros N).map φ).prod / ((linesZeros D).map φ).prod := by
  set s := (linesZeros N + linesZeros D).toFinset ∪ {0}
  have hs : (linesDivisor W N - linesDivisor W D).support ⊆ s := by
    intro R hR
    rw [Finsupp.mem_support_iff, Finsupp.sub_apply, linesDivisor_apply, linesDivisor_apply] at hR
    simp only [s, Finset.mem_union, Multiset.mem_toFinset, Finset.mem_singleton, Multiset.mem_add]
    by_contra hc
    simp only [not_or] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    simp [Multiset.count_eq_zero.mpr h1, Multiset.count_eq_zero.mpr h2, h3] at hR
  have hcount (Z : Multiset W.Point) (hZ : Z.toFinset ⊆ s) :
      (Z.map φ).prod = ∏ R ∈ s, φ R ^ (Z.count R : ℤ) := by
    rw [Finset.prod_multiset_map_count Z φ]
    simp only [← zpow_natCast]
    refine Finset.prod_subset hZ fun R _ hR => ?_
    rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at hR
    rw [hR, Nat.cast_zero, zpow_zero]
  rw [evalDivisor, Finsupp.prod_of_support_subset _ hs _ fun _ _ => zpow_zero _,
    hcount (linesZeros N) (fun R hR => by simp_all [s]),
    hcount (linesZeros D) (fun R hR => by simp_all [s]), ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun R hR => ?_
  rw [Finsupp.sub_apply, linesDivisor_apply, linesDivisor_apply]
  by_cases hR0 : R = 0
  · simp [hR0, h0]
  · have hRs : R ∈ linesZeros N + linesZeros D := by
      simpa [s, hR0] using hR
    simp only [hR0, ite_false, sub_zero]
    rw [zpow_sub₀ (hφ R hRs)]

/-- Weil reciprocity for two quotients of products of lines, `f = N₁ / D₁` and `g = N₂ / D₂`.

The lines of `f` and the lines of `g` must meet the curve at no common finite point.

Then `f(div g) = ε g(div f)`, with both functions worth 1 at `O`.

The sign `ε` is -1 to the product of the multiplicities of `O` in the two divisors. -/
theorem weil_reciprocity {N₁ D₁ N₂ D₂ : Multiset (W.Point × W.Point)}
    (h : ∀ R ∈ linesZeros (N₁ + D₁), R ∈ linesZeros (N₂ + D₂) → R = 0) :
    evalDivisor (fun R => linesAt N₁ R / linesAt D₁ R) (linesDivisor W N₂ - linesDivisor W D₂) =
      (-1) ^ ((linesDivisor W N₁ - linesDivisor W D₁) 0 *
          (linesDivisor W N₂ - linesDivisor W D₂) 0) *
        evalDivisor (fun R => linesAt N₂ R / linesAt D₂ R)
          (linesDivisor W N₁ - linesDivisor W D₁) := by
  have hne {M : Multiset (W.Point × W.Point)} {Z : Multiset W.Point}
      (hM : ∀ R ∈ linesZeros M, R ∈ Z → R = 0) (R : W.Point) (hR : R ∈ Z) :
      linesAt M R ≠ 0 := by
    intro h0
    have hR0 := hM R (mem_linesZeros_of_linesAt_eq_zero h0) hR
    rw [hR0, linesAt_zero] at h0
    exact one_ne_zero h0
  rw [linesZeros_add, linesZeros_add] at h
  have h₁ : ∀ R ∈ linesZeros N₂ + linesZeros D₂, linesAt N₁ R ≠ 0 ∧ linesAt D₁ R ≠ 0 :=
    fun R hR => ⟨hne (fun R h₁ h₂ => h R (Multiset.mem_add.mpr (.inl h₁)) h₂) R hR,
      hne (fun R h₁ h₂ => h R (Multiset.mem_add.mpr (.inr h₁)) h₂) R hR⟩
  have h₂ : ∀ R ∈ linesZeros N₁ + linesZeros D₁, linesAt N₂ R ≠ 0 ∧ linesAt D₂ R ≠ 0 :=
    fun R hR => ⟨hne (fun R h₁ h₂ => h R h₂ (Multiset.mem_add.mpr (.inl h₁))) R hR,
      hne (fun R h₁ h₂ => h R h₂ (Multiset.mem_add.mpr (.inr h₁))) R hR⟩
  rw [evalDivisor_sub_linesDivisor (by simp) fun R hR => div_ne_zero (h₁ R hR).1 (h₁ R hR).2,
    evalDivisor_sub_linesDivisor (by simp) fun R hR => div_ne_zero (h₂ R hR).1 (h₂ R hR).2]
  simp only [Multiset.prod_map_div]
  rw [prod_linesAt_linesZeros N₁ N₂, prod_linesAt_linesZeros D₁ N₂,
    prod_linesAt_linesZeros N₁ D₂, prod_linesAt_linesZeros D₁ D₂]
  have hp {Z : Multiset W.Point} {M : Multiset (W.Point × W.Point)}
      (hZ : ∀ R ∈ Z, linesAt M R ≠ 0) : (Z.map (linesAt M)).prod ≠ 0 :=
    Multiset.prod_ne_zero fun h0 => by
      obtain ⟨R, hR, hR0⟩ := Multiset.mem_map.mp h0
      exact hZ R hR hR0
  have a₁ := hp (M := N₂) (Z := linesZeros N₁) fun R hR => (h₂ R (by simp [hR])).1
  have a₂ := hp (M := N₂) (Z := linesZeros D₁) fun R hR => (h₂ R (by simp [hR])).1
  have a₃ := hp (M := D₂) (Z := linesZeros N₁) fun R hR => (h₂ R (by simp [hR])).2
  have a₄ := hp (M := D₂) (Z := linesZeros D₁) fun R hR => (h₂ R (by simp [hR])).2
  have hm1 : (-1 : F) ≠ 0 := by norm_num
  have hε : ∀ k : ℤ, (-1 : F) ^ k ≠ 0 := fun k => zpow_ne_zero k hm1
  rw [Finsupp.sub_apply, Finsupp.sub_apply,
    show (linesDivisor W N₁ 0 - linesDivisor W D₁ 0) * (linesDivisor W N₂ 0 - linesDivisor W D₂ 0) =
      linesDivisor W N₁ 0 * linesDivisor W N₂ 0 + linesDivisor W D₁ 0 * linesDivisor W D₂ 0 -
        (linesDivisor W D₁ 0 * linesDivisor W N₂ 0 + linesDivisor W N₁ 0 * linesDivisor W D₂ 0)
      by ring,
    zpow_sub₀ hm1, zpow_add₀ hm1, zpow_add₀ hm1]
  have := hε (linesDivisor W N₁ 0 * linesDivisor W N₂ 0)
  have := hε (linesDivisor W D₁ 0 * linesDivisor W D₂ 0)
  have := hε (linesDivisor W D₁ 0 * linesDivisor W N₂ 0)
  have := hε (linesDivisor W N₁ 0 * linesDivisor W D₂ 0)
  field_simp

end EthLib.Cryptography.Miller
