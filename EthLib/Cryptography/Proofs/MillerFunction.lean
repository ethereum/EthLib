module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Proofs: Miller's algorithm on an elliptic curve

Miller's algorithm evaluates, at a point `P`, a function whose divisor is a multiple of `(Q) - (O)`.

It multiplies values of the function `g_{T,S} = L_{T,S} / L_{T+S,-(T+S)}`.

Here `L_{T,S}` is the normalized line through `T` and `S`: the tangent when `T = S`.

The line through `R` and `-R` is the vertical through `R`.

The curve is in Weierstrass form, and the functions are evaluated at the coordinates `(xp, yp)`.

The loop below walks the bits of `s` from the top, which is the binary addition chain of `s`.

A doubling step multiplies `f^2` by `g_{T,T}` and doubles `T`.

An addition step multiplies `f` by `g_{T,Q}` and adds `Q` to `T`.

See Miller, "The Weil Pairing, and Its Efficient Calculation", J. Cryptology 17 (2004).

Section 4.1 defines `L` (Proposition 2), `g` (Definition 5) and `f_{n,Q}` (Definition 6).

Its Lemma 2, equation (8), gives the doubling and addition rules, and Algorithm 1 the loop.

By that lemma, the loop computes `f_{s,Q}(P)` when no value it divides by is zero.

No theorem here proves that equality; the loop is the definition.
-/

@[expose] public section

namespace EthLib.Cryptography.Miller

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F)

/-- The normalized line through `T` and `S`, at `(xp, yp)`.

The line through `(x1, y1)` with slope `m` is `m (x - x1) + y1 - y`.

A vertical line through `(x1, y1)` is `x - x1`, and so is the line through it and `O`.

The line through `O` and `O` is the constant 1. -/
noncomputable def line : W.Point → W.Point → F → F → F
  | .zero, .zero, _, _ => 1
  | .some x _ _, .zero, xp, _ => xp - x
  | .zero, .some x _ _, xp, _ => xp - x
  | .some x₁ y₁ _, .some x₂ y₂ _, xp, yp =>
    if x₁ = x₂ ∧ y₁ = W.negY x₂ y₂ then xp - x₁
    else W.slope x₁ x₂ y₁ y₂ * (xp - x₁) + y₁ - yp

/-- The function `g_{T,S} = L_{T,S} / L_{T+S,-(T+S)}`, at `(xp, yp)`. -/
noncomputable def lineRatio (T S : W.Point) (xp yp : F) : F :=
  line W T S xp yp / line W (T + S) (-(T + S)) xp yp

/-- Walk bits `n - 1` down to `0` of `s` from `(T, f)`.

At each bit it doubles `T`, then adds `Q` if the bit is set. -/
noncomputable def steps (s : ℕ) (Q : W.Point) (xp yp : F) : ℕ → W.Point → F → F
  | 0, _, f => f
  | n + 1, T, f =>
    if s.testBit n then
      steps s Q xp yp n (T + T + Q) (f ^ 2 * lineRatio W T T xp yp * lineRatio W (T + T) Q xp yp)
    else steps s Q xp yp n (T + T) (f ^ 2 * lineRatio W T T xp yp)

/-- Miller's algorithm for `s`, the point `Q` and the coordinates `(xp, yp)`.

The start `T = Q` and `f = 1` consume the leading bit of `s`. -/
noncomputable def loop (s : ℕ) (Q : W.Point) (xp yp : F) : F :=
  steps W s Q xp yp s.log2 Q 1

/-- The bits of `s` from `n` up are twice those from `n + 1` up, plus bit `n`. -/
theorem shiftRight_split (s n : ℕ) :
    s >>> n = 2 * (s >>> (n + 1)) + if s.testBit n then 1 else 0 := by
  have h1 : s >>> (n + 1) = (s >>> n) / 2 := Nat.shiftRight_succ s n
  have h2 : s.testBit n = true ↔ (s >>> n) % 2 = 1 := by
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, decide_eq_true_iff]
  split_ifs with h
  · have := h2.mp h
    omega
  · have : ¬(s >>> n % 2 = 1) := fun e => h (h2.mpr e)
    omega

/-- The leading bit of a nonzero `s` is 1: the loop starts from it. -/
theorem shiftRight_log2 {s : ℕ} (hs : s ≠ 0) : s >>> s.log2 = 1 := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt_le (by simpa using Nat.log2_self_le hs)
    (by simpa [pow_succ, mul_comm] using Nat.lt_log2_self (n := s))

/-- With no bit left, the loop returns `f`. -/
theorem steps_zero (s : ℕ) (Q T : W.Point) (xp yp f : F) : steps W s Q xp yp 0 T f = f := rfl

/-- One step: double, then add `Q` if the bit is set. -/
theorem steps_succ (s : ℕ) (Q T : W.Point) (xp yp f : F) (n : ℕ) :
    steps W s Q xp yp (n + 1) T f =
      if s.testBit n then
        steps W s Q xp yp n (T + T + Q)
          (f ^ 2 * lineRatio W T T xp yp * lineRatio W (T + T) Q xp yp)
      else steps W s Q xp yp n (T + T) (f ^ 2 * lineRatio W T T xp yp) := rfl

/-- The vertical through a finite point `R`, at `(xp, yp)`, is `xp - x`. -/
theorem line_neg_self {x y : F} (h : W.Nonsingular x y) (xp yp : F) :
    line W (.some x y h) (-(.some x y h)) xp yp = xp - x := by
  simp only [Point.neg_some, line, negY_negY, and_self, ite_true]

/-- The line through `O` and `O` is 1. -/
theorem line_zero_zero (xp yp : F) : line W 0 0 xp yp = 1 := rfl

/-- The line through two finite points that are not opposite has the slope of the curve. -/
theorem line_some_some {x₁ y₁ x₂ y₂ : F} (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) (xp yp : F) :
    line W (.some x₁ y₁ h₁) (.some x₂ y₂ h₂) xp yp =
      W.slope x₁ x₂ y₁ y₂ * (xp - x₁) + y₁ - yp := by
  simp only [line, hxy, ite_false]

/-- Miller's algorithm for the point `O` gives 1. -/
theorem loop_zero (s : ℕ) (xp yp : F) : loop W s 0 xp yp = 1 := by
  have hr : lineRatio W 0 0 xp yp = 1 := by
    simp only [lineRatio, add_zero, neg_zero, line_zero_zero, div_one]
  have h : ∀ n, steps W s 0 xp yp n 0 1 = 1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [steps_succ]
      split_ifs <;> simpa only [add_zero, hr, one_pow, mul_one] using ih
  exact h _

end EthLib.Cryptography.Miller
