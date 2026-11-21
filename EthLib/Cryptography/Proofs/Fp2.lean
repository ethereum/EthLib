module

public import EthLib.Cryptography.Fp2
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Proofs: the quadratic extension is a field

The extension `F[i] / (i^2 + 1)` is a field when `F` is one and `-1` is not a square in `F`.

The base field is read through an injective map into a Mathlib field that respects its operations.

Each ring law is then a polynomial identity on the two coordinates, checked in that field.

The norm `c0^2 + c1^2` of `c0 + c1 i` is zero only at zero, so every nonzero element is invertible.

In the integers mod a prime `p = 3 mod 4`, `-1` is not a square, by Euler's criterion.
-/

@[expose] public section

namespace EthLib.Cryptography

/-- An injective map of the field operations of `F` into a field of Mathlib, respecting each one. -/
structure FieldOps.Embedding (F K : Type) [FieldOps F] [Field K] where
  /-- The map of elements. -/
  toFun : F → K
  injective : Function.Injective toFun
  map_add : ∀ a b, toFun (a + b) = toFun a + toFun b
  map_sub : ∀ a b, toFun (a - b) = toFun a - toFun b
  map_mul : ∀ a b, toFun (a * b) = toFun a * toFun b
  map_neg : ∀ a, toFun (-a) = -toFun a
  map_zero : toFun FieldOps.zero = 0
  map_one : toFun FieldOps.one = 1
  map_inverse : ∀ a, toFun (FieldOps.inverse a) = (toFun a)⁻¹

namespace Fp2

/-- In the integers mod a prime `p = 3 mod 4`, `-1` is not a square. -/
theorem zmod_mul_self_ne_neg_one {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) (y : ZMod p) :
    y * y ≠ -1 := by
  intro h
  have hp2 : p ≠ 2 := by omega
  have hy : y ≠ 0 := by
    rintro rfl
    simp at h
  -- Fermat gives `y^(p - 1) = 1`, and `p - 1 = 2 k` with `k` odd.
  have hf := ZMod.pow_card_sub_one_eq_one hy
  rw [show p - 1 = 2 * (2 * (p / 4) + 1) by omega, pow_mul, sq, h, pow_succ, pow_mul, neg_one_sq,
    one_pow, one_mul] at hf
  -- So `-1 = 1`, and `p` divides `2`, which only `2` among the primes does.
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by
    push_cast
    linear_combination -hf
  rw [ZMod.natCast_eq_zero_iff] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h2)

/-- The derived boolean equality compares both coordinates, so it is equality. -/
instance {F : Type} [BEq F] [LawfulBEq F] : LawfulBEq (Fp2 F) where
  eq_of_beq {a b} h := by
    cases a; cases b
    change (_ && _) = true at h
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
    rw [h.1, h.2]
  rfl {a} := by
    cases a
    change (_ && _) = true
    simp

variable {F K : Type} [FieldOps F] [Field K]

/-! ## Components -/

omit [FieldOps F] in
@[ext]
protected theorem ext {a b : Fp2 F} (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) : a = b := by
  cases a; cases b; simp_all

instance : Zero (Fp2 F) := ⟨zero⟩
instance : One (Fp2 F) := ⟨one⟩

@[simp] theorem zero_c0 : (0 : Fp2 F).c0 = FieldOps.zero := rfl
@[simp] theorem zero_c1 : (0 : Fp2 F).c1 = FieldOps.zero := rfl
@[simp] theorem one_c0 : (1 : Fp2 F).c0 = FieldOps.one := rfl
@[simp] theorem one_c1 : (1 : Fp2 F).c1 = FieldOps.zero := rfl
@[simp] theorem add_c0 (a b : Fp2 F) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : Fp2 F) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem sub_c0 (a b : Fp2 F) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 (a b : Fp2 F) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem neg_c0 (a : Fp2 F) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 (a : Fp2 F) : (-a).c1 = -a.c1 := rfl
@[simp] theorem mul_c0 (a b : Fp2 F) : (a * b).c0 = a.c0 * b.c0 - a.c1 * b.c1 := rfl
@[simp] theorem mul_c1 (a b : Fp2 F) : (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 := rfl

theorem inverse_c0 (a : Fp2 F) :
    a.inverse.c0 = a.c0 * FieldOps.inverse (a.c0 * a.c0 + a.c1 * a.c1) := rfl

theorem inverse_c1 (a : Fp2 F) :
    a.inverse.c1 = -(a.c1 * FieldOps.inverse (a.c0 * a.c0 + a.c1 * a.c1)) := rfl

/-! ## The norm -/

/-- The norm `c0^2 + c1^2` is zero only at zero, when `-1` is not a square. -/
theorem norm_eq_zero (hsq : ∀ y : K, y * y ≠ -1) {c0 c1 : K} (h : c0 * c0 + c1 * c1 = 0) :
    c0 = 0 ∧ c1 = 0 := by
  by_cases hc1 : c1 = 0
  · subst hc1
    exact ⟨mul_self_eq_zero.mp (by simpa using h), rfl⟩
  · -- Division by `c1^2` gives `(c0 / c1)^2 = -1`, which has no solution.
    refine absurd ?_ (hsq (c0 * c1⁻¹))
    have hinv : c1 * c1⁻¹ = 1 := mul_inv_cancel₀ hc1
    linear_combination (c1⁻¹ * c1⁻¹) * h - (c1 * c1⁻¹ + 1) * hinv

/-! ## The laws

Each law holds after the map into the field of Mathlib, coordinate by coordinate. -/

section Laws

variable (e : FieldOps.Embedding F K)
include e

/-- Pushes the map through each operation of the base field. -/
local macro "push_map" : tactic =>
  `(tactic| simp only [zero_c0, zero_c1, one_c0, one_c1, add_c0, add_c1, sub_c0, sub_c1, neg_c0,
    neg_c1, mul_c0, mul_c1, e.map_add, e.map_sub, e.map_mul, e.map_neg, e.map_zero, e.map_one])

protected theorem add_comm (a b : Fp2 F) : a + b = b + a := by
  apply Fp2.ext <;> apply e.injective <;> push_map <;> ring

protected theorem add_assoc (a b c : Fp2 F) : a + b + c = a + (b + c) := by
  apply Fp2.ext <;> apply e.injective <;> push_map <;> ring

protected theorem zero_add (a : Fp2 F) : 0 + a = a := by
  apply Fp2.ext <;> apply e.injective <;> push_map <;> ring

protected theorem add_zero (a : Fp2 F) : a + 0 = a := by
  apply Fp2.ext <;> apply e.injective <;> push_map <;> ring

protected theorem neg_add_cancel (a : Fp2 F) : -a + a = 0 := by
  apply Fp2.ext <;> apply e.injective <;> push_map <;> ring

protected theorem sub_eq_add_neg (a b : Fp2 F) : a - b = a + -b := by
  apply Fp2.ext <;> apply e.injective <;> push_map <;> ring

protected theorem mul_comm (a b : Fp2 F) : a * b = b * a := by
  apply Fp2.ext <;> apply e.injective <;> push_map <;> ring

protected theorem mul_assoc (a b c : Fp2 F) : a * b * c = a * (b * c) := by
  apply Fp2.ext <;> apply e.injective <;> push_map <;> ring

protected theorem one_mul (a : Fp2 F) : 1 * a = a := by
  apply Fp2.ext <;> apply e.injective <;> push_map <;> ring

protected theorem mul_one (a : Fp2 F) : a * 1 = a := by
  apply Fp2.ext <;> apply e.injective <;> push_map <;> ring

protected theorem zero_mul (a : Fp2 F) : 0 * a = 0 := by
  apply Fp2.ext <;> apply e.injective <;> push_map <;> ring

protected theorem mul_zero (a : Fp2 F) : a * 0 = 0 := by
  apply Fp2.ext <;> apply e.injective <;> push_map <;> ring

protected theorem left_distrib (a b c : Fp2 F) : a * (b + c) = a * b + a * c := by
  apply Fp2.ext <;> apply e.injective <;> push_map <;> ring

protected theorem right_distrib (a b c : Fp2 F) : (a + b) * c = a * c + b * c := by
  apply Fp2.ext <;> apply e.injective <;> push_map <;> ring

protected theorem zero_ne_one : (0 : Fp2 F) ≠ 1 := fun h => by
  have h0 := congrArg (fun a : Fp2 F => e.toFun a.c0) h
  simp only [zero_c0, one_c0, e.map_zero, e.map_one] at h0
  exact zero_ne_one h0

/-- Every nonzero element times its inverse is one, when `-1` is not a square. -/
theorem mul_inverse_cancel (hsq : ∀ y : K, y * y ≠ -1) {a : Fp2 F} (h : a ≠ 0) :
    a * a.inverse = 1 := by
  have hn : e.toFun (a.c0 * a.c0 + a.c1 * a.c1) ≠ 0 := fun hn => by
    rw [e.map_add, e.map_mul, e.map_mul] at hn
    obtain ⟨h0, h1⟩ := norm_eq_zero hsq hn
    exact h (Fp2.ext (e.injective (h0.trans e.map_zero.symm))
      (e.injective (h1.trans e.map_zero.symm)))
  -- With `w = 1 / N(a)`, the product is `(c0^2 + c1^2) w + (c1 c0 - c0 c1) w i`.
  have hw := mul_inv_cancel₀ hn
  rw [← e.map_inverse, e.map_add, e.map_mul, e.map_mul] at hw
  apply Fp2.ext <;> apply e.injective <;>
    simp only [mul_c0, mul_c1, one_c0, one_c1, inverse_c0, inverse_c1] <;>
    generalize FieldOps.inverse (a.c0 * a.c0 + a.c1 * a.c1) = w at hw ⊢ <;> push_map
  · linear_combination hw
  · ring

/-- The inverse of zero is zero. -/
theorem inverse_zero : (0 : Fp2 F).inverse = 0 := by
  apply Fp2.ext <;> apply e.injective <;> simp only [inverse_c0, inverse_c1] <;> push_map <;>
    ring

end Laws

/-! ## Powers -/

/-- Square and multiply is the power of any monoid on the extension with its one and product. -/
theorem powNat_eq_npow (M : Monoid (Fp2 F)) (hone : M.one = one) (hmul : ∀ a b, M.mul a b = a * b)
    (a : Fp2 F) (n : ℕ) : powNat a n = M.npow n a := by
  let _ := M
  induction n using Nat.strongRecOn generalizing a with
  | _ n ih =>
    rw [powNat]
    split
    · rename_i h
      subst h
      exact hone.symm.trans (M.npow_zero a).symm
    · rename_i h
      rw [ih (n / 2) (by omega)]
      -- `a^n = a^(n mod 2) * (a^2)^(n / 2)`.
      have hsq : M.npow (n / 2) (a * a) = a ^ (2 * (n / 2)) := by
        rw [pow_mul, pow_two, ← hmul]
        rfl
      by_cases h2 : n % 2 = 1
      · rw [ite_eq_left h2, hsq, ← hmul]
        exact (pow_succ' a _).symm.trans (congrArg (a ^ ·) (by omega))
      · rw [ite_eq_right h2, hsq]
        exact congrArg (a ^ ·) (by omega)

end Fp2

end EthLib.Cryptography
