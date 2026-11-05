module

public import Mathlib.Data.ZMod.Basic

/-!
# Proofs: a sum of products in `ZMod n`

The pairing law of a check compares a power of a generator of order `n` with 1.

The exponent is a sum of products of natural numbers, the values of scalars in `ZMod n`.

The power is 1 exactly when `n` divides that sum, so when the sum of the scalar products is zero.
-/

@[expose] public section

namespace EthLib.Cryptography

/-- A sum of products of values is zero in `ZMod n` exactly when `n` divides it. -/
theorem dvd_sum_zipWith_val_iff {n : ℕ} [NeZero n] (a b : List (ZMod n)) :
    n ∣ (List.zipWith (fun x y => x.val * y.val) a b).sum ↔
      (List.zipWith (· * ·) a b).sum = 0 := by
  have hcast : ∀ a b : List (ZMod n),
      (((List.zipWith (fun x y => x.val * y.val) a b).sum : ℕ) : ZMod n) =
        (List.zipWith (· * ·) a b).sum := by
    intro a b
    induction a generalizing b with
    | nil => simp
    | cons x xs ih =>
      cases b with
      | nil => simp
      | cons y ys =>
        rw [List.zipWith_cons_cons, List.zipWith_cons_cons, List.sum_cons, List.sum_cons,
          Nat.cast_add, Nat.cast_mul, ih, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [← hcast]
  exact (ZMod.natCast_eq_zero_iff _ _).symm

end EthLib.Cryptography
