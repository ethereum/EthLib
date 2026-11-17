module

/-!
# `Base.Proofs.Nat`

Facts about natural numbers that Lean core does not prove and that several layers use.

A number below `p` equals its remainder `r` mod `n` when `p <= r + n`.

Applying a step once more before its repetitions is one more repetition.

Lean writes a digit `0` to `9` or `a` to `f` for a number below sixteen, and `*` from sixteen on.

Lean states each case as a public lemma, and this module gathers them into one equation.

Whole increments of a total, each paid a share of a factor, get at most the total's share.
-/

@[expose] public section

namespace EthLib.Base

/-- A number `x` below `p` with `x mod n = r` is `r`, when `p <= r + n`.

The quotient is then 0, since a quotient of 1 or more would put `x` at `r + n` or above. -/
theorem eq_of_mod_eq_of_lt {x n r p : Nat} (hx : x % n = r) (hlt : x < p) (hp : p ≤ r + n) :
    x = r := by
  have hdiv := Nat.mod_add_div x n
  by_cases h0 : x / n = 0
  · rw [h0, Nat.mul_zero, Nat.add_zero] at hdiv
    omega
  · have := Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero h0)
    omega

/-- Iterating `k` times from `f a` is iterating `k + 1` times from `a`. -/
theorem repeat_apply_eq_repeat_succ {α : Type} (f : α → α) (k : Nat) (a : α) :
    Nat.repeat f k (f a) = Nat.repeat f (k + 1) a := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg f ih

/-- The digit of a number below sixteen is `0` to `9` or `a` to `f`, and `*` for any other number.

`decide` can evaluate the right side, which the hidden body of `Nat.digitChar` does not allow. -/
theorem digitChar_eq (n : Nat) :
    n.digitChar =
      if n = 0 then '0' else if n = 1 then '1' else if n = 2 then '2' else
      if n = 3 then '3' else if n = 4 then '4' else if n = 5 then '5' else
      if n = 6 then '6' else if n = 7 then '7' else if n = 8 then '8' else
      if n = 9 then '9' else if n = 0xa then 'a' else if n = 0xb then 'b' else
      if n = 0xc then 'c' else if n = 0xd then 'd' else if n = 0xe then 'e' else
      if n = 0xf then 'f' else '*' := by
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => simp
  | n + 16 => simp

/-- Whole increments of a total, times one increment's share of a factor, are at most the total's.

The share of an increment is the increment times the factor over the root.

The share of the total is the total times the factor over the root. -/
theorem div_mul_div_le_mul_div (total increment factor root : Nat) :
    total / increment * (increment * factor / root) ≤ total * factor / root :=
  calc total / increment * (increment * factor / root)
      ≤ total / increment * (increment * factor) / root := Nat.mul_div_le_mul_div_assoc _ _ _
    _ ≤ total * factor / root := by
        refine Nat.div_le_div_right ?_
        rw [← Nat.mul_assoc]
        exact Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)

end EthLib.Base
