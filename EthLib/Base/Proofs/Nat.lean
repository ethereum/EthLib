module

/-!
# `Base.Proofs.Nat`

Facts about natural numbers that Lean core does not prove and that several layers use.

Lean states each case of a hex digit as a lemma, and this module gathers them in one equation.
-/

@[expose] public section

namespace EthLib.Base

/-- Rounding down to a multiple of a step keeps the order. -/
theorem rounded_mono (inc : Nat) {low high : Nat} (le : low ≤ high) :
    low - low % inc ≤ high - high % inc := by
  have one := Nat.mod_add_div low inc
  have two := Nat.mod_add_div high inc
  have three := Nat.div_le_div_right (c := inc) le
  have four := Nat.mul_le_mul_left inc three
  omega

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

/-- The rounded-up quotient is at most its numerator. -/
theorem ceil_div_le (c q : Nat) : (c + q - 1) / q ≤ c := by
  rcases Nat.eq_zero_or_pos q with rfl | pos
  · simp
  · exact (Nat.div_le_iff_le_mul pos).mpr (by
      have := Nat.le_mul_of_pos_right c pos
      omega)

/-- The quotient of a sum is at most the floor of one quotient plus the ceiling of the other. -/
theorem floor_add_ceil_le (a b Q : Nat) (pos : 0 < Q) :
    (a + b) / Q ≤ a / Q + (b + Q - 1) / Q := by
  apply (Nat.div_le_iff_le_mul pos).mpr
  rw [Nat.add_mul, Nat.mul_comm (_ / Q) Q, Nat.mul_comm ((b + Q - 1) / Q) Q]
  have ha := Nat.div_add_mod a Q
  have hr := Nat.mod_lt a pos
  have hb := Nat.div_add_mod (b + Q - 1) Q
  have hs := Nat.mod_lt (b + Q - 1) pos
  omega

/-- Round down a sum using an upper bound that rounds the added amount up instead. -/
theorem rounded_add_ceil_le (I x C : Nat) (hI : 0 < I) :
    (x + C) - (x + C) % I ≤ (x - x % I) + I * ((C + I - 1) / I) := by
  rw [← Nat.mul_div_self_eq_mod_sub_self, ← Nat.mul_div_self_eq_mod_sub_self, ← Nat.mul_add]
  exact Nat.mul_le_mul_left _ (floor_add_ceil_le x C I hI)

/-- Round down a sum by allowing for the added remainder before rounding the base down. -/
theorem rounded_add_floor_le (I x y : Nat) (hI : 0 < I) :
    (x + y) - (x + y) % I ≤ (x + I - 1) - (x + I - 1) % I + I * (y / I) := by
  have h := rounded_add_ceil_le I y x hI
  rw [Nat.add_comm y x, ← Nat.mul_div_self_eq_mod_sub_self (x := y),
    Nat.mul_div_self_eq_mod_sub_self (x := x + I - 1),
    Nat.add_comm (I * (y / I))] at h
  exact h

/-- Rounding down a number less than one increment above an aligned bound stays below it. -/
theorem floor_le_of_lt {B E I : Nat} (hI : 0 < I) (aligned : E % I = 0)
    (lt : B < E + I) : B - B % I ≤ E := by
  obtain ⟨u, rfl⟩ := Nat.dvd_of_mod_eq_zero aligned
  rw [← Nat.mul_div_self_eq_mod_sub_self]
  apply Nat.mul_le_mul_left
  exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hI).mpr (by
    simpa [Nat.succ_mul, Nat.mul_comm u I] using lt))

end EthLib.Base
