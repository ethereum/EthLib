module

/-!
# `Base.Proofs.Nat`

Facts about natural numbers that Lean core does not prove and that several layers use.

A number below `p` equals its remainder `r` mod `n` when `p <= r + n`.
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

end EthLib.Base
