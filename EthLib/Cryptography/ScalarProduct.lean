module

/-!
# The scalar product of a curve point

Every short Weierstrass curve of the library computes `k P` with the one method of this file.

It is the binary NAF method, Algorithm 3.31 of "Guide to Elliptic Curve Cryptography".

That book is by Hankerson, Menezes and Vanstone (Springer, 2004).
-/

@[expose] public section

namespace EthLib.Cryptography.ScalarProduct

variable {α : Type}

/-- Steps `n, n - 1, ..., 1` of the scalar product, from the accumulator `q`.

Step `i` doubles `q`, then adds the digit `h_i - k_i` times `p`, from bit `i` of `h` and of `k`.

`np` is the negation of `p`. -/
@[specialize] def nafSteps (double : α → α) (add : α → α → α) (p np : α) (k h : Nat) :
    Nat → α → α
  | 0, q => q
  | i + 1, q =>
    let q := double q
    -- The digit is `1`, `-1` or `0`.
    let q := match h.testBit (i + 1), k.testBit (i + 1) with
      | true, false => add q p
      | false, true => add q np
      | _, _ => q
    nafSteps double add p np k h i q

/-- `k p`, left to right on the non-adjacent form of `k`, from the doubling and addition of a curve.

`zero` is the point at infinity, and `np` is the negation of `p`.

With `h = 3k`, the digits `h_i - k_i` for `i` from the top bit of `h` down to 1 write `k`.

These digits are `-1`, `0` or `1`, and digit `i` has the weight `2^(i-1)`.

No two adjacent digits are nonzero, so about a third of them are, against half of the bits of `k`.

Each addition adds `p` or `np`, so it takes the shorter mixed formulas when `p` has `z = 1`. -/
@[specialize] def naf (double : α → α) (add : α → α → α) (zero p np : α) (k : Nat) : α :=
  -- Bit `log2 h` of `h` is its top bit, so the steps start from there.
  nafSteps double add p np k (3 * k) (3 * k).log2 zero

end EthLib.Cryptography.ScalarProduct
