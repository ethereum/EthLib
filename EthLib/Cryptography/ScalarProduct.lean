module

/-!
# The scalar product of a curve point

The short Weierstrass curves of the library compute `k P`, and `k P + l Q` in general, here.

The method interleaves non-adjacent forms of width 2, Algorithm 3.51 of the book below.

The book is "Guide to Elliptic Curve Cryptography", by Hankerson, Menezes and Vanstone (2004).
-/

@[expose] public section

namespace EthLib.Cryptography.ScalarProduct

variable {α : Type}

/-- The limbs of `n` in base `2^62`, low limb first, up to its top bit.

On a 64-bit platform, a limb below `2^62` is a small number in compiled code.

So reading its bits allocates nothing, where reading a bit of `n` itself shifts a big number. -/
def limbs (n : Nat) : List Nat :=
  (List.range (n.log2 / 62 + 1)).map fun j => (n >>> (62 * j)) % 2 ^ 62

/-- Bit `i` of the number whose limbs are `c`. -/
@[inline] def bit (c : List Nat) (i : Nat) : Bool :=
  (c.getD (i / 62) 0).testBit (i % 62)

/-- Add digit `i` of a non-adjacent form, times `p`, to `q`.

The digit is bit `i` of `h` minus bit `i` of `k`, read from their limbs `hc` and `kc`.

It is `1`, `-1` or `0`, and `np` is the negation of `p`. -/
@[inline] def addDigit (add : α → α → α) (p np : α) (kc hc : List Nat) (i : Nat) (q : α) : α :=
  match bit hc i, bit kc i with
  | true, false => add q p
  | false, true => add q np
  | _, _ => q

/-- Steps `n, n - 1, ..., 1` of the joint product, from the accumulator `acc`.

Step `i` doubles `acc`, then adds digit `i` of each scalar times its point.

The digits of `k` come from the limbs `kc` of `k` and `hc` of `3k`.

Those of `l` come from the limbs `lc` of `l` and `hc'` of `3l`. -/
@[specialize] def jointSteps (double : α → α) (add : α → α → α) (p np q nq : α)
    (kc hc lc hc' : List Nat) : Nat → α → α
  | 0, acc => acc
  | i + 1, acc =>
    let acc := addDigit add p np kc hc (i + 1) (double acc)
    let acc := addDigit add q nq lc hc' (i + 1) acc
    jointSteps double add p np q nq kc hc lc hc' i acc

/-- `k p + l q`, left to right on the non-adjacent forms of `k` and `l`, with shared doublings.

`zero` is the point at infinity, and `np` and `nq` are the negations of `p` and `q`. -/
@[specialize] def joint (double : α → α) (add : α → α → α) (zero p np q nq : α) (k l : Nat) :
    α :=
  -- With `h = 3k`, the digits `h_i - k_i` for `i` from the top bit of `h` down to 1 write `k`.
  --
  -- These digits are `-1`, `0` or `1`, and digit `i` has the weight `2^(i-1)`.
  --
  -- No two adjacent digits are nonzero, so about a third of them are, against half of the bits.
  --
  -- Each addition adds a point or its negation, so a point with `z = 1` takes the mixed formulas.
  --
  -- Bit `log2 h` of `h` is its top bit, so the steps start from the higher top bit.
  jointSteps double add p np q nq (limbs k) (limbs (3 * k)) (limbs l) (limbs (3 * l))
    (max (3 * k).log2 (3 * l).log2) zero

/-- `k p`: the joint product with `l = 0`, which adds no multiple of the second point. -/
@[specialize] def naf (double : α → α) (add : α → α → α) (zero p np : α) (k : Nat) : α :=
  joint double add zero p np zero zero k 0

end EthLib.Cryptography.ScalarProduct
