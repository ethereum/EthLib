module

public import EthLib.Cryptography.Inverse
public import EthLib.Cryptography.Word64

/-!
# Inverses by the divsteps of Bernstein and Yang

A candidate for `x^(-1) mod p`, for an odd modulus `p`, by jumps of 60 divsteps on words.

A check keeps a candidate only when it is the inverse, else the Euclidean inverse is used.

Source: [Bernstein and Yang][safegcd], §8.1 for the divstep, §12.1 for the jumps of divsteps.

[safegcd]: <https://gcd.cr.yp.to/safegcd-20190413.pdf>
-/

@[expose] public section

namespace EthLib.Cryptography.SafeGcd

open Word64

/-! ## Divsteps on the low words -/

/-- The state after `k` divsteps: `delta` and the transition matrix, scaled by `2^k`. -/
structure Transition where
  /-- The value of `delta` after the steps, as a signed word. -/
  delta : UInt64
  /-- The entry `u` of the matrix `[[u, v], [q, r]]` of Theorem 11.2, times `2^k`. -/
  aa : UInt64
  /-- The entry `v`, times `2^k`. -/
  ab : UInt64
  /-- The entry `q`, times `2^k`. -/
  ba : UInt64
  /-- The entry `r`, times `2^k`. -/
  bb : UInt64

/-- The `delta` and the scaled transition matrix of the next divsteps, from low words of `f, g`.

By Theorem 9.4, the low `t` bits of `f` and `g` fix the next `t` divsteps. -/
@[noinline] def jump : Nat → UInt64 → UInt64 → UInt64 →
    UInt64 → UInt64 → UInt64 → UInt64 → Transition
  -- No step left: return `delta` and the matrix.
  | 0, delta, _, _, aa, ab, ba, bb => ⟨delta, aa, ab, ba, bb⟩
  | fuel + 1, delta, f, g, aa, ab, ba, bb =>
    -- §8: the second case of `divstep` is split by parity.
    --
    -- An even `g` gives `(1 + delta, f, g / 2)`.
    --
    -- The matrix rows follow `f` and `g`, scaled by 2 as in §8.1, so that no step divides.
    --
    -- Here `2 T = [[2, 0], [0, 1]]`, so the first row doubles and the second stays.
    if g &&& 1 == 0 then
      jump fuel (delta + 1) f (g >>> 1) (aa + aa) (ab + ab) ba bb
    -- `(1 - delta, g, (g - f) / 2)` if `delta > 0` and `g` is odd.
    --
    -- The high bit of `delta - 1` tests `delta > 0`.
    --
    -- Here `2 T = [[0, 2], [-1, 1]]`.
    --
    -- The new first row is twice the old second, and the new second is the second minus the first.
    else if (delta - 1) >>> 63 == 0 then
      jump fuel (1 - delta) g ((g - f) >>> 1) (ba + ba) (bb + bb) (ba - aa) (bb - ab)
    -- Otherwise `(1 + delta, f, (g + f) / 2)`, for an odd `g`.
    --
    -- Here `2 T = [[2, 0], [1, 1]]`: the first row doubles, the second gains the first.
    else
      jump fuel (delta + 1) f ((g + f) >>> 1) (aa + aa) (ab + ab) (ba + aa) (bb + ab)

/-- The table of 6 divsteps, indexed by `delta + 6` in `[0, 12]` and by `g / f mod 64`.

Each entry packs the final `delta` in bits 32 to 37 and the four matrix entries in bytes 3 to 0. -/
def jumpTable : Vector Nat 1024 := Vector.ofFn fun i =>
  -- The row gives `delta = row - 6`.
  --
  -- Rows 13 to 15 are filled but never read.
  let d := (i.val >>> 6).toUInt64 - 6
  -- The column gives the low 6 bits of `g`, which fix 6 divsteps by Theorem 9.4.
  let g := i.val.toUInt64 &&& 63
  -- Divsteps commute with scaling `f` and `g` by an odd 2-adic unit, so `f = 1` stands for any `f`.
  let t := jump 6 d 1 g 1 0 0 1
  -- Each entry of `2^6 T` has absolute value at most `2^6`, so it fits a signed byte.
  let pack (a : UInt64) : UInt64 := a &&& 255
  -- The final `delta` lies in `[-12, 12]`, so it fits 6 signed bits.
  (((t.delta &&& 63) <<< 32) |||
    (pack t.aa <<< 24) ||| (pack t.ab <<< 16) |||
    (pack t.ba <<< 8) ||| pack t.bb).toNat

/-- The signed byte in the low 8 bits of `w`, as a signed word. -/
@[inline] def unpackCoefficient (w : UInt64) : UInt64 :=
  -- Flipping bit 7 and subtracting `2^7` maps `[0, 255]` onto `[-128, 127]`.
  ((w &&& 255) ^^^ 128) - 128

/-- The `delta` and the scaled transition matrix of `6 k` divsteps, by `k` table lookups. -/
@[noinline] def jumpBlocks : Nat → UInt64 → UInt64 → UInt64 →
    UInt64 → UInt64 → UInt64 → UInt64 → Transition
  -- No block left: return `delta` and the matrix.
  | 0, delta, _, _, aa, ab, ba, bb => ⟨delta, aa, ab, ba, bb⟩
  | fuel + 1, delta, f, g, aa, ab, ba, bb =>
    -- Since f is odd, its square is one modulo eight.
    --
    -- One Newton step gives its inverse modulo 64 for the table index.
    let inv := f * (2 - f * f)
    -- The column of the table: `g / f mod 64`.
    let ratio := (g * inv) &&& 63
    -- The table covers `delta` in `[-6, 6]`, and a larger `|delta|` uses the nearest row.
    let positive := delta.toInt64 > 6
    let negative := delta.toInt64 < -6
    -- Any `delta > 6` makes the same 6 decisions as `delta = 6`, and any `delta < -6` as `-6`.
    let row : UInt64 := if positive then 12 else if negative then 0 else delta + 6
    -- The masked index is below 1024, which is the bound the table lookup needs.
    let index := ((row <<< 6) ||| ratio) &&& 1023
    let entry := (jumpTable.get ⟨index.toNat, by
      rw [UInt64.toNat_and]
      change _ &&& ((2 : Nat) ^ 10 - 1) < _
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by decide)⟩).toUInt64
    -- Sign-extend the 6-bit `delta` of the entry.
    let nextDelta := (((entry >>> 32) ^^^ 32) - 32)
    -- A large positive delta is negated at most once, at the first odd step.
    --
    -- With no odd step, when `g / f = 0 mod 64`, the offset `delta - 6` is kept.
    --
    -- After an odd step, the offset is negated.
    --
    -- A large negative delta cannot change sign within this block, so its offset is kept.
    let adjustment := if positive then
        if ratio == 0 then delta - 6 else 6 - delta
      else if negative then delta + 6 else 0
    -- The block matrix `[[a, b], [c, d]]`, as signed words.
    let a := unpackCoefficient (entry >>> 24)
    let b := unpackCoefficient (entry >>> 16)
    let c := unpackCoefficient (entry >>> 8)
    let d := unpackCoefficient entry
    -- `(f, g) <- [[a, b], [c, d]] (f, g) / 2^6`, exact in the low bits that later blocks read.
    --
    -- The matrix so far is multiplied on the left by the block matrix.
    jumpBlocks fuel (nextDelta + adjustment) ((a*f + b*g) >>> 6) ((c*f + d*g) >>> 6)
      (a*aa + b*ba) (a*ab + b*bb) (c*aa + d*ba) (c*ab + d*bb)

/-! ## Signed integers in words -/

/-- `x a + y b + carry` as a low word and a high word. -/
@[inline] def linWord (a b x y carry : UInt64) : Pair :=
  -- `x a + carry` fits two words.
  let t := mac x a 0 carry
  -- Add `y b` to the low word.
  let u := mac y b t.lo 0
  -- With `|a|, |b| <= 2^60`, the sum is below `2^126`, so the high word does not overflow.
  ⟨u.lo, t.hi + u.hi⟩

/-- Signed integers of a fixed number of words in two's complement, with the operations of a jump.

The operations are exact while the results fit the words. -/
class Signed (W : Type) where
  /-- The integer of a word. -/
  ofWord : UInt64 → W
  /-- The lowest word. -/
  low : W → UInt64
  /-- Whether the integer is `0`. -/
  isZero : W → Bool
  /-- Whether the integer is negative. -/
  isNeg : W → Bool
  /-- `a + b`. -/
  add : W → W → W
  /-- `a - b`. -/
  sub : W → W → W
  /-- `floor(a / 2^60)`. -/
  shr60 : W → W
  /-- `a x + b y` for signed words `a, b` with `|a|, |b| <= 2^60`. -/
  lin : UInt64 → UInt64 → W → W → W
  /-- `x + q p` for a word `q` below `2^60` and a nonnegative `p`. -/
  addMul : W → W → UInt64 → W

namespace Signed

variable {W : Type} [Signed W]

/-- The magnitudes and masks of two signed words, for a linear combination.

The masks are all ones for a negative word, and the carry is the sum of the negative magnitudes. -/
@[inline] def split (a b : UInt64) : UInt64 × UInt64 × UInt64 × UInt64 × UInt64 :=
  -- The sign bits of `a` and `b`.
  let negA := a >>> 63
  let negB := b >>> 63
  -- All ones for a negative coefficient, else zero.
  let maskA := 0 - negA
  let maskB := 0 - negB
  -- The magnitudes `|a|` and `|b|`.
  let aa := (a ^^^ maskA) + negA
  let bb := (b ^^^ maskB) + negB
  -- For `a < 0`, `a x = |a| (-x) = |a| (not x) + |a|`.
  --
  -- So each word with a negative coefficient is complemented, and `|a|` joins the carry.
  (aa, bb, maskA, maskB, (aa &&& maskA) + (bb &&& maskB))

/-- A number congruent to `x / 2^60 mod p`: `x + q p` for the `q` that makes it divisible by `2^60`.

The word `pinv` is `-p^(-1) mod 2^64`. -/
@[inline] def adjust (x p : W) (pinv : UInt64) : W :=
  -- `q = -x p^(-1) mod 2^60`, so `x + q p = 0 mod 2^60`, and the shift divides exactly.
  shr60 (addMul x p ((low x * pinv) &&& 0xfffffffffffffff))

/-- `sgn(f) d`, reduced into `[0, p)` by adding or subtracting `p`, then converted.

A `d` out of the range that these steps reduce gives a wrong candidate, which a check rejects. -/
@[noinline, specialize] def normalize {A : Type} (finish : W → A) (d p : W) (neg : Bool) : A :=
  -- Step 7: the factor `sgn(f)`.
  let d := if neg then sub (ofWord 0) d else d
  -- Add `p` while `d` is negative, at most twice.
  let d := if isNeg d then add d p else d
  let d := if isNeg d then add d p else d
  -- Subtract `p` once if `d - p` is not negative.
  let e := sub d p
  if isNeg e then finish d else finish e

/-- The jumps of §12.1 on `(delta, f, g)` and on the coefficients `(d, e)`, up to a bound.

It returns `sgn(f) d mod p` once `g = 0`, or `none` when the jumps run out first. -/
@[noinline, specialize] def run {A : Type} (finish : W → A) (p : W) (pinv : UInt64) :
    Nat → UInt64 → W → W → W → W → Option A
  -- A loop that has not finished after its jumps gives no candidate.
  | 0, _, f, g, d, _ =>
    if isZero g then some (normalize finish d p (isNeg f)) else none
  | fuel + 1, δ, f, g, d, e =>
    -- Step 7: once `g = 0`, `f = +-1` and `d x = f mod p`, so `x^-1 = sgn(f) d mod p`.
    --
    -- Each jump already divided `d` by `2^60` mod `p`, so no factor `2^-k` is left.
    --
    -- The paper always runs its full count of divsteps.
    --
    -- This loop stops early instead, since a divstep with `g = 0` keeps `f`.
    --
    -- So its time depends on the input.
    --
    -- EthLib makes no constant-time claim (SOUNDNESS.md A3).
    if isZero g then some (normalize finish d p (isNeg f))
    else
      -- §12.1, steps 2 and 3: the transition matrix of the next 60 divsteps, from the low words.
      --
      -- The paper takes 62 divsteps per jump.
      --
      -- Here a jump takes 60, ten blocks of the 6-step table.
      let t := jumpBlocks 10 δ (low f) (low g) 1 0 0 1
      -- Step 4: `(f, g) <- T_i (f, g) / 2^60`.
      let nf := shr60 (lin t.aa t.ab f g)
      let ng := shr60 (lin t.ba t.bb f g)
      -- In place of step 6, the matrix also updates the coefficients `(d, e)` of `x` mod `p`.
      --
      -- Each gains a multiple of `p` that makes it divisible by `2^60`, keeping `d x = f mod p`.
      let nd := adjust (lin t.aa t.ab d e) p pinv
      let ne := adjust (lin t.ba t.bb d e) p pinv
      -- Step 5: `delta <- delta'`, then back to the low words for the next jump.
      run finish p pinv fuel t.delta nf ng nd ne

/-- A candidate for `x^(-1) mod p`, converted by `finish`, or `none` when the jumps run out.

The modulus `p` is odd and positive, `pinv` is `-p^(-1) mod 2^64`, and `jumps` bounds the loop. -/
@[inline] def inverse {A : Type} (finish : W → A) (p : W) (pinv : UInt64) (jumps : Nat)
    (x : W) : Option A :=
  -- §12.1, step 1: `f = p`, `g = x`, `delta = 1`, with the coefficients `d = 0` and `e = 1`.
  run finish p pinv jumps 1 p x (ofWord 0) (ofWord 1)

end Signed

/-! ## Five words

Four words and a signed top word hold the jumps for a modulus below `2^256`.
-/

/-- The signed integers of `Words64`, with the top word as the sign-carrying word. -/
instance : Signed Words64 where
  ofWord w := ⟨w, 0, 0, 0, 0⟩
  low a := a.w0
  isZero a := a.w0 ||| a.w1 ||| a.w2 ||| a.w3 ||| a.top == 0
  isNeg a := a.top >>> 63 != 0
  add a b :=
    -- Add word by word, from the least significant, with the carry.
    let x0 := plus a.w0 b.w0 0
    let x1 := plus a.w1 b.w1 x0.hi
    let x2 := plus a.w2 b.w2 x1.hi
    let x3 := plus a.w3 b.w3 x2.hi
    -- The carry out of the top word is dropped.
    ⟨x0.lo, x1.lo, x2.lo, x3.lo, a.top + b.top + x3.hi⟩
  sub a b :=
    -- Subtract word by word, from the least significant, with the borrow.
    let x0 := minus a.w0 b.w0 0
    let x1 := minus a.w1 b.w1 x0.hi
    let x2 := minus a.w2 b.w2 x1.hi
    let x3 := minus a.w3 b.w3 x2.hi
    -- The borrow out of the top word is dropped.
    ⟨x0.lo, x1.lo, x2.lo, x3.lo, a.top - b.top - x3.hi⟩
  shr60 a :=
    -- Each word takes its high 4 bits and the low 60 bits of the next word up.
    ⟨(a.w0 >>> 60) ||| (a.w1 <<< 4), (a.w1 >>> 60) ||| (a.w2 <<< 4),
      (a.w2 >>> 60) ||| (a.w3 <<< 4), (a.w3 >>> 60) ||| (a.top <<< 4),
      -- The top word shifts arithmetically, which keeps the sign.
      ((a.top.toInt64) >>> (60 : UInt64).toInt64).toUInt64⟩
  lin a b x y :=
    let (aa, bb, maskA, maskB, carry) := Signed.split a b
    -- Multiply and add word by word, from the least significant, with the carry.
    let r0 := linWord aa bb (x.w0 ^^^ maskA) (y.w0 ^^^ maskB) carry
    let r1 := linWord aa bb (x.w1 ^^^ maskA) (y.w1 ^^^ maskB) r0.hi
    let r2 := linWord aa bb (x.w2 ^^^ maskA) (y.w2 ^^^ maskB) r1.hi
    let r3 := linWord aa bb (x.w3 ^^^ maskA) (y.w3 ^^^ maskB) r2.hi
    -- The top word is computed mod `2^64`, which is exact when the result fits five words.
    ⟨r0.lo, r1.lo, r2.lo, r3.lo, (x.top ^^^ maskA) * aa + (y.top ^^^ maskB) * bb + r3.hi⟩
  addMul x p q :=
    -- `x + q p`, word by word, from the least significant, with the carry.
    let r0 := mac p.w0 q x.w0 0
    let r1 := mac p.w1 q x.w1 r0.hi
    let r2 := mac p.w2 q x.w2 r1.hi
    let r3 := mac p.w3 q x.w3 r2.hi
    ⟨r0.lo, r1.lo, r2.lo, r3.lo, p.top * q + x.top + r3.hi⟩

/-! ## Seven words

Six words and a signed top word hold the jumps for a modulus below `2^384`.
-/

/-- Six words and a signed word above them, least significant first. -/
structure Words7 where
  /-- Bits 0 through 63. -/
  w0 : UInt64
  /-- Bits 64 through 127. -/
  w1 : UInt64
  /-- Bits 128 through 191. -/
  w2 : UInt64
  /-- Bits 192 through 255. -/
  w3 : UInt64
  /-- Bits 256 through 319. -/
  w4 : UInt64
  /-- Bits 320 through 383. -/
  w5 : UInt64
  /-- The signed word above bit 383. -/
  top : UInt64

/-- The signed integers of `Words7`, with the top word as the sign-carrying word. -/
instance : Signed Words7 where
  ofWord w := ⟨w, 0, 0, 0, 0, 0, 0⟩
  low a := a.w0
  isZero a := a.w0 ||| a.w1 ||| a.w2 ||| a.w3 ||| a.w4 ||| a.w5 ||| a.top == 0
  isNeg a := a.top >>> 63 != 0
  add a b :=
    -- Add word by word, from the least significant, with the carry.
    let x0 := plus a.w0 b.w0 0
    let x1 := plus a.w1 b.w1 x0.hi
    let x2 := plus a.w2 b.w2 x1.hi
    let x3 := plus a.w3 b.w3 x2.hi
    let x4 := plus a.w4 b.w4 x3.hi
    let x5 := plus a.w5 b.w5 x4.hi
    -- The carry out of the top word is dropped.
    ⟨x0.lo, x1.lo, x2.lo, x3.lo, x4.lo, x5.lo, a.top + b.top + x5.hi⟩
  sub a b :=
    -- Subtract word by word, from the least significant, with the borrow.
    let x0 := minus a.w0 b.w0 0
    let x1 := minus a.w1 b.w1 x0.hi
    let x2 := minus a.w2 b.w2 x1.hi
    let x3 := minus a.w3 b.w3 x2.hi
    let x4 := minus a.w4 b.w4 x3.hi
    let x5 := minus a.w5 b.w5 x4.hi
    -- The borrow out of the top word is dropped.
    ⟨x0.lo, x1.lo, x2.lo, x3.lo, x4.lo, x5.lo, a.top - b.top - x5.hi⟩
  shr60 a :=
    -- Each word takes its high 4 bits and the low 60 bits of the next word up.
    ⟨(a.w0 >>> 60) ||| (a.w1 <<< 4), (a.w1 >>> 60) ||| (a.w2 <<< 4),
      (a.w2 >>> 60) ||| (a.w3 <<< 4), (a.w3 >>> 60) ||| (a.w4 <<< 4),
      (a.w4 >>> 60) ||| (a.w5 <<< 4), (a.w5 >>> 60) ||| (a.top <<< 4),
      -- The top word shifts arithmetically, which keeps the sign.
      ((a.top.toInt64) >>> (60 : UInt64).toInt64).toUInt64⟩
  lin a b x y :=
    let (aa, bb, maskA, maskB, carry) := Signed.split a b
    -- Multiply and add word by word, from the least significant, with the carry.
    let r0 := linWord aa bb (x.w0 ^^^ maskA) (y.w0 ^^^ maskB) carry
    let r1 := linWord aa bb (x.w1 ^^^ maskA) (y.w1 ^^^ maskB) r0.hi
    let r2 := linWord aa bb (x.w2 ^^^ maskA) (y.w2 ^^^ maskB) r1.hi
    let r3 := linWord aa bb (x.w3 ^^^ maskA) (y.w3 ^^^ maskB) r2.hi
    let r4 := linWord aa bb (x.w4 ^^^ maskA) (y.w4 ^^^ maskB) r3.hi
    let r5 := linWord aa bb (x.w5 ^^^ maskA) (y.w5 ^^^ maskB) r4.hi
    -- The top word is computed mod `2^64`, which is exact when the result fits seven words.
    ⟨r0.lo, r1.lo, r2.lo, r3.lo, r4.lo, r5.lo,
      (x.top ^^^ maskA) * aa + (y.top ^^^ maskB) * bb + r5.hi⟩
  addMul x p q :=
    -- `x + q p`, word by word, from the least significant, with the carry.
    let r0 := mac p.w0 q x.w0 0
    let r1 := mac p.w1 q x.w1 r0.hi
    let r2 := mac p.w2 q x.w2 r1.hi
    let r3 := mac p.w3 q x.w3 r2.hi
    let r4 := mac p.w4 q x.w4 r3.hi
    let r5 := mac p.w5 q x.w5 r4.hi
    ⟨r0.lo, r1.lo, r2.lo, r3.lo, r4.lo, r5.lo, p.top * q + x.top + r5.hi⟩

/-! ## Inverses mod an integer below `2^256`

The five-word jumps give a candidate, which a check keeps only when it is the inverse.
-/

/-- `-m^(-1) mod 2^64` for an odd word `m`, by Newton's iteration. -/
@[inline] def negInverseWord (m : UInt64) : UInt64 :=
  -- An odd `m` has `m m = 1 mod 8`, so `x = m` is the inverse in the low 3 bits.
  --
  -- Each step `x <- x (2 - m x)` doubles the correct low bits: 6, 12, 24, 48, then 96.
  let x := m * (2 - m * m)
  let x := x * (2 - m * x)
  let x := x * (2 - m * x)
  let x := x * (2 - m * x)
  0 - x * (2 - m * x)

/-- A candidate for `a^(-1) mod m`, or `none` for `a = 0` or when the jumps run out.

A modulus that is even or not below `2^256`, or an input not below it, may give a wrong one. -/
@[inline] def candidate (m a : Nat) : Option Nat :=
  -- `0` has no inverse.
  if a = 0 then none
  else
    -- Theorem 11.2 needs `floor((49 * 256 + 57) / 17) = 741` divsteps for 256-bit inputs.
    --
    -- So thirteen jumps, 780 divsteps, always suffice.
    Signed.inverse (fun w => rawToNat (Raw.fromWords w)) (rawOfNat m).words
      (negInverseWord m.toUInt64) 13 (rawOfNat a).words

/-- The candidate when it is the inverse of `a` mod `m`, or else the Euclidean inverse.

A candidate below `m` whose product with `a` is `1` mod `m` is accepted. -/
@[inline] def check {m : Nat} [NeZero m] (c : Option Nat) (a : Fin m) : Fin m :=
  match c with
  -- No candidate: the extended Euclidean algorithm gives the inverse.
  | none => Fin.inverse a
  | some v =>
    -- Any other candidate, like no candidate, gives way to the extended Euclidean algorithm.
    --
    -- So the result never depends on the loop being right.
    if h : v < m ∧ v * a.val % m = 1 then ⟨v, h.1⟩ else Fin.inverse a

/-- The inverse of a nonzero `a` mod a prime `m`, and `0` for `0`.

The divsteps give a candidate, and the Euclidean inverse replaces one that fails the check. -/
@[inline] def inverseFin {m : Nat} [NeZero m] (a : Fin m) : Fin m :=
  check (candidate m a.val) a

end EthLib.Cryptography.SafeGcd
