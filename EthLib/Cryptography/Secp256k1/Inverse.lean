module

public import EthLib.Cryptography.Inverse
public import EthLib.Cryptography.Secp256k1.Montgomery

/-!
# `Secp256k1.Inverse`

The inverses mod `n` and mod `p`, by the divsteps of Bernstein and Yang, checked.

Source: [Bernstein and Yang][safegcd], §8.1 for the divstep, §12.1 for the jumps of 60 divsteps.

[safegcd]: <https://gcd.cr.yp.to/safegcd-20190413.pdf>
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

open Word64

namespace Inverse

open Montgomery (plus minus mac)

/-- The state after `k` divsteps: `delta` and the transition matrix, scaled by `2^k`. -/
private structure Transition where
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
@[noinline] private def jump : Nat → UInt64 → UInt64 → UInt64 →
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
private def jumpTable : Vector Nat 1024 := Vector.ofFn fun i =>
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
@[inline] private def unpackCoefficient (w : UInt64) : UInt64 :=
  -- Flipping bit 7 and subtracting `2^7` maps `[0, 255]` onto `[-128, 127]`.
  ((w &&& 255) ^^^ 128) - 128

/-- The `delta` and the scaled transition matrix of `6 k` divsteps, by `k` table lookups. -/
@[noinline] private def jumpBlocks : Nat → UInt64 → UInt64 → UInt64 →
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

/-- A signed integer in five words of two's complement, least significant first. -/
private abbrev Wide := Montgomery.Words64

/-- `a mod 2^320` in five words. -/
@[inline] private def Wide.ofNat (a : Nat) : Wide :=
  ⟨a.toUInt64, (a >>> 64).toUInt64, (a >>> 128).toUInt64, (a >>> 192).toUInt64,
    (a >>> 256).toUInt64⟩

/-- The integer of the low four words, which is the value of a number in `[0, 2^256)`. -/
@[inline] private def Wide.lowNat (a : Wide) : Nat :=
  a.w0.toNat + ((a.w1.toNat + ((a.w2.toNat + (a.w3.toNat <<< 64)) <<< 64)) <<< 64)

/-- Whether the number is `0`. -/
@[inline] private def Wide.isZero (a : Wide) : Bool :=
  a.w0 ||| a.w1 ||| a.w2 ||| a.w3 ||| a.top == 0

/-- `a + b mod 2^320`. -/
@[inline] private def Wide.add (a b : Wide) : Wide :=
  -- Add word by word, from the least significant, with the carry.
  let x0 := plus a.w0 b.w0 0
  let x1 := plus a.w1 b.w1 x0.hi
  let x2 := plus a.w2 b.w2 x1.hi
  let x3 := plus a.w3 b.w3 x2.hi
  -- The carry out of the top word is dropped.
  ⟨x0.lo, x1.lo, x2.lo, x3.lo, a.top + b.top + x3.hi⟩

/-- `a - b mod 2^320`. -/
@[inline] private def Wide.sub (a b : Wide) : Wide :=
  -- Subtract word by word, from the least significant, with the borrow.
  let x0 := minus a.w0 b.w0 0
  let x1 := minus a.w1 b.w1 x0.hi
  let x2 := minus a.w2 b.w2 x1.hi
  let x3 := minus a.w3 b.w3 x2.hi
  -- The borrow out of the top word is dropped.
  ⟨x0.lo, x1.lo, x2.lo, x3.lo, a.top - b.top - x3.hi⟩

/-- `-a mod 2^320`. -/
@[inline] private def Wide.neg (a : Wide) : Wide := Wide.sub ⟨0, 0, 0, 0, 0⟩ a

/-- `floor(a / 2^60)` for a signed `a`. -/
@[inline] private def Wide.shr60 (a : Wide) : Wide :=
  -- Each word takes its high 4 bits and the low 60 bits of the next word up.
  ⟨(a.w0 >>> 60) ||| (a.w1 <<< 4), (a.w1 >>> 60) ||| (a.w2 <<< 4),
    (a.w2 >>> 60) ||| (a.w3 <<< 4), (a.w3 >>> 60) ||| (a.top <<< 4),
    -- The top word shifts arithmetically, which keeps the sign.
    ((a.top.toInt64) >>> (60 : UInt64).toInt64).toUInt64⟩

/-- `x a + y b + carry` as a low word and a high word. -/
@[inline] private def linWord (a b x y carry : UInt64) : Montgomery.Pair :=
  -- `x a + carry` fits two words.
  let t := mac x a 0 carry
  -- Add `y b` to the low word.
  let u := mac y b t.lo 0
  -- With `|a|, |b| <= 2^60`, the sum is below `2^126`, so the high word does not overflow.
  ⟨u.lo, t.hi + u.hi⟩

/-- `a x + b y` for signed words `a, b` and signed numbers `x, y`. -/
@[inline] private def lin (a b : UInt64) (x y : Wide) : Wide :=
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
  -- So each remainder with a negative coefficient is complemented, and `|a|` joins the carry.
  let carry := (aa &&& maskA) + (bb &&& maskB)
  -- Multiply and add word by word, from the least significant, with the carry.
  let r0 := linWord aa bb (x.w0 ^^^ maskA) (y.w0 ^^^ maskB) carry
  let r1 := linWord aa bb (x.w1 ^^^ maskA) (y.w1 ^^^ maskB) r0.hi
  let r2 := linWord aa bb (x.w2 ^^^ maskA) (y.w2 ^^^ maskB) r1.hi
  let r3 := linWord aa bb (x.w3 ^^^ maskA) (y.w3 ^^^ maskB) r2.hi
  -- The top word is computed mod `2^64`, which is exact when the result fits five words.
  ⟨r0.lo, r1.lo, r2.lo, r3.lo, (x.top ^^^ maskA) * aa + (y.top ^^^ maskB) * bb + r3.hi⟩

/-- A number congruent to `x / 2^60 mod p`: `x + q p` for the `q` that makes it divisible by `2^60`.

The word `pinv` is `-p^(-1) mod 2^64`. -/
@[inline] private def adjust (x p : Wide) (pinv : UInt64) : Wide :=
  -- `q = -x p^(-1) mod 2^60`, so `x + q p = 0 mod 2^60`.
  let q := (x.w0 * pinv) &&& 0xfffffffffffffff
  -- `x + q p`, word by word, from the least significant, with the carry.
  let r0 := mac p.w0 q x.w0 0
  let r1 := mac p.w1 q x.w1 r0.hi
  let r2 := mac p.w2 q x.w2 r1.hi
  let r3 := mac p.w3 q x.w3 r2.hi
  -- The low 60 bits are zero, so the shift divides exactly.
  Wide.shr60 ⟨r0.lo, r1.lo, r2.lo, r3.lo, p.top * q + x.top + r3.hi⟩

/-- `sgn(f) d`, reduced into `[0, p)` by adding or subtracting `p`, then converted.

A `d` out of the range that these steps reduce gives a wrong candidate, which the check rejects. -/
@[noinline, specialize finish] private def normalize {A : Type} (finish : Wide → A)
    (d p : Wide) (neg : Bool) : A :=
  -- Step 7: the factor `sgn(f)`.
  let d := if neg then d.neg else d
  -- Add `p` while `d` is negative, at most twice.
  let d := if d.top >>> 63 == 0 then d else d.add p
  let d := if d.top >>> 63 == 0 then d else d.add p
  -- Subtract `p` once if `d - p` is not negative.
  let e := d.sub p
  if e.top >>> 63 == 0 then finish e else finish d

/-- The jumps of §12.1 on `(delta, f, g)` and on the coefficients `(d, e)`, up to a bound.

It returns `sgn(f) d mod p` once `g = 0`, or `none` when the jumps run out first. -/
@[noinline, specialize finish] private def run {A : Type} (finish : Wide → A)
    (p : Wide) (pinv : UInt64) :
    Nat → UInt64 → Wide → Wide → Wide → Wide → Option A
  -- A loop that has not finished after its jumps gives no candidate.
  | 0, _, f, g, d, _ =>
    if g.isZero then some (normalize finish d p (f.top >>> 63 != 0)) else none
  | fuel + 1, δ, f, g, d, e =>
    -- Step 7: once `g = 0`, `f = +-1` and `d x = f mod p`, so `x^-1 = sgn(f) d mod p`.
    --
    -- Each jump already divided `d` by `2^60` mod `p`, so no factor `2^-744` is left.
    --
    -- The paper always runs its full count of divsteps.
    --
    -- This loop stops early instead, since a divstep with `g = 0` keeps `f`.
    --
    -- So its time depends on the input.
    --
    -- EthLib makes no constant-time claim (SOUNDNESS.md A3).
    if g.isZero then some (normalize finish d p (f.top >>> 63 != 0))
    else
      -- §12.1, steps 2 and 3: the transition matrix of the next 60 divsteps, from the low words.
      --
      -- The paper takes 62 divsteps per jump.
      --
      -- Here a jump takes 60, ten blocks of the 6-step table.
      let t := jumpBlocks 10 δ f.w0 g.w0 1 0 0 1
      -- Step 4: `(f, g) <- T_i (f, g) / 2^60`.
      let nf := (lin t.aa t.ab f g).shr60
      let ng := (lin t.ba t.bb f g).shr60
      -- In place of step 6, the matrix also updates the coefficients `(d, e)` of `x` mod `p`.
      --
      -- Each gains a multiple of `p` that makes it divisible by `2^60`, keeping `d x = f mod p`.
      let nd := adjust (lin t.aa t.ab d e) p pinv
      let ne := adjust (lin t.ba t.bb d e) p pinv
      -- Step 5: `delta <- delta'`, then back to the low words for the next jump.
      run finish p pinv fuel t.delta nf ng nd ne

/-- A candidate for `a^(-1) mod p`, or `none` for `a = 0` or when the jumps run out. -/
@[noinline] private def candidate (p : Wide) (pinv : UInt64) (a : Nat) : Option Nat :=
  -- `0` has no inverse.
  if a = 0 then none
  else
    -- §12.1, step 1: `f = p`, `g = x`, `delta = 1`, with the coefficients `d = 0` and `e = 1`.
    --
    -- Theorem 11.2 needs `floor((49 * 256 + 57) / 17) = 741` divsteps for 256-bit inputs.
    --
    -- So thirteen jumps, 780 divsteps, always suffice.
    --
    -- A failure still falls back to Euclid.
    run Wide.lowNat p pinv 13 1 p (Wide.ofNat a) ⟨0, 0, 0, 0, 0⟩ ⟨1, 0, 0, 0, 0⟩

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

open Secp256k1.Montgomery in
/-- Read a 256-bit result of the inversion loop as a canonical residue. -/
@[inline] private def finishWords (w : Wide) : Montgomery :=
  -- The low four words, with a zero top word.
  let t : Words64 := ⟨w.w0, w.w1, w.w2, w.w3, 0⟩
  -- Any four words are below `2^256 < 2 p`, which is what the final reduction needs.
  finish t (by
    have h0 := w.w0.toNat_lt
    have h1 := w.w1.toNat_lt
    have h2 := w.w2.toNat_lt
    have h3 := w.w3.toNat_lt
    simp only [t, value, lowValue, wordRadix, Fp.modulus, UInt64.toNat_zero,
      Nat.mul_zero, Nat.add_zero]
    omega)

/-- The integer `R^3 mod p`, which turns the inverse of `x R` into the form of `x^(-1)`.

With `R = 2^256 = 2^32 + 977 mod p`, it is `(2^32 + 977)^3`, which is below `p`. -/
private def montgomeryCube : Montgomery := ⟨⟨0x2bb1e33795f671, 0x100000b73, 0, 0⟩, by decide⟩

/-- The candidate when its product with `a` is one, or else the Euclidean inverse. -/
@[inline] def checkMontgomery (c : Option Montgomery) (a : Montgomery) : Montgomery :=
  -- The extended Euclidean algorithm on the plain residue, returned in Montgomery form.
  let fallback := fun () => Montgomery.ofFin (Fin.inverse a.toFin)
  match c with
  -- No candidate: fall back.
  | none => fallback ()
  -- A candidate whose product with `a` is not one: fall back.
  | some b => if b * a = 1 then b else fallback ()

end Inverse

/-- The inverse of `a`, which sends `0` to `0`.

The divsteps give a candidate, and the Euclidean inverse replaces one that fails the check. -/
@[no_expose] def Fn.inv (a : Fn) : Fn :=
  -- The word constant is `-n^(-1) mod 2^64`.
  Inverse.check (Inverse.candidate (.ofNat Fn.modulus) 0x4b0dff665588b13f a.val) a

/-- The inverse of `a`, which sends `0` to `0`.

The divsteps invert the stored words `a R`, which gives `a^(-1) R^(-1)`.

A Montgomery product by `R^3` turns that into `a^(-1) R`, the stored form of the inverse. -/
@[no_expose] def Montgomery.inv (a : Montgomery) : Montgomery :=
  -- The stored words `a R mod p`.
  let w := a.raw
  let p := Inverse.Wide.ofNat Fp.modulus
  -- §12.1, step 1 on `g = a R`, with `-p^(-1) mod 2^64` for the division by `2^60`.
  --
  -- The result `a^(-1) R^(-1)` is multiplied by `R^3`, as a Montgomery product, to give `a^(-1) R`.
  let c := Inverse.run (fun w => Inverse.montgomeryCube * Inverse.finishWords w) p
    Montgomery.inverseComplement 13 1 p ⟨w.w0, w.w1, w.w2, w.w3, 0⟩ ⟨0, 0, 0, 0, 0⟩
    ⟨1, 0, 0, 0, 0⟩
  -- The Euclidean inverse replaces a candidate that fails the check.
  Inverse.checkMontgomery c a

/-- The inverse of `a`, which sends `0` to `0`.

It is the inverse of the Montgomery form of `a`, read back. -/
def Fp.inv (a : Fp) : Fp := (Montgomery.ofFin a).inv.toFin

end EthLib.Cryptography.Secp256k1
