module

public import EthLib.Cryptography.Secp256k1.RecoveryField

/-!
# Modular inversion for secp256k1 recovery

Recovery inverts a signature component and the final projective denominator.

Both inputs are public, so the jump loop can stop when the second remainder is zero.

The divstep transition comes from [Bernstein and Yang][safegcd] §8.1.

The low-word matrix construction follows §12.1, with 60 divsteps per jump.

Each jump uses a table of 6-step matrices generated from the scalar divstep recurrence.

A jump then applies that matrix to the full remainders and residues.

The final check accepts only a canonical residue whose product with the input is one.

[safegcd]: <https://gcd.cr.yp.to/safegcd-20190413.pdf>
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1.RecoveryInverse

open Fp.RecoveryField (plus minus mac)

private structure Transition where
  delta : UInt64
  aa : UInt64
  ab : UInt64
  ba : UInt64
  bb : UInt64

/-- Compute a jump matrix from the low words and the signed step state. -/
@[noinline] private def jump : Nat → UInt64 → UInt64 → UInt64 →
    UInt64 → UInt64 → UInt64 → UInt64 → Transition
  | 0, delta, _, _, aa, ab, ba, bb => ⟨delta, aa, ab, ba, bb⟩
  | fuel + 1, delta, f, g, aa, ab, ba, bb =>
    if g &&& 1 == 0 then
      jump fuel (delta + 1) f (g >>> 1) (aa + aa) (ab + ab) ba bb
    -- The high bit tests whether the signed step state is positive.
    else if (delta - 1) >>> 63 == 0 then
      jump fuel (1 - delta) g ((g - f) >>> 1) (ba + ba) (bb + bb) (ba - aa) (bb - ab)
    else
      jump fuel (delta + 1) f ((g + f) >>> 1) (aa + aa) (ab + ab) (ba + aa) (bb + ab)

/-- Pack 6-step transition matrices by the signed step state and the low bits of g / f.

The recurrence reads at most 6 low bits and uses f = 1 after dividing both inputs by the odd f.

The packed value stores the signed step state and the four signed coefficients.
-/
private def jumpTable : Vector Nat 1024 := Vector.ofFn fun i =>
  let d := (i.val >>> 6).toUInt64 - 6
  let g := i.val.toUInt64 &&& 63
  let t := jump 6 d 1 g 1 0 0 1
  let pack (a : UInt64) : UInt64 := a &&& 255
  (((t.delta &&& 63) <<< 32) |||
    (pack t.aa <<< 24) ||| (pack t.ab <<< 16) |||
    (pack t.ba <<< 8) ||| pack t.bb).toNat

/-- Extend a signed field of a table entry to one word. -/
@[inline] private def unpackCoefficient (w : UInt64) : UInt64 :=
  ((w &&& 255) ^^^ 128) - 128

/-- Apply one table transition for each block of 6 divsteps. -/
@[noinline] private def jumpBlocks : Nat → UInt64 → UInt64 → UInt64 →
    UInt64 → UInt64 → UInt64 → UInt64 → Transition
  | 0, delta, _, _, aa, ab, ba, bb => ⟨delta, aa, ab, ba, bb⟩
  | fuel + 1, delta, f, g, aa, ab, ba, bb =>
    -- Since f is odd, its square is one modulo eight.
    --
    -- One Newton step gives its inverse modulo 64 for the table index.
    let inv := f * (2 - f * f)
    let ratio := (g * inv) &&& 63
    let positive := delta.toInt64 > 6
    let negative := delta.toInt64 < -6
    let row : UInt64 := if positive then 12 else if negative then 0 else delta + 6
    let index := ((row <<< 6) ||| ratio) &&& 1023
    let entry := (jumpTable.get ⟨index.toNat, by
      rw [UInt64.toNat_and]
      change _ &&& ((2 : Nat) ^ 10 - 1) < _
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by decide)⟩).toUInt64
    -- A large positive delta is negated at most once, at the first odd step.
    --
    -- A large negative delta cannot change sign within this block.
    let nextDelta := (((entry >>> 32) ^^^ 32) - 32)
    let adjustment := if positive then
        if ratio == 0 then delta - 6 else 6 - delta
      else if negative then delta + 6 else 0
    let a := unpackCoefficient (entry >>> 24)
    let b := unpackCoefficient (entry >>> 16)
    let c := unpackCoefficient (entry >>> 8)
    let d := unpackCoefficient entry
    jumpBlocks fuel (nextDelta + adjustment) ((a*f + b*g) >>> 6) ((c*f + d*g) >>> 6)
      (a*aa + b*ba) (a*ab + b*bb) (c*aa + d*ba) (c*ab + d*bb)

/-- A signed integer in five words of two's complement. -/
private structure Wide where
  x0 : UInt64
  x1 : UInt64
  x2 : UInt64
  x3 : UInt64
  x4 : UInt64

@[inline] private def Wide.ofNat (a : Nat) : Wide :=
  ⟨a.toUInt64, (a >>> 64).toUInt64, (a >>> 128).toUInt64, (a >>> 192).toUInt64,
    (a >>> 256).toUInt64⟩

@[inline] private def Wide.lowNat (a : Wide) : Nat :=
  a.x0.toNat + ((a.x1.toNat + ((a.x2.toNat + (a.x3.toNat <<< 64)) <<< 64)) <<< 64)

@[inline] private def Wide.isZero (a : Wide) : Bool :=
  a.x0 ||| a.x1 ||| a.x2 ||| a.x3 ||| a.x4 == 0

@[inline] private def Wide.add (a b : Wide) : Wide :=
  let x0 := plus a.x0 b.x0 0
  let x1 := plus a.x1 b.x1 x0.hi
  let x2 := plus a.x2 b.x2 x1.hi
  let x3 := plus a.x3 b.x3 x2.hi
  ⟨x0.lo, x1.lo, x2.lo, x3.lo, a.x4 + b.x4 + x3.hi⟩

@[inline] private def Wide.sub (a b : Wide) : Wide :=
  let x0 := minus a.x0 b.x0 0
  let x1 := minus a.x1 b.x1 x0.hi
  let x2 := minus a.x2 b.x2 x1.hi
  let x3 := minus a.x3 b.x3 x2.hi
  ⟨x0.lo, x1.lo, x2.lo, x3.lo, a.x4 - b.x4 - x3.hi⟩

@[inline] private def Wide.neg (a : Wide) : Wide := Wide.sub ⟨0, 0, 0, 0, 0⟩ a

@[inline] private def Wide.shr60 (a : Wide) : Wide :=
  ⟨(a.x0 >>> 60) ||| (a.x1 <<< 4), (a.x1 >>> 60) ||| (a.x2 <<< 4),
    (a.x2 >>> 60) ||| (a.x3 <<< 4), (a.x3 >>> 60) ||| (a.x4 <<< 4),
    ((a.x4.toInt64) >>> (60 : UInt64).toInt64).toUInt64⟩

/-- Accumulate a pair of products with a single carry. -/
@[inline] private def linWord (a b x y carry : UInt64) : Fp.RecoveryField.Pair :=
  let t := mac x a 0 carry
  let u := mac y b t.lo 0
  ⟨u.lo, t.hi + u.hi⟩

/-- Multiply each remainder by a signed coefficient and add the two products. -/
@[inline] private def lin (a b : UInt64) (x y : Wide) : Wide :=
  let negA := a >>> 63
  let negB := b >>> 63
  let maskA := 0 - negA
  let maskB := 0 - negB
  let aa := (a ^^^ maskA) + negA
  let bb := (b ^^^ maskB) + negB
  -- Complement each remainder with a negative coefficient.
  --
  -- Add its magnitude to the carry to complete the two's complement negation.
  let carry := (aa &&& maskA) + (bb &&& maskB)
  let r0 := linWord aa bb (x.x0 ^^^ maskA) (y.x0 ^^^ maskB) carry
  let r1 := linWord aa bb (x.x1 ^^^ maskA) (y.x1 ^^^ maskB) r0.hi
  let r2 := linWord aa bb (x.x2 ^^^ maskA) (y.x2 ^^^ maskB) r1.hi
  let r3 := linWord aa bb (x.x3 ^^^ maskA) (y.x3 ^^^ maskB) r2.hi
  ⟨r0.lo, r1.lo, r2.lo, r3.lo, (x.x4 ^^^ maskA) * aa + (y.x4 ^^^ maskB) * bb + r3.hi⟩

/-- Add a multiple of the modulus so the residue divides by `2^60`. -/
@[inline] private def adjust (x p : Wide) (pinv : UInt64) : Wide :=
  let q := (x.x0 * pinv) &&& 0xfffffffffffffff
  let r0 := mac p.x0 q x.x0 0
  let r1 := mac p.x1 q x.x1 r0.hi
  let r2 := mac p.x2 q x.x2 r1.hi
  let r3 := mac p.x3 q x.x3 r2.hi
  Wide.shr60 ⟨r0.lo, r1.lo, r2.lo, r3.lo, p.x4 * q + x.x4 + r3.hi⟩

@[noinline, specialize finish] private def normalize {A : Type} (finish : Wide → A)
    (d p : Wide) (neg : Bool) : A :=
  let d := if neg then d.neg else d
  let d := if d.x4 >>> 63 == 0 then d else d.add p
  let d := if d.x4 >>> 63 == 0 then d else d.add p
  let e := d.sub p
  if e.x4 >>> 63 == 0 then finish e else finish d

@[noinline, specialize finish] private def run {A : Type} (finish : Wide → A)
    (p : Wide) (pinv : UInt64) :
    Nat → UInt64 → Wide → Wide → Wide → Wide → Option A
  | 0, _, f, g, d, _ =>
    if g.isZero then some (normalize finish d p (f.x4 >>> 63 != 0)) else none
  | fuel + 1, δ, f, g, d, e =>
    if g.isZero then some (normalize finish d p (f.x4 >>> 63 != 0))
    else
      let t := jumpBlocks 10 δ f.x0 g.x0 1 0 0 1
      let nf := (lin t.aa t.ab f g).shr60
      let ng := (lin t.ba t.bb f g).shr60
      let nd := adjust (lin t.aa t.ab d e) p pinv
      let ne := adjust (lin t.ba t.bb d e) p pinv
      run finish p pinv fuel t.delta nf ng nd ne

@[noinline] private def candidate (p : Wide) (pinv : UInt64) (a : Nat) : Option Nat :=
  if a = 0 then none
  else
    -- The attempt is limited to thirteen jumps.
    run Wide.lowNat p pinv 13 1 p (Wide.ofNat a) ⟨0, 0, 0, 0, 0⟩ ⟨1, 0, 0, 0, 0⟩

/-- Accept a canonical inverse candidate, or compute the inverse by exponentiation. -/
@[inline] def check {m : Nat} (c : Option Nat) (a : Fin m) : Fin m :=
  match c with
  | none => Fin.inversePrime a
  | some v =>
    if h : v < m ∧ v * a.val % m = 1 then ⟨v, h.1⟩ else Fin.inversePrime a

/-- The inverse of the final projective denominator in recovery. -/
@[no_expose] def invFp (a : Fp) : Fp :=
  check (candidate (Wide.ofNat Fp.modulus) Fp.RecoveryField.inverseComplement a.val) a

/-- The inverse of the signature component in recovery. -/
@[no_expose] def invFn (a : Fn) : Fn :=
  -- The word constant is -n^(-1) mod 2^64.
  check (candidate (Wide.ofNat Fn.modulus) 0x4b0dff665588b13f a.val) a

open Fp.RecoveryField in
/-- Read a 256-bit result of the inversion loop as a canonical residue. -/
@[inline] private def finishWords (w : Wide) : Element :=
  let t : Words64 := ⟨w.x0, w.x1, w.x2, w.x3, 0⟩
  finish t (by
    have h0 := w.x0.toNat_lt
    have h1 := w.x1.toNat_lt
    have h2 := w.x2.toNat_lt
    have h3 := w.x3.toNat_lt
    simp only [t, value, lowValue, wordRadix, Fp.modulus, UInt64.toNat_zero,
      Nat.mul_zero, Nat.add_zero]
    omega)

open Fp.RecoveryField in
/-- The canonical integer R^3 mod p, for converting the candidate to Montgomery form. -/
private def montgomeryCube : Element := ⟨⟨0x2bb1e33795f671, 0x100000b73, 0, 0⟩, by decide⟩

open Fp.RecoveryField in
/-- Check a candidate in the same field representation as the input. -/
@[inline] def checkMontgomery (c : Option Element) (a : Element) : Element :=
  let fallback := fun () => ofFin (Fin.inversePrime (toFin a))
  match c with
  | none => fallback ()
  | some b => if b * a = 1 then b else fallback ()

open Fp.RecoveryField in
/-- Invert the projective denominator using its Montgomery words. -/
@[no_expose] def invMontgomery (a : Element) : Element :=
  let w := a.raw
  let p := Wide.ofNat Fp.modulus
  -- Inverting the integer x R gives x^-1 R^-1, which a Montgomery product by R^3 rescales.
  let c := run (fun w => montgomeryCube * finishWords w) p inverseComplement 13 1 p
    ⟨w.w0, w.w1, w.w2, w.w3, 0⟩ ⟨0, 0, 0, 0, 0⟩ ⟨1, 0, 0, 0, 0⟩
  checkMontgomery c a

/-- Check a candidate for the scalar inverse in the word representation. -/
@[inline] def checkFnWords (c : Option Fp.RecoveryField.Raw) (a : Fp.RecoveryField.Raw) :
    Fp.RecoveryField.Raw :=
  let fallback := fun _ : Unit =>
    FnRecoveryWords.fromFin (Fin.inversePrime (FnRecoveryWords.toFin a))
  match c with
  | none => fallback ()
  | some b =>
    let q := FnRecoveryWords.mul b a
    if q.w0 == 1 && q.w1 == 0 && q.w2 == 0 && q.w3 == 0 && !FnRecoveryWords.geOrder b.words then
      b
    else fallback ()

/-- Invert a scalar using its four words directly. -/
@[no_expose] def invFnWords (a : Fp.RecoveryField.Raw) : Fp.RecoveryField.Raw :=
  let p := Wide.ofNat Fn.modulus
  let c := run (fun w => (⟨w.x0, w.x1, w.x2, w.x3⟩ : Fp.RecoveryField.Raw)) p
    0x4b0dff665588b13f 13 1 p ⟨a.w0, a.w1, a.w2, a.w3, 0⟩
    ⟨0, 0, 0, 0, 0⟩ ⟨1, 0, 0, 0, 0⟩
  checkFnWords c a

end EthLib.Cryptography.Secp256k1.RecoveryInverse
