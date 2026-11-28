module

public import EthLib.Cryptography.Inverse
public import EthLib.Cryptography.SafeGcd
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

/-- A signed integer in five words of two's complement, least significant first. -/
private abbrev Wide := Montgomery.Words64

/-- `a mod 2^320` in five words. -/
@[inline] private def Wide.ofNat (a : Nat) : Wide :=
  ⟨a.toUInt64, (a >>> 64).toUInt64, (a >>> 128).toUInt64, (a >>> 192).toUInt64,
    (a >>> 256).toUInt64⟩

/-- The integer of the low four words, which is the value of a number in `[0, 2^256)`. -/
@[inline] private def Wide.lowNat (a : Wide) : Nat :=
  a.w0.toNat + ((a.w1.toNat + ((a.w2.toNat + (a.w3.toNat <<< 64)) <<< 64)) <<< 64)

/-- A candidate for `a^(-1) mod p`, or `none` for `a = 0` or when the jumps run out. -/
@[noinline] private def candidate (p : Wide) (pinv : UInt64) (a : Nat) : Option Nat :=
  -- `0` has no inverse.
  if a = 0 then none
  else
    -- Theorem 11.2 needs `floor((49 * 256 + 57) / 17) = 741` divsteps for 256-bit inputs.
    --
    -- So thirteen jumps, 780 divsteps, always suffice.
    --
    -- A failure still falls back to Euclid.
    SafeGcd.Signed.inverse Wide.lowNat p pinv 13 (Wide.ofNat a)

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
  -- The divsteps on `x = a R`, with `-p^(-1) mod 2^64` for the division by `2^60`.
  --
  -- The result `a^(-1) R^(-1)` is multiplied by `R^3`, as a Montgomery product, to give `a^(-1) R`.
  let c := SafeGcd.Signed.inverse (fun w => Inverse.montgomeryCube * Inverse.finishWords w) p
    Montgomery.inverseComplement 13 ⟨w.w0, w.w1, w.w2, w.w3, 0⟩
  -- The Euclidean inverse replaces a candidate that fails the check.
  Inverse.checkMontgomery c a

/-- The inverse of `a`, which sends `0` to `0`.

It is the inverse of the Montgomery form of `a`, read back. -/
def Fp.inv (a : Fp) : Fp := (Montgomery.ofFin a).inv.toFin

end EthLib.Cryptography.Secp256k1
