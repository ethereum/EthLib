module

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

open Secp256k1.Montgomery in
/-- Read a 256-bit result of the inversion loop as a canonical residue. -/
@[inline] private def finishWords (w : Words64) : Montgomery :=
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
@[no_expose] def Fn.inv (a : Fn) : Fn := SafeGcd.inverseFin a

/-- The inverse of `a`, which sends `0` to `0`.

The divsteps invert the stored words `a R`, which gives `a^(-1) R^(-1)`.

A Montgomery product by `R^3` turns that into `a^(-1) R`, the stored form of the inverse. -/
@[no_expose] def Montgomery.inv (a : Montgomery) : Montgomery :=
  -- The stored words `a R mod p`.
  let w := a.raw
  let p := (rawOfNat Fp.modulus).words
  -- The divsteps on `x = a R`, with `-p^(-1) mod 2^64` for the division by `2^60`.
  --
  -- The result `a^(-1) R^(-1)` is multiplied by `R^3`, as a Montgomery product, to give `a^(-1) R`.
  let c := SafeGcd.Signed.inverse (fun w => Inverse.montgomeryCube * Inverse.finishWords w) p
    Montgomery.inverseComplement 13 w.words
  -- The Euclidean inverse replaces a candidate that fails the check.
  Inverse.checkMontgomery c a

/-- The inverse of `a`, which sends `0` to `0`.

It is the inverse of the Montgomery form of `a`, read back. -/
def Fp.inv (a : Fp) : Fp := (Montgomery.ofFin a).inv.toFin

end EthLib.Cryptography.Secp256k1
