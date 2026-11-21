module

public import EthLib.Cryptography.BaseField

/-!
# `Fp2`

The quadratic extension `F[i] / (i^2 + 1)` of a base field `F`, with elements `c0 + c1 i`.

The product follows from `i^2 = -1`: `(a + b i)(c + d i) = (ac - bd) + (ad + bc) i`.

The inverse uses the conjugate: `(a + b i)^(-1) = (a - b i) / (a^2 + b^2)`.

The code reads only the field operations of the base field.

So proofs can run the same code on another base field with the same operations.

The square root and the sign also read the square root and the sign of the base field.

BLS12-381 and alt_bn128 both build their extension of degree 2 this way.
-/

@[expose] public section

namespace EthLib.Cryptography

/-- An element of the quadratic extension of `F`, written `c0 + c1 · i` with `i^2 = −1`. -/
structure Fp2 (F : Type) where
  /-- The coefficient of 1. -/
  c0 : F
  /-- The coefficient of `i`. -/
  c1 : F
deriving Inhabited, BEq, DecidableEq, Repr

namespace Fp2

variable {F : Type} [FieldOps F]

@[inline] def zero : Fp2 F := ⟨FieldOps.zero, FieldOps.zero⟩
@[inline] def one  : Fp2 F := ⟨FieldOps.one, FieldOps.zero⟩
@[inline] def i    : Fp2 F := ⟨FieldOps.zero, FieldOps.one⟩

@[inline] def ofFp (x : F) : Fp2 F := ⟨x, FieldOps.zero⟩

@[inline] def add (a b : Fp2 F) : Fp2 F := ⟨a.c0 + b.c0, a.c1 + b.c1⟩
@[inline] def sub (a b : Fp2 F) : Fp2 F := ⟨a.c0 - b.c0, a.c1 - b.c1⟩
@[inline] def neg (a : Fp2 F)   : Fp2 F := ⟨-a.c0, -a.c1⟩

@[inline] def mul (a b : Fp2 F) : Fp2 F :=
  -- (a0 + a1·i)(b0 + b1·i) = (a0·b0 − a1·b1) + (a0·b1 + a1·b0)·i
  ⟨a.c0 * b.c0 - a.c1 * b.c1, a.c0 * b.c1 + a.c1 * b.c0⟩

instance : Add (Fp2 F) := ⟨add⟩
instance : Sub (Fp2 F) := ⟨sub⟩
instance : Mul (Fp2 F) := ⟨mul⟩
instance : Neg (Fp2 F) := ⟨neg⟩

@[inline] def beq (a b : Fp2 F) : Bool := FieldOps.beq a.c0 b.c0 && FieldOps.beq a.c1 b.c1
@[inline] def isZero (a : Fp2 F) : Bool := FieldOps.isZero a.c0 && FieldOps.isZero a.c1

/-- Frobenius (complex conjugation): `c0 + c1·i ↦ c0 − c1·i`. -/
@[inline] def conjugate (a : Fp2 F) : Fp2 F := ⟨a.c0, -a.c1⟩

/-- Multiplicative inverse: `(c0 + c1·i)⁻¹ = (c0 − c1·i) / (c0^2 + c1^2)`, and 0 for 0. -/
def inverse (a : Fp2 F) : Fp2 F :=
  let norm := a.c0 * a.c0 + a.c1 * a.c1   -- in the base field
  let invN := FieldOps.inverse norm
  ⟨a.c0 * invN, -(a.c1 * invN)⟩

instance : Div (Fp2 F) := ⟨fun a b => a * b.inverse⟩

/-- The field operations of the extension.

Code that reads only the field operations of its base field can then run on the extension.

The inverse of zero is zero, as for the inverse of the extension. -/
instance : FieldOps (Fp2 F) where
  toAdd := inferInstance
  toSub := inferInstance
  toMul := inferInstance
  toNeg := inferInstance
  zero := zero
  one := one
  beq := beq
  isZero := isZero
  inverse := inverse

/-- Square-and-multiply by a `Nat`. -/
def powNat (base : Fp2 F) (e : Nat) : Fp2 F :=
  if e = 0 then one
  else
    let half := powNat (base * base) (e / 2)
    if e % 2 = 1 then base * half else half
-- Every nonzero exponent decreases when divided by two.
termination_by e
decreasing_by omega

section BaseField

variable {F : Type} [BaseField F]

/-- A square root, by the [complex method][source] of Adj and Rodríguez-Henríquez, §V.A.

It relies on the base-field candidate, whose square is its input or the negation of its input.

It returns `none` when the square root of the base field finds no root of the norm of the input.

Which of the two roots it returns is not fixed, since every caller chooses the sign afterwards.

Write the input as `a0 + a1*i` with `i^2 = -1`, and let `s` be a root of the norm `a0^2 + a1^2`.

The base-field candidate `c` of `(a0 + s)/2` squares to it or to its negation.

In the first case `c + (a1/(2*c))*i` is a root, and in the second `a1/(2*c) + c*i` is one.

When the base-field candidate and square root are one exponentiation each, as over BLS12-381:

- a real input needs one exponentiation;
- any other input needs at most two.

[source]: https://eprint.iacr.org/2012/685
-/
def sqrt (a : Fp2 F) : Option (Fp2 F) :=
  -- Real input: the candidate of `a0` squares to `a0` or to `-a0`.
  if BaseField.isZero a.c1 then
    let c := BaseField.sqrtCandidate a.c0
    if BaseField.beq (c * c) a.c0 then some ⟨c, BaseField.zero⟩
    else some ⟨BaseField.zero, c⟩
  else
    match BaseField.sqrt (a.c0 * a.c0 + a.c1 * a.c1) with
    | none => none
    | some s =>
      let u := (a.c0 + s) * BaseField.inverse (BaseField.ofNat 2 : F)
      let c := BaseField.sqrtCandidate u
      let d := a.c1 * BaseField.inverse (BaseField.ofNat 2 * c)
      if BaseField.beq (c * c) u then some ⟨c, d⟩ else some ⟨d, c⟩

/-- The sign `sgn0` of [RFC 9380 §4.1][sgn0], the case `m = 2` for `x = x_0 + x_1 * I`.

The sign is the parity of `x_0`, or the parity of `x_1` when `x_0 = 0`.

[sgn0]: https://www.rfc-editor.org/rfc/rfc9380#section-4.1
-/
def sgn0 (x : Fp2 F) : Bool :=
  -- Step 1: `sign_0 = x_0 mod 2`.
  let s0 := BaseField.sgn0 x.c0
  -- Step 2: `zero_0 = x_0 == 0`.
  let z0 := BaseField.isZero x.c0
  -- Step 3: `sign_1 = x_1 mod 2`.
  let s1 := BaseField.sgn0 x.c1
  -- Steps 4 and 5: `return sign_0 OR (zero_0 AND sign_1)`.
  s0 || (z0 && s1)

end BaseField

end Fp2

end EthLib.Cryptography
