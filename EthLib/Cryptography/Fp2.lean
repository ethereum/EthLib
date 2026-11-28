module

public import EthLib.Cryptography.BaseField

/-!
# `Fp2`

The quadratic extension `F[i] / (i^2 + 1)` of a base field `F`, with elements `c0 + c1 i`.

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

-- The code reads only the field operations of the base field.
--
-- So proofs can run the same code on another base field with the same operations.
variable {F : Type} [FieldOps F]

@[inline] def zero : Fp2 F := ⟨FieldOps.zero, FieldOps.zero⟩
@[inline] def one  : Fp2 F := ⟨FieldOps.one, FieldOps.zero⟩
@[inline] def i    : Fp2 F := ⟨FieldOps.zero, FieldOps.one⟩

@[inline] def ofFp (x : F) : Fp2 F := ⟨x, FieldOps.zero⟩

-- The numerals `0` and `1` of the extension.
instance : Zero (Fp2 F) := ⟨zero⟩
instance : One (Fp2 F) := ⟨one⟩

@[inline] def add (a b : Fp2 F) : Fp2 F := ⟨a.c0 + b.c0, a.c1 + b.c1⟩
@[inline] def sub (a b : Fp2 F) : Fp2 F := ⟨a.c0 - b.c0, a.c1 - b.c1⟩
@[inline] def neg (a : Fp2 F)   : Fp2 F := ⟨-a.c0, -a.c1⟩

/-- The product, by the Karatsuba method of [Devegili et al.][dev], §3, with `β = -1`.

It takes three products of the base field instead of four.

[dev]: https://eprint.iacr.org/2006/471
-/
@[inline] def mul (a b : Fp2 F) : Fp2 F :=
  -- The product follows from `i^2 = -1`.
  --
  -- (a0 + a1·i)(b0 + b1·i) = (a0·b0 − a1·b1) + (a0·b1 + a1·b0)·i
  --
  -- §3: `v0 = a0 b0` and `v1 = a1 b1`.
  let v0 := a.c0 * b.c0
  let v1 := a.c1 * b.c1
  -- §3: `c0 = v0 + β v1` and `c1 = (a0 + a1)(b0 + b1) - v0 - v1`.
  ⟨v0 - v1, (a.c0 + a.c1) * (b.c0 + b.c1) - v0 - v1⟩

/-- Squaring, by the complex method of [Devegili et al.][dev], §3, with `β = -1`.

It takes two products of the base field, where the product of two elements takes three.

[dev]: https://eprint.iacr.org/2006/471
-/
@[inline] def square (a : Fp2 F) : Fp2 F :=
  -- §3: `v0 = a0 a1`.
  let t := a.c0 * a.c1
  -- §3: `c0 = (a0 + a1)(a0 + β a1) - v0 - β v0`, which is `(a0 + a1)(a0 - a1)` for `β = -1`.
  --
  -- §3: `c1 = 2 v0`.
  ⟨(a.c0 + a.c1) * (a.c0 - a.c1), t + t⟩

/-- The product by an element of the base field, with two products of the base field. -/
@[inline] def mulFp (a : Fp2 F) (x : F) : Fp2 F := ⟨a.c0 * x, a.c1 * x⟩

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
  -- The inverse uses the conjugate, divided by the norm.
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
  square := square

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

-- The constants, the square root and the sign also read the base field's own operations.
variable {F : Type} [BaseField F]

/-- The element `c0 + c1 * i`, from its two coordinates as integers.

The specifications write the constants of `Fp2` this way, as pairs of integers below `p`. -/
def ofNats (c0 c1 : Nat) : Fp2 F :=
  ⟨BaseField.ofNat c0, BaseField.ofNat c1⟩

/-- A square root of `a`, given a square root `s` of its norm `a0^2 + a1^2`.

It is the [complex method][source] of Adj and Rodríguez-Henríquez, Algorithm 8, past step 9.

When the candidate root of the base field squares to its input or its negation, as over BLS12-381:

- a real input needs one exponentiation, and reads no `s`;
- any other input needs one, and two inversions of the base field.

[source]: https://eprint.iacr.org/2012/685
-/
def sqrtOfNormRoot (a : Fp2 F) (s : F) : Fp2 F :=
  -- The steps are those of Algorithm 8 of the source.
  --
  -- The base-field candidate squares to its input or to the negation of its input.
  --
  -- Step 1: the case `a1 = 0`.
  if BaseField.isZero a.c1 then
    -- Step 2: the root is `SQRT_q(a0)`.
    --
    -- That root exists only when `a0` is a square of the base field.
    --
    -- Otherwise the candidate `c` squares to `-a0`, and `c i` is a root, since `i^2 = -1`.
    let c := BaseField.sqrtCandidate a.c0
    if BaseField.beq (c * c) a.c0 then ⟨c, BaseField.zero⟩
    else ⟨BaseField.zero, c⟩
  else
    -- Step 10: `delta <- (a0 + alpha) / 2`, with `alpha = s` the root of the norm.
    let u := (a.c0 + s) * BaseField.inverse (BaseField.ofNat 2 : F)
    -- Steps 11 to 15 test `delta` and take `x0 <- SQRT_q(delta)`.
    --
    -- Here the candidate `c` of `delta` squares to `delta` or to `-delta`, with no test first.
    let c := BaseField.sqrtCandidate u
    -- Step 16: `x1 <- a1 / (2 x0)`, with `x0 = c`.
    let d := a.c1 * BaseField.inverse (BaseField.ofNat 2 * c)
    -- Step 17: `x <- x0 + x1 y`, with `y = i`, when `c^2 = delta`.
    --
    -- When `c^2 = -delta`, `x0 = d` is the root of step 13's `(a0 - alpha) / 2`, and `x1 = c`.
    --
    -- So the root is `d + c i`, with one exponentiation instead of a test and a square root.
    if BaseField.beq (c * c) u then ⟨c, d⟩ else ⟨d, c⟩

/-- A square root, by the [complex method][source] of Adj and Rodríguez-Henríquez, §V.A.

It returns `none` when the square root of the base field finds no root of the norm of the input.

Which of the two roots it returns is not fixed, since every caller chooses the sign afterwards.

[source]: https://eprint.iacr.org/2012/685
-/
def sqrt (a : Fp2 F) : Option (Fp2 F) :=
  -- Step 1: a real input needs no root of its norm.
  if BaseField.isZero a.c1 then some (sqrtOfNormRoot a BaseField.zero)
  -- Step 4: `alpha <- a0^2 - beta a1^2`, with `beta = -1`.
  --
  -- Steps 5 to 8: `gamma <- chi_q(alpha)`, and the input is not a square when `gamma = -1`.
  --
  -- Step 9: `alpha <- SQRT_q(alpha)`.
  --
  -- Steps 5 to 9 are one call of the base-field square root, which fails on a non-square.
  else (BaseField.sqrt (a.c0 * a.c0 + a.c1 * a.c1)).map (sqrtOfNormRoot a)

/-- The sign `sgn0` of [RFC 9380 §4.1][sgn0], the case `m = 2` for `x = x_0 + x_1 * I`.

The sign is the parity of `x_0`, or the parity of `x_1` when `x_0 = 0`.

[sgn0]: https://www.rfc-editor.org/rfc/rfc9380#section-4.1
-/
def sgn0 (x : Fp2 F) : Bool :=
  -- Step 1: `sign_0 = x_0 mod 2`.
  let s0 := BaseField.sgn0 x.c0
  -- Step 2: `zero_0` is true exactly when `x_0 = 0`.
  let z0 := BaseField.isZero x.c0
  -- Step 3: `sign_1 = x_1 mod 2`.
  let s1 := BaseField.sgn0 x.c1
  -- Steps 4 and 5: the sign is `sign_0 OR (zero_0 AND sign_1)`.
  s0 || (z0 && s1)

end BaseField

end Fp2

end EthLib.Cryptography
