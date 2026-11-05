module

public import EthLib.Cryptography.Bls.Fp

/-!
# `Fp2`

The quadratic extension `Fp2 = Fp[i] / (i^2 + 1)`, with elements `c0 + c1 i`.

The product follows from `i^2 = -1`: `(a + b i)(c + d i) = (ac - bd) + (ad + bc) i`.

The inverse uses the conjugate: `(a + b i)^(-1) = (a - b i) / (a^2 + b^2)`.

The code is generic in the base field, and the base field is `Fp` unless stated.

So proofs can run the same code on another base field with the same operations.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

/-- An element of the quadratic extension of `F`, written `c0 + c1 · i` with `i² = −1`.

The base field is `Fp` unless stated, so `Fp2` alone is the extension of BLS12-381. -/
structure Fp2 (F : Type := Fp) where
  c0 : F
  c1 : F
deriving Inhabited, BEq, Repr

namespace Fp2

variable {F : Type} [BaseField F]

@[inline] def zero : Fp2 F := ⟨BaseField.zero, BaseField.zero⟩
@[inline] def one  : Fp2 F := ⟨BaseField.one, BaseField.zero⟩
@[inline] def i    : Fp2 F := ⟨BaseField.zero, BaseField.one⟩

@[inline] def ofFp (x : F) : Fp2 F := ⟨x, BaseField.zero⟩

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

@[inline] def beq (a b : Fp2 F) : Bool := BaseField.beq a.c0 b.c0 && BaseField.beq a.c1 b.c1
@[inline] def isZero (a : Fp2 F) : Bool := BaseField.isZero a.c0 && BaseField.isZero a.c1

/-- Multiply by `1 + i`, the cubic-extension non-residue `ξ`. -/
@[inline] def mulByOnePlusI (a : Fp2 F) : Fp2 F :=
  ⟨a.c0 - a.c1, a.c0 + a.c1⟩

/-- Frobenius (complex conjugation): `c0 + c1·i ↦ c0 − c1·i`. -/
@[inline] def conjugate (a : Fp2 F) : Fp2 F := ⟨a.c0, -a.c1⟩

/-- Multiplicative inverse: `(c0 + c1·i)⁻¹ = (c0 − c1·i) / (c0² + c1²)`. -/
def inverse (a : Fp2 F) : Fp2 F :=
  let norm := a.c0 * a.c0 + a.c1 * a.c1   -- in the base field
  let invN := BaseField.inverse norm
  ⟨a.c0 * invN, -(a.c1 * invN)⟩

instance : Div (Fp2 F) := ⟨fun a b => a * b.inverse⟩

/-- Square-and-multiply by a `Nat`. -/
def powNat (base : Fp2 F) (e : Nat) : Fp2 F :=
  if e = 0 then one
  else
    let half := powNat (base * base) (e / 2)
    if e % 2 = 1 then base * half else half
-- Every nonzero exponent decreases when divided by two.
termination_by e
decreasing_by omega

end Fp2

end EthLib.Cryptography.Bls
