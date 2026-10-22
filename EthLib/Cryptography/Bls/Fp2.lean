import EthLib.Cryptography.Bls.Fp

/-!
# `Fp2`

The quadratic extension `Fp2 = Fp[i] / (i² + 1)`. Elements look like
`c0 + c1·i` and arithmetic is the obvious "complex-number" rules:

  (a + b·i)(c + d·i) = (ac − bd) + (ad + bc)·i        (since i² = −1)

Inversion uses the conjugate identity:

  (a + b·i)⁻¹ = (a − b·i) / (a² + b²)
-/

namespace EthLib.Cryptography.Bls

/-- An element of `Fp2`, written `c0 + c1 · i` with `i² = −1`. -/
structure Fp2 where
  c0 : Fp
  c1 : Fp
deriving Inhabited, BEq, Repr

namespace Fp2

@[inline] def zero : Fp2 := ⟨Fp.zero, Fp.zero⟩
@[inline] def one  : Fp2 := ⟨Fp.one,  Fp.zero⟩
@[inline] def i    : Fp2 := ⟨Fp.zero, Fp.one⟩

@[inline] def ofFp (x : Fp) : Fp2 := ⟨x, Fp.zero⟩

@[inline] def add (a b : Fp2) : Fp2 := ⟨a.c0 + b.c0, a.c1 + b.c1⟩
@[inline] def sub (a b : Fp2) : Fp2 := ⟨a.c0 - b.c0, a.c1 - b.c1⟩
@[inline] def neg (a : Fp2)   : Fp2 := ⟨-a.c0, -a.c1⟩

@[inline] def mul (a b : Fp2) : Fp2 :=
  -- (a0 + a1·i)(b0 + b1·i) = (a0·b0 − a1·b1) + (a0·b1 + a1·b0)·i
  ⟨a.c0 * b.c0 - a.c1 * b.c1, a.c0 * b.c1 + a.c1 * b.c0⟩

instance : Add Fp2 := ⟨add⟩
instance : Sub Fp2 := ⟨sub⟩
instance : Mul Fp2 := ⟨mul⟩
instance : Neg Fp2 := ⟨neg⟩

@[inline] def beq (a b : Fp2) : Bool := a.c0.beq b.c0 && a.c1.beq b.c1
@[inline] def isZero (a : Fp2) : Bool := a.c0.isZero && a.c1.isZero

/-- Multiply by `1 + i`, the cubic-extension non-residue `ξ`. -/
@[inline] def mulByOnePlusI (a : Fp2) : Fp2 :=
  ⟨a.c0 - a.c1, a.c0 + a.c1⟩

/-- Frobenius (complex conjugation): `c0 + c1·i ↦ c0 − c1·i`. -/
@[inline] def conjugate (a : Fp2) : Fp2 := ⟨a.c0, -a.c1⟩

/-- Multiplicative inverse: `(c0 + c1·i)⁻¹ = (c0 − c1·i) / (c0² + c1²)`. -/
def inverse (a : Fp2) : Fp2 :=
  let norm := a.c0 * a.c0 + a.c1 * a.c1   -- in Fp
  let invN := norm.inverse
  ⟨a.c0 * invN, -(a.c1 * invN)⟩

instance : Div Fp2 := ⟨fun a b => a * b.inverse⟩

/-- Square-and-multiply by a `Nat`. -/
partial def powNat (base : Fp2) (e : Nat) : Fp2 :=
  if e = 0 then one
  else
    let half := powNat (base * base) (e / 2)
    if e % 2 = 1 then base * half else half

end Fp2

end EthLib.Cryptography.Bls
