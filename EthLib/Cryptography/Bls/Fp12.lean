import EthLib.Cryptography.Bls.Fp6

/-!
# `Fp12`

The quadratic extension `Fp12 = Fp6[w] / (w² − v)`. Elements are written
`c0 + c1·w` with each coefficient in `Fp6`. The reduction rule is
`w² = v ∈ Fp6`, so multiplication is

  (a₀ + a₁·w)(b₀ + b₁·w) = (a₀·b₀ + v·a₁·b₁) + (a₀·b₁ + a₁·b₀)·w

Inversion comes from `(a₀ + a₁·w)·(a₀ − a₁·w) = a₀² − v·a₁²`, giving

  (a₀ + a₁·w)⁻¹ = (a₀ − a₁·w) / (a₀² − v·a₁²)
-/

namespace EthLib.Cryptography.Bls

/-- An element of `Fp12`, written `c0 + c1·w` with `w² = v`. -/
structure Fp12 where
  c0 : Fp6
  c1 : Fp6
deriving Inhabited, BEq, Repr

namespace Fp12

@[inline] def zero : Fp12 := ⟨Fp6.zero, Fp6.zero⟩
@[inline] def one  : Fp12 := ⟨Fp6.one,  Fp6.zero⟩

@[inline] def add (a b : Fp12) : Fp12 := ⟨a.c0 + b.c0, a.c1 + b.c1⟩
@[inline] def sub (a b : Fp12) : Fp12 := ⟨a.c0 - b.c0, a.c1 - b.c1⟩
@[inline] def neg (a : Fp12)   : Fp12 := ⟨-a.c0, -a.c1⟩

/-- Karatsuba-style multiplication. -/
def mul (a b : Fp12) : Fp12 :=
  let t0 := a.c0 * b.c0
  let t1 := a.c1 * b.c1
  let c0 := t0 + t1.mulByV
  let c1 := (a.c0 + a.c1) * (b.c0 + b.c1) - t0 - t1
  ⟨c0, c1⟩

instance : Add Fp12 := ⟨add⟩
instance : Sub Fp12 := ⟨sub⟩
instance : Mul Fp12 := ⟨mul⟩
instance : Neg Fp12 := ⟨neg⟩

@[inline] def beq (a b : Fp12) : Bool := a.c0.beq b.c0 && a.c1.beq b.c1
@[inline] def isOne (a : Fp12) : Bool :=
  -- a == ⟨one, zero⟩
  Fp6.beq a.c0 Fp6.one && Fp6.isZero a.c1

/-- Squaring. -/
@[inline] def square (a : Fp12) : Fp12 := a * a

/-- Inversion via the conjugate. -/
def inverse (a : Fp12) : Fp12 :=
  let norm := a.c0 * a.c0 - (a.c1 * a.c1).mulByV
  let invN := norm.inverse
  ⟨a.c0 * invN, -(a.c1 * invN)⟩

/-- Conjugation: `c0 + c1·w ↦ c0 − c1·w`. -/
@[inline] def conjugate (a : Fp12) : Fp12 := ⟨a.c0, -a.c1⟩

/-- Square-and-multiply modular exponentiation. -/
partial def powNat (base : Fp12) (e : Nat) : Fp12 :=
  if e = 0 then one
  else
    let half := powNat (base * base) (e / 2)
    if e % 2 = 1 then base * half else half

end Fp12

end EthLib.Cryptography.Bls
