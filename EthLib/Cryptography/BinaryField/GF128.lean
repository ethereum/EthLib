module

public import EthLib.Cryptography.BinaryField.GF64

/-!
# `BinaryField.GF128`

The field `E = K[y]/(y^2 + x y + 1)`, the quadratic extension of `K = GF(2^64)`.

Lidl and Niederreiter, Finite Fields, chapter 2, give extension fields, conjugates and norms.

An element is `c0 + c1 y`, with its two limbs `c0` and `c1` in `K`.

Addition is limb by limb.

Since `y^2 = x y + 1`, the product is `(a0 b0 + a1 b1) + (a0 b1 + a1 b0 + x a1 b1) y`.

The Frobenius map `e ↦ e^(2^64)` fixes `K` and sends `y` to its conjugate `y + x`.

The norm `e * e^(2^64)` lies in `K`.

The inverse is the Frobenius image times the inverse of the norm.

So zero has the inverse zero.

It is not intended to be constant-time.
-/

@[expose] public section

namespace EthLib.Cryptography.BinaryField

/-- An element `c0 + c1 y` of E = K[y]/(y^2 + x y + 1). -/
structure GF128 where
  c0 : GF64
  c1 : GF64
  deriving DecidableEq, Repr, Inhabited

namespace GF128

/-- The zero element. -/
def zero : GF128 := ⟨0, 0⟩

/-- The element `1`. -/
def one : GF128 := ⟨1, 0⟩

/-- The generator `g = x`, embedded. -/
def g : GF128 := ⟨GF64.g, 0⟩

/-- The embedding of K, as `c0 + 0 y`. -/
def ofBase (a : GF64) : GF128 := ⟨a, 0⟩

/-- The element `y`, a root of `y^2 + x y + 1`. -/
def y : GF128 := ⟨0, 1⟩

/-- Addition, limb by limb. -/
def add (a b : GF128) : GF128 := ⟨a.c0 + b.c0, a.c1 + b.c1⟩

/-- The product, with `y^2 = x y + 1`.

So `(a0 + a1 y)(b0 + b1 y)` is `(a0 b0 + a1 b1) + (a0 b1 + a1 b0 + x a1 b1) y`. -/
def mul (a b : GF128) : GF128 :=
  let p11 := a.c1 * b.c1
  ⟨a.c0 * b.c0 + p11, a.c0 * b.c1 + a.c1 * b.c0 + GF64.g * p11⟩

/-- Multiplication by an element of K, limb by limb. -/
def mulBase (a : GF128) (k : GF64) : GF128 := ⟨a.c0 * k, a.c1 * k⟩

/-- The square `a * a`. -/
def square (a : GF128) : GF128 := mul a a

/-- `a^n` by square and multiply, low bit first.

The power is `1` at `n = 0`.

Otherwise it is `(a^2)^(n / 2)`, times `a` when `n` is odd. -/
def pow (a : GF128) (n : Nat) : GF128 :=
  if n = 0 then one
  else
    let rest := pow (square a) (n / 2)
    if n % 2 = 1 then mul a rest else rest
termination_by n
decreasing_by omega

/-- `a^(2^64)`: K is fixed and `y` maps to `y + x`.

So `c0 + c1 y` maps to `(c0 + x c1) + c1 y`. -/
def frobenius (a : GF128) : GF128 := ⟨a.c0 + GF64.g * a.c1, a.c1⟩

/-- The inverse through the norm `a * a^(2^64)`, which lies in K.

It is `a^(2^64)` times the inverse in K of the norm.

The inverse of zero is zero. -/
def inv (a : GF128) : GF128 := mulBase (frobenius a) (mul a (frobenius a)).c0⁻¹

instance : Zero GF128 := ⟨zero⟩

instance : One GF128 := ⟨one⟩

instance : Add GF128 := ⟨add⟩

instance : Mul GF128 := ⟨mul⟩

instance : Inv GF128 := ⟨inv⟩

instance : Pow GF128 Nat := ⟨pow⟩

end GF128

end EthLib.Cryptography.BinaryField
