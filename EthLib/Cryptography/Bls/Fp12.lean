module

public import EthLib.Cryptography.Bls.Fp6

/-!
# `Fp12`

The quadratic extension `Fp12 = Fp6[w] / (w^2 - v)`, with elements `c0 + c1 w`.

With `w^2 = v`, the product is `(a0 + a1 w)(b0 + b1 w) = (a0 b0 + v a1 b1) + (a0 b1 + a1 b0) w`.

The code is generic in the base field, as for `Fp2`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

/-- An element of `Fp12`, written `c0 + c1·w` with `w^2 = v`.

The base field is `Fp` unless stated. -/
structure Fp12 (F : Type := Fp) where
  c0 : Fp6 F
  c1 : Fp6 F
deriving Inhabited, BEq, Repr

namespace Fp12

variable {F : Type} [BaseField F]

@[inline] def zero : Fp12 F := ⟨Fp6.zero, Fp6.zero⟩
@[inline] def one  : Fp12 F := ⟨Fp6.one,  Fp6.zero⟩

@[inline] def add (a b : Fp12 F) : Fp12 F := ⟨a.c0 + b.c0, a.c1 + b.c1⟩
@[inline] def sub (a b : Fp12 F) : Fp12 F := ⟨a.c0 - b.c0, a.c1 - b.c1⟩
@[inline] def neg (a : Fp12 F)   : Fp12 F := ⟨-a.c0, -a.c1⟩

/-- The product, by the Karatsuba method of [Devegili et al.][dev], §3, with `β = v`.

[dev]: https://eprint.iacr.org/2006/471
-/
def mul (a b : Fp12 F) : Fp12 F :=
  -- §3: `v0 = a0 b0`, `v1 = a1 b1`.
  let t0 := a.c0 * b.c0
  let t1 := a.c1 * b.c1
  -- §3: `c0 = v0 + β v1`.
  let c0 := t0 + t1.mulByV
  -- §3: `c1 = (a0 + a1)(b0 + b1) - v0 - v1`.
  let c1 := (a.c0 + a.c1) * (b.c0 + b.c1) - t0 - t1
  ⟨c0, c1⟩

instance : Add (Fp12 F) := ⟨add⟩
instance : Sub (Fp12 F) := ⟨sub⟩
instance : Mul (Fp12 F) := ⟨mul⟩
instance : Neg (Fp12 F) := ⟨neg⟩

@[inline] def beq (a b : Fp12 F) : Bool := a.c0.beq b.c0 && a.c1.beq b.c1
@[inline] def isOne (a : Fp12 F) : Bool :=
  -- a == ⟨one, zero⟩
  Fp6.beq a.c0 Fp6.one && Fp6.isZero a.c1

/-- Squaring. -/
@[inline] def square (a : Fp12 F) : Fp12 F := a * a

/-- Squaring in the cyclotomic subgroup, by [Granger and Scott][source], §3.2, equation (5).

Over `Fp`, it equals `a * a` when `a^(p^4 - p^2 + 1) = 1`, and also at zero.

Here `p` is the modulus of `Fp`, and `z_k` in `Fp2` is the coefficient of `w^k`.

It is the "cubic over a quadratic extension" form of §3.2, with `x = w` and `y = w^3`.

So the element is `a + b x + c x^2`, with `a = z0 + z3 y`, `b = z1 + z4 y`, `c = z2 + z5 y`.

These lie in `Fp4 = Fp2[y] / (y^2 - (1 + i))`.

[source]: https://eprint.iacr.org/2009/565
-/
def cyclotomicSquare (a : Fp12 F) : Fp12 F :=
  -- §3.1: `(a + b y)^2 = (a + i b)(a + b) - a b (1 + i) + 2 a b y`, with `y^2 = i`.
  --
  -- Here the constant `i` of §3.1 is `1 + i` of `Fp2`, as `y^2 = 1 + i`.
  let squareFp4 (x y : Fp2 F) :=
    let xy := x * y
    ((x + y.mulByOnePlusI) * (x + y) - xy - xy.mulByOnePlusI, xy + xy)
  let tripleSubDouble (x y : Fp2 F) :=
    let d := x - y
    d + d + x
  let tripleAddDouble (x y : Fp2 F) :=
    let d := x + y
    d + d + x
  -- The squares `a^2`, `b^2` and `c^2` in `Fp4`.
  let sa := squareFp4 a.c0.c0 a.c1.c1
  let sb := squareFp4 a.c1.c0 a.c0.c2
  let sc := squareFp4 a.c0.c1 a.c1.c2
  -- §3.2, cubic form: `A = 3 a^2 - 2 conj(a)` and `C = 3 b^2 - 2 conj(c)`.
  --
  -- §3.2, cubic form: `B = 3 sqrt(i) c^2 + 2 conj(b)`.
  --
  -- Here `sqrt(i) = y`, since `y^2 = i`.
  --
  -- `conj` negates the `y` part, and `y (u0 + u1 y) = (1 + i) u1 + u0 y`.
  --
  -- The coefficients of `w^0` to `w^5` are then `A_0`, `B_0`, `C_0`, `A_1`, `B_1`, `C_1`.
  ⟨⟨tripleSubDouble sa.1 a.c0.c0, tripleSubDouble sb.1 a.c0.c1,
      tripleSubDouble sc.1 a.c0.c2⟩,
    ⟨tripleAddDouble sc.2.mulByOnePlusI a.c1.c0, tripleAddDouble sa.2 a.c1.c1,
      tripleAddDouble sb.2 a.c1.c2⟩⟩

/-- Inversion via the conjugate. -/
def inverse (a : Fp12 F) : Fp12 F :=
  -- `(a0 + a1 w)(a0 - a1 w) = a0^2 - v a1^2`, an element of `Fp6`.
  --
  -- So `(a0 + a1 w)^(-1) = (a0 - a1 w) / (a0^2 - v a1^2)`.
  let norm := a.c0 * a.c0 - (a.c1 * a.c1).mulByV
  let invN := norm.inverse
  ⟨a.c0 * invN, -(a.c1 * invN)⟩

/-- Conjugation: `c0 + c1·w ↦ c0 − c1·w`. -/
@[inline] def conjugate (a : Fp12 F) : Fp12 F := ⟨a.c0, -a.c1⟩

/-- The constant `γ = ξ^((p - 1) / 6)` of the Frobenius map, with `ξ = 1 + i`.

Since `w^6 = ξ`, the `p`-th power of `w` is `γ w`.

The exponent uses `p`, so this holds only when the base field models the integers mod `p`. -/
def frobeniusCoeff : Fp2 F := Fp2.powNat ⟨BaseField.one, BaseField.one⟩ ((Fp.modulus - 1) / 6)

/-- The Frobenius map `a ↦ a^p`.

Write `a` as the sum of `a_k w^k` for `k < 6`, with each `a_k` in `Fp2`.

The `p`-th power is a ring map, the `p`-th power of `a_k` is its conjugate, and `w^p = γ w`.

So the `p`-th power of `a` is the sum of `conj(a_k) γ^k w^k`.

In `c0 + c1 w`, the coefficient `a_k` sits in `c0` for even `k` and in `c1` for odd `k`. -/
def frobenius (a : Fp12 F) : Fp12 F :=
  let g1 := frobeniusCoeff
  let g2 := g1 * g1
  let g3 := g2 * g1
  ⟨⟨a.c0.c0.conjugate, a.c0.c1.conjugate * g2, a.c0.c2.conjugate * (g2 * g2)⟩,
   ⟨a.c1.c0.conjugate * g1, a.c1.c1.conjugate * g3, a.c1.c2.conjugate * (g3 * g2)⟩⟩

/-- Square-and-multiply exponentiation that squares with the cyclotomic formula.

Over `Fp`, it equals `base^e` when `base` is zero or lies in the cyclotomic subgroup. -/
def cyclotomicPow (base : Fp12 F) (e : Nat) : Fp12 F :=
  if e = 0 then one
  else
    let half := cyclotomicPow base.cyclotomicSquare (e / 2)
    if e % 2 = 1 then base * half else half
-- Every nonzero exponent decreases when divided by two.
termination_by e
decreasing_by omega

end Fp12

end EthLib.Cryptography.Bls
