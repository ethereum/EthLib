import EthLib.Cryptography.Secp256k1.Field

/-!
# `Secp256k1.Curve`

The curve `E: y^2 = x^3 + 7` over `Fp`, from SEC 2 v2 §2.4.1, where `a = 0` and `b = 7`.

A point is the point at infinity `O`, or a pair `(x, y)` that satisfies the equation.

The points form a group under the addition rule of SEC 1 v2 §2.2.1.
`O` is its zero, and `-(x, y) = (x, -y)`.

The rule is written in affine coordinates, as SEC 1 prints it.
Each addition then takes one inverse, which costs about 256 multiplications.
-/

namespace EthLib.Cryptography.Secp256k1

/-- `b`, the constant term of the curve equation, from SEC 2 v2 §2.4.1. -/
def b : Fp := 7

/-- A point of the curve: the point at infinity, or a pair of coordinates.

A pair is a point of the curve only when it satisfies the equation, which `isOnCurve` tests. -/
inductive Point where
  /-- The point at infinity `O`, the zero of the group. -/
  | infinity
  /-- The point `(x, y)`. -/
  | affine (x y : Fp)
deriving DecidableEq, Repr, Inhabited

namespace Point

/-- Whether a point satisfies the defining equation `y^2 = x^3 + 7`.

The point at infinity always does. -/
def isOnCurve : Point → Bool
  | infinity => true
  | affine x y => y * y == x * x * x + b

/-- The base point `G`, from SEC 2 v2 §2.4.1. -/
def generator : Point :=
  affine 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
    0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

/-- The negative of a point, from rule 3 of SEC 1 v2 §2.2.1: `-(x, y) = (x, -y)`. -/
def neg : Point → Point
  | infinity => infinity
  | affine x y => affine x (-y)

/-- The sum of two points, by the addition rule of SEC 1 v2 §2.2.1.

```text
    O + P = P + O = P                                       rules 1 and 2
    (x, y) + (x, -y) = O                                    rule 3
    x1 != x2:   l = (y2 - y1) / (x2 - x1)                   rule 4
    P = P, y1 != 0:   l = 3 x1^2 / (2 y1)                   rule 5, with a = 0
    then        x3 = l^2 - x1 - x2,   y3 = l (x1 - x3) - y1
```

Rule 5 writes `x3 = l^2 - 2 x1`, which is `l^2 - x1 - x2` when `x1 = x2`. -/
def add : Point → Point → Point
  | infinity, q => q
  | p, infinity => p
  | affine x1 y1, affine x2 y2 =>
    if x1 = x2 then
      -- The same x: two points of the curve are then equal, or opposite.
      if y2 = -y1 then infinity
      else
        -- Doubling, with the tangent's slope.
        let l := 3 * x1 * x1 * (2 * y1).inv
        let x3 := l * l - x1 - x2
        affine x3 (l * (x1 - x3) - y1)
    else
      -- Two different x: the chord's slope.
      let l := (y2 - y1) * (x2 - x1).inv
      let x3 := l * l - x1 - x2
      affine x3 (l * (x1 - x3) - y1)

instance : Add Point := ⟨add⟩

instance : Neg Point := ⟨neg⟩

/-- `k P`, for `k < 2^fuel`, by double and add on the bits of `k`, low bit first.

It recurses on `fuel`, so the kernel can run it. -/
def mulBits : Nat → Nat → Point → Point
  | 0, _, _ => infinity
  | fuel + 1, k, p =>
    -- `k P = (k mod 2) P + (k / 2) (2 P)`.
    let rest := mulBits fuel (k / 2) (p + p)
    if k % 2 = 1 then p + rest else rest

/-- `k P`, the scalar multiplication of SEC 1 v2 §2.2.1, for a scalar mod `n`.

`n` has 256 bits, so 256 steps cover every scalar. -/
def mul (k : Fn) (p : Point) : Point := mulBits 256 k.val p

end Point

end EthLib.Cryptography.Secp256k1
