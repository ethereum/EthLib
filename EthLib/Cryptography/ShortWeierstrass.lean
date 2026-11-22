module

public import EthLib.Cryptography.Jacobian

/-!
# Short Weierstrass curves

The curve `E: y^2 = x^3 + a x + b` over a field of characteristic other than 2.

It is written once for every such curve.

A point is the point at infinity `O`, or a pair `(x, y)` that satisfies the equation.

The points form a group under the addition rule of SEC 1 v2 §2.2.1.

`O` is its zero, and `-(x, y) = (x, -y)`.

The rule is written in affine coordinates, as SEC 1 prints it.

Scalar multiplication runs in Jacobian coordinates instead, over any such field.

It takes one inverse, at the end.

Each curve gives its field, the constants `a` and `b`, and the inverse that its rule uses.
-/

@[expose] public section

namespace EthLib.Cryptography.ShortWeierstrass

/-- The constants of a curve over the field `F`, and the inverse of `F` that the rule uses.

The class states no laws: proofs take them from a map into a field. -/
class Params (F : Type) where
  /-- `a`, the coefficient of `x` in the equation. -/
  a : F
  /-- `b`, the constant term of the equation. -/
  b : F
  /-- The multiplicative inverse of the field. -/
  inv : F → F

/-- A point of the curve: the point at infinity, or a pair of coordinates.

A pair is a point of the curve only when it satisfies the equation. -/
inductive Point (F : Type) where
  /-- The point at infinity `O`, the zero of the group. -/
  | infinity
  /-- The point `(x, y)`. -/
  | affine (x y : F)
deriving DecidableEq, Repr, Inhabited

namespace Point

open Params (a b inv)

section Affine

variable {F : Type} [Add F] [Sub F] [Mul F] [Neg F] [OfNat F 0] [OfNat F 2] [OfNat F 3]
  [DecidableEq F] [Params F]

/-- Whether a point satisfies the equation `y^2 = x^3 + a x + b`.

The point at infinity always does.

When `a = 0`, the term `a x` is skipped. -/
@[specialize] def isOnCurve : Point F → Bool
  | infinity => true
  | affine x y => y * y == if (a : F) = 0 then x * x * x + b else x * x * x + a * x + b

/-- The negative of a point, from rule 3 of SEC 1 v2 §2.2.1: `-(x, y) = (x, -y)`. -/
def neg : Point F → Point F
  | infinity => infinity
  | affine x y => affine x (-y)

/-- The sum of two points, by the addition rule of [SEC 1 v2][sec1] §2.2.1.

SEC 1 states the rule over a prime field.

The same formulas hold over any field of characteristic other than 2, such as `Fp2`.

[sec1]: https://www.secg.org/sec1-v2.pdf
-/
@[specialize] def add : Point F → Point F → Point F
  -- Rules 1 and 2: `O + O = O` and `(x, y) + O = O + (x, y) = (x, y)`.
  | infinity, q => q
  | p, infinity => p
  | affine x1 y1, affine x2 y2 =>
    if x1 = x2 then
      -- Rule 3: `(x, y) + (x, -y) = O`.
      if y2 = -y1 then infinity
      else
        -- Rule 5: `lambda = (3 x1^2 + a) / (2 y1)`; when `a = 0`, the term `a` is skipped.
        --
        -- On the curve, the same `x` gives `y2 = y1` or `y2 = -y1`, so the points are equal here.
        --
        -- Then `y1` differs from `-y1`, so `y1` is nonzero, as rule 5 asks.
        let l := (if (a : F) = 0 then 3 * x1 * x1 else 3 * x1 * x1 + a) * inv (2 * y1)
        -- Rule 5: `x3 = lambda^2 - 2 x1`, written `lambda^2 - x1 - x2` since `x1 = x2`.
        let x3 := l * l - x1 - x2
        -- Rule 5: `y3 = lambda (x1 - x3) - y1`.
        affine x3 (l * (x1 - x3) - y1)
    else
      -- Rule 4: `lambda = (y2 - y1) / (x2 - x1)`.
      let l := (y2 - y1) * inv (x2 - x1)
      -- Rule 4: `x3 = lambda^2 - x1 - x2`.
      let x3 := l * l - x1 - x2
      -- Rule 4: `y3 = lambda (x1 - x3) - y1`.
      affine x3 (l * (x1 - x3) - y1)

instance : Add (Point F) := ⟨add⟩

instance : Neg (Point F) := ⟨neg⟩

end Affine

section Jacobian

/-- The Jacobian form of a point: `(x, y, 1)`, or `(1, 1, 0)` at infinity. -/
def toCoords {F : Type} [OfNat F 0] [OfNat F 1] : Point F → Jacobian.Coords F
  | infinity => .infinity
  | affine x y => ⟨x, y, 1⟩

variable {m : Nat} [NeZero m]

/-- The Jacobian form of a point over the integers mod `m`. -/
def toJacobian (p : Point (Fin m)) : Jacobian m := Jacobian.ofCoords p.toCoords

/-- The point of Jacobian coordinates in a representation of the field.

It takes the inverse of that representation, and the map that reads an element back. -/
@[specialize] def ofCoords {F G : Type} [OfNat G 0] [OfNat G 1] [Add G] [Sub G] [Mul G]
    [DecidableEq G] (inverse : G → G) (read : G → F) (p : Jacobian.Coords G) : Point F :=
  match p.toAffine inverse with
  | none => infinity
  | some (x, y) => affine (read x) (read y)

/-- The point of a Jacobian form. -/
def ofJacobian (p : Jacobian m) : Point (Fin m) := ofCoords Fin.inverse id p.toCoords

/-- `k P`, for `k < 2^fuel`, by double and add on the bits of `k`, low bit first.

The steps run in Jacobian coordinates, in a representation of the field.

It takes the maps into and out of that representation, its inverse, and the curve's `a` in it.

The representation can be the field itself, with the identity for both maps.

Only the conversion back takes an inverse. -/
@[specialize] def mulBits {F G : Type} [OfNat F 0] [OfNat F 1] [OfNat G 0] [OfNat G 1]
    [Add G] [Sub G] [Mul G] [DecidableEq G] (encode : F → G) (inverse : G → G) (read : G → F)
    (a : G) (fuel k : Nat) (p : Point F) : Point F :=
  ofCoords inverse read (Jacobian.Coords.mulBits a fuel k (p.toCoords.map encode))

end Jacobian

end Point

end EthLib.Cryptography.ShortWeierstrass
