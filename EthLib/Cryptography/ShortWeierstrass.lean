module

public import EthLib.Cryptography.Jacobian

/-!
# Short Weierstrass curves

The curve `E: y^2 = x^3 + a x + b` over a prime field, written once for every such curve.

A point is the point at infinity `O`, or a pair `(x, y)` that satisfies the equation.

The points form a group under the addition rule of SEC 1 v2 §2.2.1.

`O` is its zero, and `-(x, y) = (x, -y)`.

The rule is written in affine coordinates, as SEC 1 prints it.

Scalar multiplication runs in Jacobian coordinates instead, with one inverse at the end.

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

/-- The sum of two points, by the addition rule of SEC 1 v2 §2.2.1.

- Rules 1 and 2: `O + P = P + O = P`.
- Rule 3: `(x, y) + (x, -y) = O`.
- Rule 4, for `x1 != x2`: the chord's slope `l = (y2 - y1) / (x2 - x1)`.
- Rule 5, for `P + P` with `y1 != 0`: the tangent's slope `l = (3 x1^2 + a) / (2 y1)`.

Rules 4 and 5 then give `x3 = l^2 - x1 - x2` and `y3 = l (x1 - x3) - y1`.

Rule 5 writes `x3 = l^2 - 2 x1`, which is `l^2 - x1 - x2` when `x1 = x2`. -/
@[specialize] def add : Point F → Point F → Point F
  | infinity, q => q
  | p, infinity => p
  | affine x1 y1, affine x2 y2 =>
    if x1 = x2 then
      -- The same x: two points of the curve are then equal, or opposite.
      if y2 = -y1 then infinity
      else
        -- Doubling, with the tangent's slope; when `a = 0`, the term `a` is skipped.
        let l := (if (a : F) = 0 then 3 * x1 * x1 else 3 * x1 * x1 + a) * inv (2 * y1)
        let x3 := l * l - x1 - x2
        affine x3 (l * (x1 - x3) - y1)
    else
      -- Two different x: the chord's slope.
      let l := (y2 - y1) * inv (x2 - x1)
      let x3 := l * l - x1 - x2
      affine x3 (l * (x1 - x3) - y1)

instance : Add (Point F) := ⟨add⟩

instance : Neg (Point F) := ⟨neg⟩

end Affine

section Jacobian

variable {m : Nat} [NeZero m]

/-- The Jacobian form of a point. -/
def toJacobian : Point (Fin m) → Jacobian m
  | infinity => .infinity
  | affine x y => .ofAffine x y

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

Only the conversion back takes an inverse. -/
@[specialize] def mulBits {G : Type} [OfNat G 0] [OfNat G 1] [Add G] [Sub G] [Mul G]
    [DecidableEq G] (encode : Fin m → G) (inverse : G → G) (read : G → Fin m) (a : G)
    (fuel k : Nat) (p : Point (Fin m)) : Point (Fin m) :=
  ofCoords inverse read (Jacobian.Coords.mulBits a fuel k ((toJacobian p).toCoords.map encode))

end Jacobian

end Point

end EthLib.Cryptography.ShortWeierstrass
