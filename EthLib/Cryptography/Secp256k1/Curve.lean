module

public import EthLib.Cryptography.Secp256k1.Inverse
public import EthLib.Cryptography.ShortWeierstrass

/-!
# `Secp256k1.Curve`

The curve `E: y^2 = x^3 + 7` over `Fp`, from SEC 2 v2 §2.4.1, where `a = 0` and `b = 7`.

Its points and the addition rule of SEC 1 v2 §2.2.1 are those of every short Weierstrass curve.

Scalar multiplication runs in Jacobian coordinates in Montgomery form, with one inverse at the end.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

/-- `b`, the constant term of the curve equation, from SEC 2 v2 §2.4.1. -/
def b : Fp := 7

/-- secp256k1 as a short Weierstrass curve, with `a = 0`, its `b`, and the inverse of `Fp`. -/
instance instParams : ShortWeierstrass.Params Fp := ⟨0, b, Fp.inv⟩

/-- A point of the curve: the point at infinity, or a pair of coordinates.

A pair is a point of the curve only when it satisfies the equation. -/
abbrev Point := ShortWeierstrass.Point Fp

namespace Point

export ShortWeierstrass.Point (toJacobian ofCoords ofJacobian)

-- The constructors and the negation are restated at this curve's point type.
--
-- Numerals in coordinates are then read in `Fp`, and dot notation finds this curve's operations.

/-- The point at infinity `O`, the zero of the group. -/
@[match_pattern] abbrev infinity : Point := ShortWeierstrass.Point.infinity

/-- The point `(x, y)`. -/
@[match_pattern] abbrev affine (x y : Fp) : Point := ShortWeierstrass.Point.affine x y

/-- The negative of a point: `-(x, y) = (x, -y)`. -/
abbrev neg (p : Point) : Point := ShortWeierstrass.Point.neg p

/-- The base point `G`, from SEC 2 v2 §2.4.1. -/
def generator : Point :=
  affine 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
    0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

/-- The Jacobian form of a point, in Montgomery form. -/
def toMontgomeryCoords (p : Point) : Jacobian.Coords Fp.Montgomery :=
  (toJacobian p).toCoords.map Montgomery.ofFin

/-- The point of a Jacobian form in Montgomery form. -/
def ofMontgomeryCoords (p : Jacobian.Coords Fp.Montgomery) : Point :=
  ofCoords Montgomery.inv Montgomery.toFin p

/-- `k P`, for `k < 2^fuel`, by double and add on the bits of `k`, low bit first.

The steps run in Jacobian coordinates in Montgomery form.

Only the conversion back takes an inverse. -/
def mulBits (fuel k : Nat) (p : Point) : Point :=
  ShortWeierstrass.Point.mulBits Montgomery.ofFin Montgomery.inv Montgomery.toFin 0 fuel k p

/-- `k P`, the scalar multiplication of SEC 1 v2 §2.2.1, for a scalar mod `n`.

`n` has 256 bits, so 256 steps cover every scalar. -/
def mul (k : Fn) (p : Point) : Point := mulBits 256 k.val p

end Point

end EthLib.Cryptography.Secp256k1
