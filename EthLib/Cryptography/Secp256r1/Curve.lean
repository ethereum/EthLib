module

public import EthLib.Cryptography.Ecdsa.Curve
public import EthLib.Cryptography.Secp256r1.Montgomery
public import EthLib.Cryptography.ShortWeierstrass

/-!
# `Secp256r1.Curve`

The curve `E: y^2 = x^3 + a x + b` over `Fp`, with `a = -3`, from SEC 2 v2 §2.4.2.

NIST calls it P-256, and SP 800-186 §3.2.1.3 standardizes the same parameters.

The cofactor is 1, so every point of the curve but `O` generates the whole group.

Its points and the addition rule of SEC 1 v2 §2.2.1 are those of every short Weierstrass curve.

The two products of verification share one chain in Montgomery form, with one inverse at the end.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256r1

/-- `a = -3`, from SEC 2 v2 §2.4.2. -/
def a : Fp := 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFC

/-- `b`, from SEC 2 v2 §2.4.2. -/
def b : Fp := 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B

/-- P-256 as a short Weierstrass curve, with its `a` and `b`, and the inverse of `Fp`. -/
instance instParams : ShortWeierstrass.Params Fp := ⟨a, b, Fp.inv⟩

/-- A point of the curve, or the point at infinity `O`. -/
abbrev Point := ShortWeierstrass.Point Fp

namespace Point

export ShortWeierstrass.Point (toJacobian ofJacobian)

-- The constructors are restated at this curve's point type.
--
-- Numerals in coordinates are then read in `Fp`, and dot notation finds this curve's operations.

/-- The point at infinity `O`, the zero of the group. -/
@[match_pattern] abbrev infinity : Point := ShortWeierstrass.Point.infinity

/-- The point `(x, y)`. -/
@[match_pattern] abbrev affine (x y : Fp) : Point := ShortWeierstrass.Point.affine x y

/-- The base point `G`, from SEC 2 v2 §2.4.2. -/
def generator : Point :=
  affine 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
    0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5

/-- `k P`, for `k < 2^fuel`, by double and add on the bits of `k`, low bit first.

The steps run in Jacobian coordinates, so only the conversion back takes an inverse. -/
def mulBits (fuel k : Nat) (p : Point) : Point :=
  ShortWeierstrass.Point.mulBits id Fin.inverse id a fuel k p

/-- `k P`, the scalar multiplication of SEC 1 v2 §2.2.1, for a scalar mod `n`.

`n` has 256 bits, so 256 steps cover every scalar. -/
def mul (k : Fn) (p : Point) : Point := mulBits 256 k.val p

/-- `a` in Montgomery form. -/
def aMontgomery : Montgomery := Montgomery.ofFin a

/-- `k P + l Q`, for scalars mod `n`, with one chain of doublings for both.

The chain runs in Jacobian coordinates in Montgomery form, and only the conversion back inverts.

On points of the curve it is the sum of the two products. -/
def mulAdd (k : Fn) (p : Point) (l : Fn) (q : Point) : Point :=
  let p' := (toJacobian p).toCoords.map Montgomery.ofFin
  let q' := (toJacobian q).toCoords.map Montgomery.ofFin
  -- The shared chain reads the bits of each scalar from its four words.
  --
  -- Halving a 256-bit scalar at each step would allocate a big integer, at a dominant cost.
  ShortWeierstrass.Point.ofCoords Montgomery.inv Montgomery.toFin
    (Jacobian.Coords.mulAddBits aMontgomery p' q' (Jacobian.Coords.add aMontgomery p' q')
      (Word64.rawOfNat k.val).bit (Word64.rawOfNat l.val).bit 256 0)

end Point

/-- P-256 as ECDSA uses it: the base point `G`, its products, and the inverse mod `n`. -/
@[inline] def domain : Cryptography.Ecdsa.Curve Fp.modulus Fn.modulus :=
  ⟨Point.generator, Point.mul, Point.mulAdd, Fn.inv⟩

/-- Whether `(r, s)` is a valid signature on the hash integer `e` under the public key `q`.

It is the verifying operation of SEC 1 v2 §4.1.4, that of every curve of cofactor 1.

`e` acts mod `n`, like every scalar.

The signature is valid when `R = (e / s) G + (r / s) q` is not `O` and its `x` is `r` mod `n`. -/
def verify (q : Point) (e r s : Nat) : Bool := domain.verify q e r s

end EthLib.Cryptography.Secp256r1
