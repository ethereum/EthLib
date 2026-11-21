module

public import EthLib.Cryptography.Secp256k1.Field
public import EthLib.Cryptography.ShortWeierstrass

/-!
# `Secp256r1.Curve`

The curve `E: y^2 = x^3 + a x + b` over `Fp`, with `a = -3`, from SEC 2 v2 §2.4.2.

NIST calls it P-256, and SP 800-186 §3.2.1.3 standardizes the same parameters.

- `Fp` is the base field, integers mod the prime `p`.
- `Fn` is the scalar field, integers mod the prime order `n` of the generator.

The cofactor is 1, so every point of the curve but `O` generates the whole group.

Its points and the addition rule of SEC 1 v2 §2.2.1 are those of every short Weierstrass curve.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256r1

/-- `p`, the modulus of the base field, from SEC 2 v2 §2.4.2. -/
def Fp.modulus : Nat := 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF

/-- `n`, the order of the generator, from SEC 2 v2 §2.4.2. -/
def Fn.modulus : Nat := 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551

-- Named explicitly, since both anonymous instances would get the same name.
instance Fp.instNeZeroModulus : NeZero Fp.modulus := ⟨by decide⟩
instance Fn.instNeZeroModulus : NeZero Fn.modulus := ⟨by decide⟩

/-- An element of the base field. -/
abbrev Fp := Fin Fp.modulus

/-- An element of the scalar field. -/
abbrev Fn := Fin Fn.modulus

/-- The inverse in `Fp`, by the extended Euclidean algorithm, and 0 for 0. -/
def Fp.inv (a : Fp) : Fp := Fin.inverse a

/-- The inverse in `Fn`, by the extended Euclidean algorithm, and 0 for 0. -/
def Fn.inv (a : Fn) : Fn := Fin.inverse a

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

/-- `k P + l Q`, for scalars mod `n`, with one chain of doublings for both.

On points of the curve it is the sum of the two products. -/
def mulAdd (k : Fn) (p : Point) (l : Fn) (q : Point) : Point :=
  ofJacobian (Jacobian.mulAdd a 256 k.val (toJacobian p) l.val (toJacobian q))

end Point

/-- Whether `(r, s)` is a valid signature on the hash integer `e` under the public key `q`.

It is the verifying operation of SEC 1 v2 §4.1.4.

`e` acts mod `n`, like every scalar.

The signature is valid when `R = (e / s) G + (r / s) q` is not `O` and its `x` is `r` mod `n`. -/
def verify (q : Point) (e r s : Nat) : Bool :=
  -- Step 1: `r` and `s` lie in `[1, n - 1]`, and the key is valid.
  if hr : 0 < r ∧ r < Fn.modulus then
    if hs : 0 < s ∧ s < Fn.modulus then
      if q ≠ .infinity ∧ q.isOnCurve then
        let sInv := Fn.inv ⟨s, hs.2⟩
        let u1 := (Fin.ofNat _ e : Fn) * sInv
        let u2 := (⟨r, hr.2⟩ : Fn) * sInv
        -- Steps 5 to 8: `R = u1 G + u2 q` must not be `O`, and `x_R mod n` must be `r`.
        match Point.mulAdd u1 .generator u2 q with
        | .infinity => false
        | .affine x _ => x.val % Fn.modulus == r
      else false
    else false
  else false

end EthLib.Cryptography.Secp256r1
