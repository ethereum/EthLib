module

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
  ShortWeierstrass.Point.ofCoords Montgomery.inv Montgomery.toFin
    (chain p' q' (Jacobian.Coords.add aMontgomery p' q') (Word64.rawOfNat k.val)
      (Word64.rawOfNat l.val) 256 0)
where
  /-- `(k / 2^s) P + (l / 2^s) Q`, for `k, l < 2^(s + fuel)`, high bits first.

  `pq` is `P + Q`, and the scalars are four words each.

  It is the shared chain of the simultaneous multiplication, with the same doublings and sums.

  It reads bit `s` of the words instead of halving the scalars.

  Halving a 256-bit integer at each step allocates a big integer, which would dominate the chain. -/
  chain (p q pq : Jacobian.Coords Montgomery) (k l : Word64.Raw) :
      Nat → Nat → Jacobian.Coords Montgomery
    | 0, _ => Jacobian.Coords.infinity
    | fuel + 1, s =>
      let acc := Jacobian.Coords.double aMontgomery (chain p q pq k l fuel (s + 1))
      if k.bit s then
        if l.bit s then Jacobian.Coords.add aMontgomery acc pq
        else Jacobian.Coords.add aMontgomery acc p
      else if l.bit s then Jacobian.Coords.add aMontgomery acc q else acc

end Point

/-- Whether `(r, s)` is a valid signature on the hash integer `e` under the public key `q`.

It is the verifying operation of SEC 1 v2 §4.1.4.

`e` acts mod `n`, like every scalar.

The signature is valid when `R = (e / s) G + (r / s) q` is not `O` and its `x` is `r` mod `n`. -/
def verify (q : Point) (e r s : Nat) : Bool :=
  -- Step 1: if `r` and `s` are not both integers in `[1, n-1]`, output "invalid".
  if hr : 0 < r ∧ r < Fn.modulus then
    if hs : 0 < s ∧ s < Fn.modulus then
      -- Not a step of §4.1.4: steps 1 and 3 of SEC 1 v2 §3.2.2.1, not `O` and on the curve.
      --
      -- Its step 2 holds by the type, and its step 4, `n Q = O`, since `h = 1`.
      if q ≠ .infinity ∧ q.isOnCurve then
        -- Steps 2 and 3 are done by the caller, which passes the integer `e` of the hash.
        --
        -- `e` is taken mod `n` here, which leaves `u1` of step 4 unchanged.
        --
        -- Step 4: `u1 = e s^(-1) mod n` and `u2 = r s^(-1) mod n`.
        let sInv := Fn.inv ⟨s, hs.2⟩
        let u1 := (Fin.ofNat _ e : Fn) * sInv
        let u2 := (⟨r, hr.2⟩ : Fn) * sInv
        -- Step 5: `R = (x_R, y_R) = u1 G + u2 Q_U`, and "invalid" if `R = O`.
        match Point.mulAdd u1 .generator u2 q with
        | .infinity => false
        -- Steps 6 to 8: `v = x_R mod n`, and "valid" exactly when `v = r`.
        | .affine x _ => x.val % Fn.modulus == r
      else false
    else false
  else false

end EthLib.Cryptography.Secp256r1
