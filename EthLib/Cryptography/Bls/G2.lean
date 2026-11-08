module

public import EthLib.Cryptography.Bls.Fp2
public import EthLib.Cryptography.Bls.Fr

/-!
# `G2`

The twisted curve `E' : y^2 = x^3 + 4 (1 + i)` over `Fp2`.

It has the shape of `G1`, with coordinates in `Fp2` and the constant `4 (1 + i)` instead of `4`.

The formulas are those of `G1`, with the operations of `Fp2`.

The code is generic in the base field, as for `Fp2`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

/-- A G2 point in Jacobian projective coordinates over `Fp2`.

`z = 0` is the point at infinity.

The base field is `Fp` unless stated. -/
structure G2 (F : Type := Fp) where
  x : Fp2 F
  y : Fp2 F
  z : Fp2 F
deriving Inhabited, BEq, Repr

namespace G2

variable {F : Type} [BaseField F]

/-- The coordinate `x.c0` of the generator of G2, as an integer. -/
def generatorX0 : Nat :=
  0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8

/-- The coordinate `x.c1` of the generator of G2, as an integer. -/
def generatorX1 : Nat :=
  0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e

/-- The coordinate `y.c0` of the generator of G2, as an integer. -/
def generatorY0 : Nat :=
  0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801

/-- The coordinate `y.c1` of the generator of G2, as an integer. -/
def generatorY1 : Nat :=
  0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be

/-- Affine generator of G2, embedded with `z = 1`. -/
def generator : G2 F :=
  let x : Fp2 F := ⟨BaseField.ofNat generatorX0, BaseField.ofNat generatorX1⟩
  let y : Fp2 F := ⟨BaseField.ofNat generatorY0, BaseField.ofNat generatorY1⟩
  ⟨x, y, Fp2.one⟩

/-- The point at infinity. -/
def zero : G2 F := ⟨Fp2.one, Fp2.one, Fp2.zero⟩

@[inline] def isInfinity (p : G2 F) : Bool := p.z.isZero

/-- The constant `b' = 4·(1 + i)` defining the G2 curve. -/
def bTwist : Fp2 F := ⟨BaseField.ofNat 4, BaseField.ofNat 4⟩

/-- Jacobian point doubling for `a = 0` curves. -/
def double (p : G2 F) : G2 F :=
  if p.z.isZero then p else
    let two := Fp2.ofFp (BaseField.ofNat 2)
    let three := Fp2.ofFp (BaseField.ofNat 3)
    let eight := Fp2.ofFp (BaseField.ofNat 8)
    let A := p.x * p.x
    let B := p.y * p.y
    let C := B * B
    let D := two * ((p.x + B) * (p.x + B) - A - C)
    let E := three * A
    let F := E * E
    let x' := F - two * D
    let y' := E * (D - x') - eight * C
    let z' := two * p.y * p.z
    ⟨x', y', z'⟩

@[inline] def neg (p : G2 F) : G2 F := ⟨p.x, -p.y, p.z⟩

/-- Jacobian addition (Bernstein–Lange 2007). -/
def add (p q : G2 F) : G2 F :=
  if p.z.isZero then q else
  if q.z.isZero then p else
    let two := Fp2.ofFp (BaseField.ofNat 2)
    let z1z1 := p.z * p.z
    let z2z2 := q.z * q.z
    let u1   := p.x * z2z2
    let u2   := q.x * z1z1
    let s1   := p.y * q.z * z2z2
    let s2   := q.y * p.z * z1z1
    if u1.beq u2 then
      if s1.beq s2 then double p else zero
    else
      let h := u2 - u1
      let i := (two * h) * (two * h)
      let j := h * i
      let r := two * (s2 - s1)
      let v := u1 * i
      let x' := r * r - j - two * v
      let y' := r * (v - x') - two * s1 * j
      let z' := ((p.z + q.z) * (p.z + q.z) - z1z1 - z2z2) * h
      ⟨x', y', z'⟩

instance : Add (G2 F) := ⟨add⟩
instance : Neg (G2 F) := ⟨neg⟩

/-- Project a Jacobian point to affine `(x, y)`. Undefined at infinity. -/
def toAffine (p : G2 F) : Fp2 F × Fp2 F :=
  if p.z.isZero then (Fp2.zero, Fp2.zero)
  else
    let zinv  := p.z.inverse
    let zinv2 := zinv * zinv
    let zinv3 := zinv2 * zinv
    (p.x * zinv2, p.y * zinv3)

/-- Scalar multiplication via double-and-add. -/
def mulNat (p : G2 F) (k : Nat) : G2 F :=
  if k = 0 then zero
  else
    let half := mulNat (double p) (k / 2)
    if k % 2 = 1 then add p half else half
termination_by k
decreasing_by omega

@[inline] def mul (p : G2 F) (s : Fr) : G2 F := mulNat p s.val

/-- Whether two Jacobian triples denote the same point.

Two finite triples agree when `X1 Z2^2 = X2 Z1^2` and `Y1 Z2^3 = Y2 Z1^3`.

Two triples at infinity agree, and a finite triple never agrees with one at infinity. -/
def projectiveEq (p q : G2 F) : Bool :=
  if p.z.isZero then q.z.isZero
  else if q.z.isZero then false
  else
    (p.x * (q.z * q.z)).beq (q.x * (p.z * p.z)) &&
    (p.y * ((q.z * q.z) * q.z)).beq (q.y * ((p.z * p.z) * p.z))

/-! ## The endomorphism `psi`

The map `psi` untwists a point to `E(Fp12)`, applies the Frobenius map `x ↦ x^p`, and twists back.

It is an endomorphism of the twist.

On the points of order `r` it acts as `[t]`, for the BLS parameter `t`.

The source is RFC 9380, Appendix G.3.
<https://www.rfc-editor.org/rfc/rfc9380#appendix-G.3>
-/

/-- Frobenius for `GF(p^2)` with basis `(1, I)`: `c0 + c1·I ↦ c0 − c1·I`. -/
def frobeniusFp2 (x : Fp2 F) : Fp2 F := ⟨x.c0, -x.c1⟩

/-- `c1_psi = 1 / (1 + I)^((p − 1) / 3)`. -/
def c1Psi : Fp2 F :=
  let oneI : Fp2 F := ⟨BaseField.one, BaseField.one⟩
  (Fp2.powNat oneI ((Fp.modulus - 1) / 3)).inverse

/-- `c2_psi = 1 / (1 + I)^((p − 1) / 2)`. -/
def c2Psi : Fp2 F :=
  let oneI : Fp2 F := ⟨BaseField.one, BaseField.one⟩
  (Fp2.powNat oneI ((Fp.modulus - 1) / 2)).inverse

/-- `psi(x, y) = (c1_psi · frobenius(x), c2_psi · frobenius(y))`, RFC 9380, Appendix G.3. -/
def psi (P : G2 F) : G2 F :=
  if P.z.isZero then P else
    -- Normalise to affine form, then map the coordinates, with `Z = 1`.
    let (x, y) := P.toAffine
    let qx := c1Psi * frobeniusFp2 x
    let qy := c2Psi * frobeniusFp2 y
    ⟨qx, qy, Fp2.one⟩

end G2

end EthLib.Cryptography.Bls
