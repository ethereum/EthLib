module

public import EthLib.Cryptography.Bls.Fp2
public import EthLib.Cryptography.Bls.G1

/-!
# `G2`

The twisted curve `E' : y^2 = x^3 + 4 (1 + i)` over `Fp2`.

It has the shape of `G1`, with coordinates in `Fp2` and the constant `4 (1 + i)` instead of `4`.

The formulas of `G1` read only the field operations and never the constant of the curve.

So a point of `G2` is a point of `G1` over `Fp2`, and the two groups share one implementation.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

/-- A G2 point in Jacobian projective coordinates over `Fp2`.

`z = 0` is the point at infinity.

The base field is `Fp` unless stated. -/
abbrev G2 (F : Type := Fp) : Type := G1 (Fp2 F)

namespace G2

-- The operations of `G1` that are written with their namespace keep their names under `G2`.
--
-- The ones read with field notation are left out, since an alias would hide the one of `G1`.
export G1 (zero neg add mul)

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
  ⟨Fp2.ofNats generatorX0 generatorX1, Fp2.ofNats generatorY0 generatorY1, Fp2.one⟩

/-- The constant `b' = 4·(1 + i)` defining the G2 curve. -/
def bTwist : Fp2 F := Fp2.ofNats 4 4

/-! ## The endomorphism `psi`

The map `psi` untwists a point to `E(Fp12)`, applies the Frobenius map `x ↦ x^p`, and twists back.

It is an endomorphism of the twist.

On the points of order `r` it acts as `[t]`, for the BLS parameter `t`.

The source is RFC 9380, Appendix G.3.
<https://www.rfc-editor.org/rfc/rfc9380#appendix-G.3>
-/

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
    let qx := c1Psi * x.conjugate
    let qy := c2Psi * y.conjugate
    ⟨qx, qy, Fp2.one⟩

end G2

end EthLib.Cryptography.Bls
