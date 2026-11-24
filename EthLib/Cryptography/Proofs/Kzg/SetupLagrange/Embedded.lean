module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.DecodeLagrange0
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.DecodeLagrange1
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.DecodeLagrange2
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.DecodeLagrange3
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.DecodeMonomial0
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.DecodeMonomial1
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.DecodeMonomial2
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.DecodeMonomial3
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA00
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA01
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA02
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA03
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA04
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA05
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA06
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA07
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA08
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA09
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA10
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA11
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA12
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA13
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA14
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundA15
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB00
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB01
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB02
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB03
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB04
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB05
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB06
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB07
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB08
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB09
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB10
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB11
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB12
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB13
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB14
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundB15
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC00
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC01
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC02
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC03
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC04
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC05
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC06
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC07
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC08
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC09
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC10
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC11
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC12
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC13
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC14
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Checks.RoundC15

/-!
# Proofs: the Lagrange points of the embedded setup come from its monomial points

The embedded setup holds 4096 monomial points and 4096 Lagrange points of `G1`.

The kernel checks that the Lagrange points are the inverse transform of the monomial points.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (G1 G2 Fr)
open EthLib.Cryptography.Kzg.Constants
open SetupLagrange

/-- If the embedded setup decodes, each Lagrange point is a sum of the monomial points.

The factors are the coefficients of its basis polynomial. -/
theorem TrustedSetup.ofHex_lagrangeOfMonomial {s : TrustedSetup}
    (h : TrustedSetup.ofHex = .ok s) : s.LagrangeOfMonomial :=
  -- The checks test that each string encodes its table point.
  --
  -- They run 768 transforms of size 16.
  lagrangeOfMonomial_of_checks (tM := tableM) (tA := tableA) (tB := tableB)
    (tL := tableL) h (checks_of% decodeM 256) (checks_of% decodeL 256)
    (checks_of% checkA 16 16) (checks_of% checkB 16 16) (checks_of% checkC 16 16)

/-- If the embedded setup decodes, it is well formed at each `τ` that its monomial points fit.

The condition on `τ` is that the monomial points represent its powers. -/
theorem TrustedSetup.ofHex_wellFormed {s : TrustedSetup} {τ : Fr}
    (h : TrustedSetup.ofHex = .ok s)
    (hg1 : ∀ i : Fin FIELD_ELEMENTS_PER_BLOB, G1.Represents s.g1Monomial[i] (τ ^ i.val))
    (hg2 : ∀ i : Fin KZG_SETUP_G2_LENGTH, G2.Represents s.g2Monomial[i] (τ ^ i.val)) :
    s.WellFormed τ :=
  TrustedSetup.WellFormed.of_lagrangeOfMonomial (TrustedSetup.ofHex_valid h)
    (TrustedSetup.ofHex_lagrangeOfMonomial h) hg1 hg2

end EthLib.Cryptography.Kzg
