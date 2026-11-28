module

public import EthLib.Cryptography.Proofs.Bls.CofactorCardinality
public import EthLib.Cryptography.Proofs.Bls.HashToCurveMap

/-!
# Proofs: certificate helpers for `G2` torsion witnesses

Each helper turns a kernel computation on points into a fact about the curve group.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.CofactorCertificate

/-- Turns a kernel computation of `[n] * P = 0` into a fact about the curve group. -/
theorem nsmul_zero_cert (P : G2) (hp : G2.Valid P) (n : Nat)
    (hc : (P.mulNat n).isInfinity = true) : n • G2.toPoint P = 0 := by
  rw [← G2.toPoint_mulNat hp]
  exact (G2.isInfinity_eq_true_iff_toPoint_eq_zero (G2.valid_mulNat hp n)).mp hc

/-- Certifies `cofactorHom (toPoint P) = 0` from a kernel check that clearing `P` gives infinity. -/
theorem cofactor_zero_cert (P : G2) (hp : G2.Valid P)
    (hc : (HashToCurve.clearCofactor P).isInfinity = true) :
    HashToCurve.cofactorHom (G2.toPoint P) = 0 := by
  rw [← HashToCurve.toPoint_clearCofactor hp]
  exact (G2.isInfinity_eq_true_iff_toPoint_eq_zero
    (HashToCurve.clearCofactor_valid hp)).mp hc

end EthLib.Cryptography.Bls.CofactorCertificate
