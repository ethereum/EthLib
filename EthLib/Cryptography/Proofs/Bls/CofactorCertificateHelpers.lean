module

public import EthLib.Cryptography.Proofs.Bls.CofactorCardinality
public import EthLib.Cryptography.Proofs.Bls.HashToCurveMap

/-!
# Proofs: certificate helpers for `G2` torsion witnesses

The kernel cannot unfold well-founded recursion, so these copies recurse on a fuel argument.

Each copy is proved equal to the library function it mirrors.

Each copy also commutes with a map of base fields, so a certificate can run in the model of `Fp`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.CofactorCertificate

/-- Turns a kernel computation of `[n] * P = 0` into a fact about the curve group. -/
theorem nsmul_zero_cert (P : G2) (hp : G2.Valid P) (n fuel : Nat)
    (hn : n < 2 ^ fuel) (hc : (G2.mulNatAux fuel P n).isInfinity = true) :
    n • G2.toPoint P = 0 := by
  rw [← G2.toPoint_mulNat hp]
  apply (G2.isInfinity_eq_true_iff_toPoint_eq_zero (G2.valid_mulNat hp n)).mp
  rwa [← G2.mulNatAux_eq fuel P n hn]

section Generic

variable {F : Type} [BaseField F]

/-- Fuel-based equivalent of `HashToCurve.mulNegX` for closed kernel evaluation. -/
def negXAux (P : G2 F) : G2 F := G2.neg (G2.mulNatAux 65 P HashToCurve.blsAbsX)

/-- Fuel-based equivalent of `HashToCurve.clearCofactor` for closed kernel evaluation. -/
def clearAux (P : G2 F) : G2 F :=
  let t1 := negXAux P
  let t2 := HashToCurve.psi P
  let t3 := HashToCurve.psi2 (G2.double P)
  let t3 := G2.add t3 (G2.neg t2)
  let t2 := G2.add t1 t2
  let t2 := negXAux t2
  let t3 := G2.add t3 t2
  let t3 := G2.add t3 (G2.neg t1)
  G2.add t3 (G2.neg P)

/-- A map of base fields commutes with the multiplication by `-x`. -/
theorem map_negXAux {G : Type} [BaseField G] (f : BaseField.Hom F G) (P : G2 F) :
    (negXAux P).map f = negXAux (P.map f) := by
  rw [negXAux, negXAux, G2.map_neg_fn, G2.map_mulNatAux]

/-- A map of base fields commutes with the cofactor clearing. -/
theorem map_clearAux {G : Type} [BaseField G] (f : BaseField.Hom F G) (P : G2 F) :
    (clearAux P).map f = clearAux (P.map f) := by
  simp only [clearAux, G2.map_add_fn, G2.map_neg_fn, map_negXAux, HashToCurve.map_psi,
    HashToCurve.map_psi2, G2.map_double]

end Generic

theorem negXAux_eq (P : G2) : negXAux P = HashToCurve.mulNegX P := by
  rw [negXAux, G2.mulNatAux_eq 65 P _ (by decide)]
  rfl

theorem clearAux_eq (P : G2) : clearAux P = HashToCurve.clearCofactor P := by
  simp only [clearAux, negXAux_eq, HashToCurve.clearCofactor]

/-- Certifies `cofactorHom (toPoint P) = 0` from a closed `(clearAux P).isInfinity = true` check. -/
theorem cofactor_zero_cert (P : G2) (hp : G2.Valid P)
    (hc : (clearAux P).isInfinity = true) :
    HashToCurve.cofactorHom (G2.toPoint P) = 0 := by
  rw [clearAux_eq] at hc
  rw [← HashToCurve.toPoint_clearCofactor hp]
  exact (G2.isInfinity_eq_true_iff_toPoint_eq_zero
    (HashToCurve.clearCofactor_valid hp)).mp hc

end EthLib.Cryptography.Bls.CofactorCertificate
