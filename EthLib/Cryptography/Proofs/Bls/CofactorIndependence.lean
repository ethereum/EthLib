module

public import EthLib.Cryptography.Proofs.Bls.CofactorPointQ13
public import EthLib.Cryptography.Proofs.Bls.CofactorPointQ23
public import EthLib.Cryptography.Proofs.Bls.CofactorPointIndependent13
public import EthLib.Cryptography.Proofs.Bls.CofactorPointIndependent23

/-!
# Proofs: Independence of the `13`-torsion and `23`-torsion witness pairs on `G2`

The second `13`-torsion point is not a multiple of the first.

The same holds for the two `23`-torsion points.

The kernel checks every multiple `[0..12]` and `[0..22]`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.CofactorCertificate

/-- Turns a kernel check of `Q != [n] * P` into a fact about the curve group. -/
theorem not_nsmul_cert (P Q : G2) (hp : G2.Valid P) (hq : G2.Valid Q)
    (n fuel : Nat) (hn : n < 2 ^ fuel)
    (hc : G2.projectiveEq Q (mulAux fuel P n) = false) :
    G2.toPoint Q ≠ n • G2.toPoint P := by
  intro he
  rw [mulAux_eq fuel P n hn] at hc
  have ht : G2.projectiveEq Q (G2.mulNat P n) = true := by
    apply (G2.projectiveEq_eq_true_iff_toPoint_eq hq (G2.valid_mulNat hp n)).mpr
    simpa only [G2.toPoint_mulNat hp] using he
  rw [hc] at ht
  exact Bool.noConfusion ht

/-- `independent13` is independent of `q13` in `G2.curve.toAffine.Point[13]`. -/
theorem independent13_not_span (i : Fin 13) :
    G2.toPoint independent13 ≠ i.val • G2.toPoint q13 := by
  have hc : ∀ i : Fin 13, G2.projectiveEq independent13 (mulAux 5 q13 i.val) = false := by
    decide +kernel
  exact not_nsmul_cert q13 independent13 q13_valid independent13_valid i.val 5
    (Nat.lt_trans i.isLt (by decide)) (hc i)

/-- `independent23` is independent of `q23` in `G2.curve.toAffine.Point[23]`. -/
theorem independent23_not_span (i : Fin 23) :
    G2.toPoint independent23 ≠ i.val • G2.toPoint q23 := by
  have hc : ∀ i : Fin 23, G2.projectiveEq independent23 (mulAux 6 q23 i.val) = false := by
    decide +kernel
  exact not_nsmul_cert q23 independent23 q23_valid independent23_valid i.val 6
    (Nat.lt_trans i.isLt (by decide)) (hc i)

end EthLib.Cryptography.Bls.CofactorCertificate
