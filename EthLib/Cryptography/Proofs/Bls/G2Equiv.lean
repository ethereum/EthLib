module

public import EthLib.Cryptography.Proofs.Bls.G2Validity

/-!
# Proofs: projective equality on `G2`

Different Jacobian triples can represent the same point of `E'`.

The projective equality of `G2` tests that equivalence over `Fp2`.

On valid triples, it agrees with equality of the points in Mathlib's affine group.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.G2

open WeierstrassCurve.Jacobian

/-- Projective equality on `G2` is reflexive. -/
@[simp] theorem projectiveEq_refl (p : G2) : p.projectiveEq p = true :=
  G1.Law.projectiveEq_refl Fp2.embedding p

/-- On a valid triple, `Z = 0` exactly when the point is `O`.

Singular triples with `Z ≠ 0` also map to `O`, so the hypothesis is needed. -/
theorem isInfinity_eq_true_iff_toPoint_eq_zero {p : G2} (hp : Valid p) :
    p.isInfinity = true ↔ toPoint p = 0 :=
  G1.Law.isInfinity_eq_true_iff_toPoint_eq_zero Fp2.embedding bTwist hp

theorem toPoint_eq_iff_rep_equiv {p q : G2} (hp : Valid p) (hq : Valid q) :
    toPoint p = toPoint q ↔ rep p ≈ rep q :=
  G1.Law.toPoint_eq_iff_rep_equiv Fp2.embedding bTwist hp hq

theorem projectiveEq_eq_true_iff_rep_equiv {p q : G2} (hp : Valid p) (hq : Valid q) :
    p.projectiveEq q = true ↔ rep p ≈ rep q :=
  G1.Law.projectiveEq_eq_true_iff_rep_equiv Fp2.embedding bTwist hp hq

/-- On valid triples, projective equality is equality of the points they denote. -/
theorem projectiveEq_eq_true_iff_toPoint_eq {p q : G2} (hp : Valid p) (hq : Valid q) :
    p.projectiveEq q = true ↔ toPoint p = toPoint q :=
  G1.Law.projectiveEq_eq_true_iff_toPoint_eq Fp2.embedding bTwist hp hq

end EthLib.Cryptography.Bls.G2
