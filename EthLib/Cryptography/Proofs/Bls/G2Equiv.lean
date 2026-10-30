module

public import EthLib.Cryptography.Proofs.Bls.G2Validity

/-!
# Proofs: `G2` projective equality and group laws

Distinct Jacobian triples can represent the same point on `E'`.

`projectiveEq` tests Jacobian projective equivalence directly over `Fp2`, leaving structural `BEq G2` untouched.

On `Valid` triples, `projectiveEq` agrees with Mathlib's Jacobian quotient and equality in `curve.toAffine.Point`.

Associativity, commutativity, and right-inverse laws of `G2.add` follow immediately up to `projectiveEq`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.G2

open WeierstrassCurve.Jacobian

/-- Cross-multiplied Jacobian equivalence test, defined separately so structural `BEq G2` stays untouched. -/
def projectiveEq (p q : G2) : Bool :=
  if p.z.isZero then q.z.isZero
  else if q.z.isZero then false
  else
    p.x * (q.z * q.z) == q.x * (p.z * p.z) &&
    p.y * ((q.z * q.z) * q.z) == q.y * ((p.z * p.z) * p.z)

theorem toPoint_eq_iff_rep_equiv {p q : G2} (hp : Valid p) (hq : Valid q) :
    toPoint p = toPoint q ↔ rep p ≈ rep q := by
  constructor
  · intro h
    -- `toAffineAddEquiv` is an equivalence on nonsingular Jacobian quotient points.
    have he : ({ point := ⟦rep p⟧, nonsingular := hp } : curve.Point) =
        ({ point := ⟦rep q⟧, nonsingular := hq } : curve.Point) :=
      (Point.toAffineAddEquiv curve).injective h
    exact Quotient.eq.mp (congrArg Point.point he)
  · exact Point.toAffine_of_equiv

theorem projectiveEq_eq_true_iff_rep_equiv {p q : G2} (hp : Valid p) (hq : Valid q) :
    projectiveEq p q = true ↔ rep p ≈ rep q := by
  unfold projectiveEq
  by_cases hpz : p.z.isZero = true
  -- First point at infinity: equivalence holds if and only if the second also has `z = 0`.
  · rw [ite_eq_left hpz]
    constructor
    · intro hqz
      exact equiv_of_Z_eq_zero hp hq (Fp2.isZero_iff.mp hpz) (Fp2.isZero_iff.mp hqz)
    · intro he
      exact Fp2.isZero_iff.mpr ((Z_eq_zero_of_equiv he).mp (Fp2.isZero_iff.mp hpz))
  · rw [ite_eq_right hpz]
    by_cases hqz : q.z.isZero = true
    -- Finite first point and infinite second point are never equivalent.
    · rw [ite_eq_left hqz]
      exact iff_of_false Bool.false_ne_true
        (not_equiv_of_Z_eq_zero_right (fun h => hpz (Fp2.isZero_iff.mpr h))
          (Fp2.isZero_iff.mp hqz))
    -- Both points finite: cross-multiplied X and Y equations characterize Jacobian equivalence.
    · rw [ite_eq_right hqz, Bool.and_eq_true, _root_.beq_iff_eq, _root_.beq_iff_eq]
      constructor
      · rintro ⟨hx, hy⟩
        apply equiv_of_X_eq_of_Y_eq (fun h => hpz (Fp2.isZero_iff.mpr h))
          (fun h => hqz (Fp2.isZero_iff.mpr h))
        · change p.x * q.z ^ 2 = q.x * p.z ^ 2
          linear_combination hx
        · change p.y * q.z ^ 3 = q.y * p.z ^ 3
          linear_combination hy
      · intro he
        constructor
        · have hx := X_eq_of_equiv he
          change p.x * q.z ^ 2 = q.x * p.z ^ 2 at hx
          linear_combination hx
        · have hy := Y_eq_of_equiv he
          change p.y * q.z ^ 3 = q.y * p.z ^ 3 at hy
          linear_combination hy

/-- Bridge allowing group-law proofs in `curve.toAffine.Point` to discharge `projectiveEq` goals on `G2`. -/
theorem projectiveEq_eq_true_iff_toPoint_eq {p q : G2} (hp : Valid p) (hq : Valid q) :
    projectiveEq p q = true ↔ toPoint p = toPoint q :=
  (projectiveEq_eq_true_iff_rep_equiv hp hq).trans (toPoint_eq_iff_rep_equiv hp hq).symm

theorem toPoint_add_assoc {p q r : G2} (hp : Valid p) (hq : Valid q) (hr : Valid r) :
    toPoint (add (add p q) r) = toPoint (add p (add q r)) := by
  simp only [toPoint_add hp hq, toPoint_add hq hr,
    toPoint_add (valid_add hp hq) hr, toPoint_add hp (valid_add hq hr)]
  exact add_assoc _ _ _

theorem toPoint_add_comm {p q : G2} (hp : Valid p) (hq : Valid q) :
    toPoint (add p q) = toPoint (add q p) := by
  rw [toPoint_add hp hq, toPoint_add hq hp, add_comm]

theorem toPoint_add_neg {p : G2} (hp : Valid p) :
    toPoint (add p (neg p)) = toPoint zero := by
  rw [toPoint_add hp (valid_neg hp), toPoint_neg hp, toPoint_zero, add_neg_cancel]

theorem add_assoc_projectiveEq {p q r : G2} (hp : Valid p) (hq : Valid q) (hr : Valid r) :
    projectiveEq (add (add p q) r) (add p (add q r)) = true :=
  (projectiveEq_eq_true_iff_toPoint_eq (valid_add (valid_add hp hq) hr)
    (valid_add hp (valid_add hq hr))).mpr (toPoint_add_assoc hp hq hr)

theorem add_comm_projectiveEq {p q : G2} (hp : Valid p) (hq : Valid q) :
    projectiveEq (add p q) (add q p) = true :=
  (projectiveEq_eq_true_iff_toPoint_eq (valid_add hp hq) (valid_add hq hp)).mpr
    (toPoint_add_comm hp hq)

theorem add_neg_projectiveEq_zero {p : G2} (hp : Valid p) :
    projectiveEq (add p (neg p)) zero = true :=
  (projectiveEq_eq_true_iff_toPoint_eq (valid_add hp (valid_neg hp)) valid_zero).mpr
    (toPoint_add_neg hp)

end EthLib.Cryptography.Bls.G2
