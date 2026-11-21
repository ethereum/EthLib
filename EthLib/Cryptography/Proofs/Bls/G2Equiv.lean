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
@[simp] theorem projectiveEq_refl (p : G2) : projectiveEq p p = true := by
  unfold projectiveEq
  by_cases hz : p.z.isZero = true <;> simp [hz, Fp2.beq_iff_eq]

/-- On a valid triple, `Z = 0` exactly when the point is `O`.

Singular triples with `Z ≠ 0` also map to `O`, so the hypothesis is needed. -/
theorem isInfinity_eq_true_iff_toPoint_eq_zero {p : G2} (hp : Valid p) :
    p.isInfinity = true ↔ toPoint p = 0 := by
  constructor
  · intro h
    exact Point.toAffine_of_Z_eq_zero (Fp2.isZero_iff.mp h)
  · intro h
    -- A finite nonsingular representative maps to `Point.some`, never `0`.
    by_contra hne
    have hz : p.z ≠ 0 := fun hz0 => hne (Fp2.isZero_iff.mpr hz0)
    rw [toPoint, Point.toAffine_of_Z_ne_zero hp hz] at h
    cases h

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
    · rw [ite_eq_right hqz, Bool.and_eq_true, Fp2.beq_iff_eq, Fp2.beq_iff_eq]
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

/-- On valid triples, projective equality is equality of the points they denote. -/
theorem projectiveEq_eq_true_iff_toPoint_eq {p q : G2} (hp : Valid p) (hq : Valid q) :
    projectiveEq p q = true ↔ toPoint p = toPoint q :=
  (projectiveEq_eq_true_iff_rep_equiv hp hq).trans (toPoint_eq_iff_rep_equiv hp hq).symm

end EthLib.Cryptography.Bls.G2
