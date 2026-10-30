module

public import EthLib.Cryptography.Proofs.Bls.TwistFrobenius
public import EthLib.Cryptography.Proofs.Bls.G2Subgroup

/-!
# Proofs: Algebra and endomorphism polynomial of `clearCofactor`

Source: `RFC 9380 Appendix G.3`.

- Applying `psi` twice gives `psi2`.
- Applying `psi2` three times negates a point.
- `clearCofactor` is a group homomorphism on the twist, since `psi` is one.
- `clearCofactor` keeps a point of order `r` in the subgroup of order `r`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.HashToCurve

open EthLib.Cryptography.Bls

private def c1 : Fp2 := (Fp2.powNat ⟨Fp.one, Fp.one⟩ ((Fp.modulus - 1) / 3)).inverse
private def c2 : Fp2 := (Fp2.powNat ⟨Fp.one, Fp.one⟩ ((Fp.modulus - 1) / 2)).inverse
private def c12 : Fp2 := ⟨(Fp.powNat (Fp.ofNat 2) ((Fp.modulus - 1) / 3)).inverse, Fp.zero⟩

private theorem c1_norm : c1 * c1.conjugate = c12 := by decide +kernel
private theorem c2_norm : c2 * c2.conjugate = -1 := by decide +kernel
private theorem c12_cube : c12 ^ 3 = 1 := by decide +kernel

private theorem toAffine_one (x y : Fp2) :
    G2.toAffine ⟨x, y, Fp2.one⟩ = (x, y) := by
  unfold G2.toAffine
  have hz : Fp2.one.isZero = false := by decide
  have hi : Fp2.one.inverse = (1 : Fp2) := inv_one
  simp only [hz, Bool.false_eq_true, ↓reduceIte, hi, mul_one]

private theorem psi_noninf (P : G2) (hz : P.z.isZero = false) :
    psi P = ⟨c1 * P.toAffine.1.conjugate, c2 * P.toAffine.2.conjugate, Fp2.one⟩ := by
  unfold psi
  rw [hz]
  rfl

private theorem psi2_noninf (P : G2) (hz : P.z.isZero = false) :
    psi2 P = ⟨c12 * P.toAffine.1, -P.toAffine.2, Fp2.one⟩ := by
  unfold psi2
  rw [hz]
  rfl

/-- The optimized `psi2` map equals two applications of `psi` (`RFC 9380 Appendix G.3`). -/
theorem psi_psi_eq_psi2 (P : G2) : psi (psi P) = psi2 P := by
  cases hz : P.z.isZero with
  | true => simp [psi, psi2, hz]
  | false =>
    rw [psi_noninf P hz]
    rw [psi_noninf _ rfl, psi2_noninf P hz, toAffine_one]
    simp only [Fp2.conjugate_mul, Fp2.conjugate_conjugate]
    congr 1
    · rw [← mul_assoc, c1_norm]
    · rw [← mul_assoc, c2_norm, neg_one_mul]

/-- Three applications of `psi2` on a finite representative normalize to affine negation. -/
theorem psi2_cube_noninf (P : G2) (hz : P.z.isZero = false) :
    psi2 (psi2 (psi2 P)) = ⟨P.toAffine.1, -P.toAffine.2, Fp2.one⟩ := by
  rw [psi2_noninf P hz, psi2_noninf _ rfl, psi2_noninf _ rfl]
  simp only [toAffine_one, neg_neg]
  congr 1
  have h := congrArg (fun c : Fp2 => c * P.toAffine.1) c12_cube
  simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using h

private theorem isZero_eq_of_projectiveEq {p q : G2} (h : G2.projectiveEq p q = true) :
    p.z.isZero = q.z.isZero := by
  unfold G2.projectiveEq at h
  by_cases hp : p.z.isZero = true
  · rw [ite_eq_left hp] at h
    exact hp.trans h.symm
  · rw [ite_eq_right hp] at h
    by_cases hq : q.z.isZero = true
    · rw [ite_eq_left hq] at h
      cases h
    · exact (Bool.eq_false_iff.mpr hp).trans (Bool.eq_false_iff.mpr hq).symm

/-- Affine coordinate normalization is invariant under `G2.projectiveEq`. -/
theorem toAffine_eq_of_projectiveEq {p q : G2} (h : G2.projectiveEq p q = true) :
    p.toAffine = q.toAffine := by
  have hi := isZero_eq_of_projectiveEq h
  by_cases hp : p.z.isZero = true
  · have hq : q.z.isZero = true := hi.symm.trans hp
    simp [G2.toAffine, hp, hq]
  · have hq : ¬q.z.isZero = true := fun hq => hp (hi.trans hq)
    have hp0 : p.z ≠ 0 := fun hz => hp (Fp2.isZero_iff.mpr hz)
    have hq0 : q.z ≠ 0 := fun hz => hq (Fp2.isZero_iff.mpr hz)
    unfold G2.projectiveEq at h
    rw [ite_eq_right hp, ite_eq_right hq, Bool.and_eq_true,
      _root_.beq_iff_eq, _root_.beq_iff_eq] at h
    unfold G2.toAffine
    rw [ite_eq_right hp, ite_eq_right hq]
    change (p.x * (p.z⁻¹ * p.z⁻¹), p.y * (p.z⁻¹ * p.z⁻¹ * p.z⁻¹)) =
      (q.x * (q.z⁻¹ * q.z⁻¹), q.y * (q.z⁻¹ * q.z⁻¹ * q.z⁻¹))
    apply Prod.ext
    · field_simp
      linear_combination h.1
    · field_simp
      linear_combination h.2

private theorem projectiveEq_refl (p : G2) : G2.projectiveEq p p = true := by
  unfold G2.projectiveEq
  by_cases hz : p.z.isZero = true <;> simp [hz]

/-- `psi` respects `G2.projectiveEq`, including at infinity. -/
theorem psi_projectiveEq_of_projectiveEq {p q : G2} (h : G2.projectiveEq p q = true) :
    G2.projectiveEq (psi p) (psi q) = true := by
  have hi := isZero_eq_of_projectiveEq h
  by_cases hp : p.z.isZero = true
  · have hq := hi.symm.trans hp
    simpa [psi, hp, hq] using h
  · have hq : ¬q.z.isZero = true := fun hq => hp (hi.trans hq)
    have he : psi p = psi q := by
      simp only [psi, hp, hq, Bool.false_eq_true, ↓reduceIte]
      rw [toAffine_eq_of_projectiveEq h]
    rw [he]
    exact projectiveEq_refl _

/-- On valid representatives `psi` depends only on the elliptic-curve group element. -/
theorem psi_toPoint_eq_of_toPoint_eq {p q : G2} (hp : G2.Valid p) (hq : G2.Valid q)
    (h : G2.toPoint p = G2.toPoint q) :
    G2.toPoint (psi p) = G2.toPoint (psi q) :=
  (G2.projectiveEq_eq_true_iff_toPoint_eq (psi_valid hp) (psi_valid hq)).mp
    (psi_projectiveEq_of_projectiveEq ((G2.projectiveEq_eq_true_iff_toPoint_eq hp hq).mpr h))

private theorem affine_neg {p : G2} (hz : p.z.isZero = false) :
    (G2.neg p).toAffine = (p.toAffine.1, -p.toAffine.2) := by
  simp only [G2.toAffine, G2.neg, hz, Bool.false_eq_true, ↓reduceIte]
  rw [neg_mul]

/-- `psi` commutes with Jacobian negation on all representatives. -/
theorem psi_neg (p : G2) : psi (G2.neg p) = G2.neg (psi p) := by
  by_cases hz : p.z.isZero = true
  · simp [psi, G2.neg, hz]
  · have hf : p.z.isZero = false := Bool.eq_false_iff.mpr hz
    have hnf : (G2.neg p).z.isZero = false := hf
    simp only [psi, hf, hnf, Bool.false_eq_true, ↓reduceIte]
    rw [affine_neg hf]
    change (⟨_, _ * Fp2.conjugate (-p.toAffine.2), _⟩ : G2) = ⟨_, -(_ * _), _⟩
    rw [Fp2.conjugate_neg, mul_neg]
    rfl

/-- On valid points `psi` commutes with group negation. -/
theorem psi_toPoint_neg {p : G2} (hp : G2.Valid p) :
    G2.toPoint (psi (G2.neg p)) = -G2.toPoint (psi p) := by
  rw [psi_neg, G2.toPoint_neg (psi_valid hp)]

/-- `psi2` respects `G2.projectiveEq`, including at infinity. -/
theorem psi2_projectiveEq_of_projectiveEq {p q : G2} (h : G2.projectiveEq p q = true) :
    G2.projectiveEq (psi2 p) (psi2 q) = true := by
  rw [← psi_psi_eq_psi2 p, ← psi_psi_eq_psi2 q]
  exact psi_projectiveEq_of_projectiveEq (psi_projectiveEq_of_projectiveEq h)

/-- On valid representatives `psi2` depends only on the elliptic-curve group element. -/
theorem psi2_toPoint_eq_of_toPoint_eq {p q : G2} (hp : G2.Valid p) (hq : G2.Valid q)
    (h : G2.toPoint p = G2.toPoint q) :
    G2.toPoint (psi2 p) = G2.toPoint (psi2 q) := by
  rw [← psi_psi_eq_psi2 p, ← psi_psi_eq_psi2 q]
  exact psi_toPoint_eq_of_toPoint_eq (psi_valid hp) (psi_valid hq)
    (psi_toPoint_eq_of_toPoint_eq hp hq h)

/-- On valid points `psi2` commutes with group negation. -/
theorem psi2_toPoint_neg {p : G2} (hp : G2.Valid p) :
    G2.toPoint (psi2 (G2.neg p)) = -G2.toPoint (psi2 p) := by
  rw [psi2_neg, G2.toPoint_neg (psi2_valid hp)]

/-- Three applications of `psi2` are projectively equal to `G2.neg P` for every `P`. -/
theorem psi2_cube_projectiveEq_neg (P : G2) :
    G2.projectiveEq (psi2 (psi2 (psi2 P))) (G2.neg P) = true := by
  cases hz : P.z.isZero with
  | true =>
    have hpsi2 : psi2 P = P := by simp [psi2, hz]
    rw [hpsi2, hpsi2, hpsi2]
    unfold G2.projectiveEq
    simp [G2.neg, hz]
  | false =>
    rw [psi2_cube_noninf P hz]
    have hnz : (G2.neg P).z.isZero = false := hz
    have hPz : P.z ≠ 0 := fun h0 => by
      rw [Fp2.isZero_iff.mpr h0] at hz
      cases hz
    have hone_nz : ¬Fp2.one.isZero = true := by decide
    unfold G2.projectiveEq
    dsimp only
    rw [ite_eq_right hone_nz, ite_eq_right (by simp [hnz])]
    dsimp only [G2.neg]
    unfold G2.toAffine
    rw [hz]
    dsimp only
    rw [Bool.and_eq_true, _root_.beq_iff_eq, _root_.beq_iff_eq]
    change P.x * (P.z⁻¹ * P.z⁻¹) * (P.z * P.z) = P.x * (1 * 1) ∧
      -(P.y * (P.z⁻¹ * P.z⁻¹ * P.z⁻¹)) * (P.z * P.z * P.z) = -P.y * (1 * 1 * 1)
    constructor <;> field_simp

/-- On valid twist points, three applications of `psi2` act as group negation. -/
theorem psi2_cube_toPoint {P : G2} (hP : G2.Valid P) :
    G2.toPoint (psi2 (psi2 (psi2 P))) = -G2.toPoint P := by
  have hpeq := psi2_cube_projectiveEq_neg P
  have heq := (G2.projectiveEq_eq_true_iff_toPoint_eq
    (psi2_valid (psi2_valid (psi2_valid hP))) (G2.valid_neg hP)).mp hpeq
  rw [heq, G2.toPoint_neg hP]

/-- Six applications of `psi` are projectively equal to `G2.neg P`. -/
theorem psi_six_projectiveEq_neg (P : G2) :
    G2.projectiveEq (psi (psi (psi (psi (psi (psi P)))))) (G2.neg P) = true := by
  rw [psi_psi_eq_psi2, psi_psi_eq_psi2, psi_psi_eq_psi2]
  exact psi2_cube_projectiveEq_neg P

/-- On valid twist points, six applications of `psi` act as group negation. -/
theorem psi_six_toPoint {P : G2} (hP : G2.Valid P) :
    G2.toPoint (psi (psi (psi (psi (psi (psi P)))))) = -G2.toPoint P := by
  rw [psi_psi_eq_psi2, psi_psi_eq_psi2, psi_psi_eq_psi2]
  exact psi2_cube_toPoint hP

/-- Multiplication by the negative BLS parameter acts as `-[blsAbsX]` in `G2.curve.toAffine.Point`. -/
theorem toPoint_mulNegX {P : G2} (hP : G2.Valid P) :
    G2.toPoint (mulNegX P) = -(blsAbsX • G2.toPoint P) := by
  rw [mulNegX, G2.toPoint_neg (G2.valid_mulNat hP _), G2.toPoint_mulNat hP]

/-- Group expression computed by `clearCofactor` (`RFC 9380 Appendix G.3`) on valid twist points. -/
theorem clearCofactor_group_expression {P : G2} (hP : G2.Valid P) :
    G2.toPoint (clearCofactor P) =
      G2.toPoint (psi2 (G2.double P)) - G2.toPoint (psi P) +
      (blsAbsX * blsAbsX + blsAbsX) • G2.toPoint P -
      blsAbsX • G2.toPoint (psi P) - G2.toPoint P := by
  unfold clearCofactor
  rw [G2.toPoint_add (G2.valid_add (G2.valid_add
    (G2.valid_add (psi2_valid (G2.valid_double hP)) (G2.valid_neg (psi_valid hP)))
    (mulNegX_valid (G2.valid_add (mulNegX_valid hP) (psi_valid hP))))
    (G2.valid_neg (mulNegX_valid hP))) (G2.valid_neg hP)]
  rw [G2.toPoint_add (G2.valid_add
    (G2.valid_add (psi2_valid (G2.valid_double hP)) (G2.valid_neg (psi_valid hP)))
    (mulNegX_valid (G2.valid_add (mulNegX_valid hP) (psi_valid hP))))
    (G2.valid_neg (mulNegX_valid hP))]
  rw [G2.toPoint_add
    (G2.valid_add (psi2_valid (G2.valid_double hP)) (G2.valid_neg (psi_valid hP)))
    (mulNegX_valid (G2.valid_add (mulNegX_valid hP) (psi_valid hP)))]
  rw [G2.toPoint_add (psi2_valid (G2.valid_double hP)) (G2.valid_neg (psi_valid hP)),
    G2.toPoint_neg (psi_valid hP), G2.toPoint_neg (mulNegX_valid hP),
    G2.toPoint_neg hP, toPoint_mulNegX (G2.valid_add (mulNegX_valid hP) (psi_valid hP)),
    G2.toPoint_add (mulNegX_valid hP) (psi_valid hP), toPoint_mulNegX hP]
  module

/-! ## Subgroup preservation on `r`-torsion and the `cofactorHom` endomorphism -/

/-- `psi` preserves `G2.inSubgroup` on valid twist points. -/
theorem psi_inSubgroup {P : G2} (hP : G2.Valid P) (hs : G2.inSubgroup P = true) :
    G2.inSubgroup (psi P) = true := by
  apply (G2.inSubgroup_iff_modulus_smul_eq_zero (psi_valid hP)).mpr
  rw [TwistFrobenius.toPoint_psi hP, ← map_nsmul,
    (G2.inSubgroup_iff_modulus_smul_eq_zero hP).mp hs, map_zero]

/-- `psi2` preserves `G2.inSubgroup` on valid twist points. -/
theorem psi2_inSubgroup {P : G2} (hP : G2.Valid P) (hs : G2.inSubgroup P = true) :
    G2.inSubgroup (psi2 P) = true := by
  rw [← psi_psi_eq_psi2]
  exact psi_inSubgroup (psi_valid hP) (psi_inSubgroup hP hs)

/-- `clearCofactor` preserves `G2.inSubgroup` whenever the input is already in the `r`-subgroup. -/
theorem clearCofactor_inSubgroup_of_inSubgroup {P : G2} (hP : G2.Valid P)
    (hs : G2.inSubgroup P = true) : G2.inSubgroup (clearCofactor P) = true := by
  apply (G2.inSubgroup_iff_modulus_smul_eq_zero (clearCofactor_valid hP)).mpr
  rw [clearCofactor_group_expression hP]
  have h0 := (G2.inSubgroup_iff_modulus_smul_eq_zero hP).mp hs
  have h1 := (G2.inSubgroup_iff_modulus_smul_eq_zero (psi_valid hP)).mp
    (psi_inSubgroup hP hs)
  have hd : G2.inSubgroup (G2.double P) = true := by
    apply (G2.inSubgroup_iff_modulus_smul_eq_zero (G2.valid_double hP)).mpr
    rw [G2.toPoint_double hP, nsmul_add, h0, zero_add]
  have h2 := (G2.inSubgroup_iff_modulus_smul_eq_zero (psi2_valid (G2.valid_double hP))).mp
    (psi2_inSubgroup (G2.valid_double hP) hd)
  simp only [nsmul_sub, nsmul_add, h0, h1, h2]
  rw [smul_comm Fr.modulus (blsAbsX * blsAbsX + blsAbsX),
    smul_comm Fr.modulus blsAbsX, h0, h1]
  simp

/-- The homomorphism `2 * psi^2 + (x - 1) * psi + (x^2 - x - 1)` computed by `clearCofactor`. -/
noncomputable def cofactorHom : G2.curve.toAffine.Point →+ G2.curve.toAffine.Point :=
  TwistFrobenius.hom.comp TwistFrobenius.hom + TwistFrobenius.hom.comp TwistFrobenius.hom -
    TwistFrobenius.hom + (blsAbsX * blsAbsX + blsAbsX) • AddMonoidHom.id _ -
    blsAbsX • TwistFrobenius.hom - AddMonoidHom.id _

/-- `clearCofactor` refines `cofactorHom` on all valid twist points. -/
theorem toPoint_clearCofactor {P : G2} (hP : G2.Valid P) :
    G2.toPoint (clearCofactor P) = cofactorHom (G2.toPoint P) := by
  rw [clearCofactor_group_expression hP, ← psi_psi_eq_psi2,
    TwistFrobenius.toPoint_psi (psi_valid (G2.valid_double hP)),
    TwistFrobenius.toPoint_psi (G2.valid_double hP), G2.toPoint_double hP,
    map_add, map_add, TwistFrobenius.toPoint_psi hP]
  rfl

/-- `clearCofactor` respects `G2.add` on all valid twist representatives. -/
theorem toPoint_clearCofactor_add {P Q : G2} (hP : G2.Valid P) (hQ : G2.Valid Q) :
    G2.toPoint (clearCofactor (G2.add P Q)) =
      G2.toPoint (clearCofactor P) + G2.toPoint (clearCofactor Q) := by
  rw [toPoint_clearCofactor (G2.valid_add hP hQ), G2.toPoint_add hP hQ,
    map_add, toPoint_clearCofactor hP, toPoint_clearCofactor hQ]

/-- `clearCofactor` commutes with `G2.mulNat` on all valid twist points. -/
theorem toPoint_clearCofactor_mulNat {P : G2} (hP : G2.Valid P) (n : Nat) :
    G2.toPoint (clearCofactor (G2.mulNat P n)) = n • G2.toPoint (clearCofactor P) := by
  rw [toPoint_clearCofactor (G2.valid_mulNat hP n), G2.toPoint_mulNat hP,
    map_nsmul, toPoint_clearCofactor hP]

end EthLib.Cryptography.Bls.HashToCurve
