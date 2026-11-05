module

public import EthLib.Cryptography.Proofs.Bls.Isogeny

/-!
# Proofs: the hash to G2 returns a valid point

Source: RFC 9380 §8.8.2 and Appendix G.3.

The endomorphisms and the cofactor clearing keep a point on the twist.

So the hash to G2 succeeds on every input and returns a nonsingular point.

Subgroup membership is proved elsewhere.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.HashToCurve

open EthLib.Cryptography.Bls


-- Definitionally equal to `c1Psi`, `c2Psi`, `c1Psi2`, checked via `change` in `psi_valid` and `psi2_valid`.
private def cp1 : Fp2 := (Fp2.powNat ⟨Fp.one, Fp.one⟩ ((Fp.modulus - 1) / 3)).inverse
private def cp2 : Fp2 := (Fp2.powNat ⟨Fp.one, Fp.one⟩ ((Fp.modulus - 1) / 2)).inverse
private def cp12 : Fp2 := ⟨(Fp.powNat (Fp.ofNat 2) ((Fp.modulus - 1) / 3)).inverse, Fp.zero⟩

private theorem cp12_cube : cp12 ^ 3 = 1 := by decide +kernel
private theorem cp1_cube : cp1 ^ 3 = cp2 ^ 2 := by decide +kernel
private theorem cp2_twist : cp2 ^ 2 * G2.bTwist.conjugate = G2.bTwist := by decide +kernel

private theorem toAffine_equation {P : G2} (hP : G2.Valid P)
    (hz : P.z.isZero = false) :
    P.toAffine.2 * P.toAffine.2 = P.toAffine.1 * P.toAffine.1 * P.toAffine.1 + G2.bTwist := by
  have heq := G2.valid_equation hP
  simp only [G2.rep_x, G2.rep_y, G2.rep_z] at heq
  have hn : P.z ≠ 0 := by
    intro h
    have := Fp2.isZero_iff.mpr h
    rw [hz] at this
    cases this
  unfold G2.toAffine
  rw [hz]
  dsimp only
  change (P.y * (P.z⁻¹ * P.z⁻¹ * P.z⁻¹)) * (P.y * (P.z⁻¹ * P.z⁻¹ * P.z⁻¹)) =
    (P.x * (P.z⁻¹ * P.z⁻¹)) * (P.x * (P.z⁻¹ * P.z⁻¹)) * (P.x * (P.z⁻¹ * P.z⁻¹)) + G2.bTwist
  field_simp
  linear_combination heq

/-- `psi` preserves `G2.Valid` (`RFC 9380 Appendix G.3`). -/
theorem psi_valid {P : G2} (hP : G2.Valid P) : G2.Valid (psi P) := by
  unfold psi
  by_cases hz : P.z.isZero = true
  · simpa [hz] using hP
  · have hz' : P.z.isZero = false := Bool.eq_false_iff.mpr hz
    rw [hz']
    dsimp only
    change G2.Valid ⟨cp1 * P.toAffine.1.conjugate, cp2 * P.toAffine.2.conjugate, Fp2.one⟩
    apply G2.valid_of_affine_equation
    have heq := congrArg Fp2.conjugate (toAffine_equation hP hz')
    simp only [Fp2.conjugate_mul, Fp2.conjugate_add] at heq
    have hc := cp1_cube
    have hb := cp2_twist
    linear_combination cp2 ^ 2 * heq - P.toAffine.1.conjugate ^ 3 * hc + hb

/-- `psi2` preserves `G2.Valid` (`RFC 9380 Appendix G.3`). -/
theorem psi2_valid {P : G2} (hP : G2.Valid P) : G2.Valid (psi2 P) := by
  unfold psi2
  by_cases hz : P.z.isZero = true
  · simpa [hz] using hP
  · have hz' : P.z.isZero = false := Bool.eq_false_iff.mpr hz
    rw [hz']
    dsimp only
    change G2.Valid ⟨cp12 * P.toAffine.1, -P.toAffine.2, Fp2.one⟩
    apply G2.valid_of_affine_equation
    have heq := toAffine_equation hP hz'
    linear_combination heq - P.toAffine.1 ^ 3 * cp12_cube

/-- Multiplication by the negative BLS parameter preserves `G2.Valid`. -/
theorem mulNegX_valid {P : G2} (hP : G2.Valid P) : G2.Valid (mulNegX P) :=
  G2.valid_neg (G2.valid_mulNat hP blsAbsX)

/-- `clearCofactor` preserves `G2.Valid` (`RFC 9380 Appendix G.3`). -/
theorem clearCofactor_valid {P : G2} (hP : G2.Valid P) : G2.Valid (clearCofactor P) := by
  unfold clearCofactor
  apply G2.valid_add
  · apply G2.valid_add
    · apply G2.valid_add
      · exact G2.valid_add (psi2_valid (G2.valid_double hP)) (G2.valid_neg (psi_valid hP))
      · exact mulNegX_valid (G2.valid_add (mulNegX_valid hP) (psi_valid hP))
    · exact G2.valid_neg (mulNegX_valid hP)
  · exact G2.valid_neg hP

/-! ## Twist endomorphism identities at infinity and negation -/

/-- `psi` fixes the point at infinity. -/
@[simp]
theorem psi_zero : psi G2.zero = G2.zero := by
  unfold psi
  have hz : (G2.zero : G2).z.isZero = true := by decide
  simp [hz]

/-- `psi2` fixes the point at infinity. -/
@[simp]
theorem psi2_zero : psi2 G2.zero = G2.zero := by
  unfold psi2
  have hz : (G2.zero : G2).z.isZero = true := by decide
  simp [hz]

/-- On finite points, `psi2` negates the affine `y` coordinate. -/
theorem psi2_neg_y (P : G2) (hp : P.z.isZero = false) :
    (psi2 P).y = -(P.toAffine).2 := by
  unfold psi2
  simp [hp]

/-- `psi2` commutes with curve negation. -/
theorem psi2_neg (P : G2) : psi2 (G2.neg P) = G2.neg (psi2 P) := by
  unfold psi2 G2.toAffine G2.neg
  dsimp only
  by_cases hp : P.z.isZero = true
  · simp [hp]
  · simp [hp, neg_mul]

/-- Every successful `hashToG2` output is a nonsingular point on the BLS12-381 twist. -/
theorem hashToG2_valid {msg dst : ByteArray} {P : G2}
    (h : hashToG2 msg dst = .ok P) : G2.Valid P := by
  unfold hashToG2 at h
  cases hf : hashToFieldFp2 msg dst 2 with
  | error e => simp [hf, bind, Except.bind] at h
  | ok us =>
    cases h0 : simpleSwu us[0]! with
    | error e => simp [hf, h0, bind, Except.bind] at h
    | ok p0 =>
      cases h1 : simpleSwu us[1]! with
      | error e => simp [hf, h0, h1, bind, Except.bind] at h
      | ok p1 =>
        simp [hf, h0, h1, bind, Except.bind, pure, Except.pure] at h
        subst P
        exact clearCofactor_valid (G2.valid_add
          (simpleSwu_isoMapG2_valid h0) (simpleSwu_isoMapG2_valid h1))

private theorem expandMessageXmd_256_ok (msg dst : ByteArray) :
    ∃ uniform, expandMessageXmd msg dst 256 = .ok uniform := by
  unfold expandMessageXmd
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [ite_eq_right (by decide), ite_eq_right (by decide),
    Std.Legacy.Range.forIn_eq_forIn_range']
  exact ⟨_, rfl⟩

private theorem hashToFieldFp2_two_ok (msg dst : ByteArray) :
    ∃ us, hashToFieldFp2 msg dst 2 = .ok us := by
  obtain ⟨uniform, hunif⟩ := expandMessageXmd_256_ok msg dst
  unfold hashToFieldFp2
  dsimp only
  rw [hunif]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact ⟨_, rfl⟩

/-- `hashToG2 msg dst` succeeds for all `msg` and `dst` and returns a `G2.Valid` point. -/
theorem hashToG2_total (msg dst : ByteArray) :
    ∃ P : G2, hashToG2 msg dst = .ok P ∧ G2.Valid P := by
  obtain ⟨us, hus⟩ := hashToFieldFp2_two_ok msg dst
  obtain ⟨p0, h0⟩ := simpleSwu_ok us[0]!
  obtain ⟨p1, h1⟩ := simpleSwu_ok us[1]!
  have hok : ∃ P : G2, hashToG2 msg dst = .ok P := by
    unfold hashToG2
    rw [hus]
    dsimp only [bind, Except.bind]
    rw [h0]
    dsimp only
    rw [h1]
    exact ⟨_, rfl⟩
  rcases hok with ⟨P, hP⟩
  exact ⟨P, hP, hashToG2_valid hP⟩

end EthLib.Cryptography.Bls.HashToCurve
