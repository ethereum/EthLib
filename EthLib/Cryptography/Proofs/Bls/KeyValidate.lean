module

public import EthLib.Cryptography.Bls.Signatures
public import EthLib.Cryptography.Proofs.Bls.G1SubgroupSpan
public import EthLib.Cryptography.Proofs.Bls.G2SubgroupSpan
public import EthLib.Cryptography.Proofs.Bls.G2Compress
public import EthLib.Cryptography.Proofs.Bls.PairingLaws

/-!
# Proofs: key validation and the subgroup checks

Key validation accepts exactly the encodings of the nonzero points of order `r` in `G1`.

The subgroup checks accept exactly the valid points that represent a multiple of the generator.

The source is [draft-04][draft-04], §2.5 and §2.7.

[draft-04]: https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

namespace G1

/-- A multiple of the generator lies in the subgroup of order `r`. -/
theorem modulus_smul_toPoint_mul_generator (a : Fr) :
    Fr.modulus • toPoint (mul generator a) = 0 := by
  rw [toPoint_mul valid_generator, smul_comm, modulus_smul_generator, nsmul_zero]

/-- The subgroup check accepts exactly the valid points that represent a multiple of `g1`. -/
theorem inSubgroup_iff_exists_represents {P : G1} (hP : Valid P) :
    inSubgroup P = true ↔ ∃ a, Represents P a := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := exists_mul_generator_of_inSubgroup hP h
    exact ⟨a, hP, ha⟩
  · rintro ⟨a, -, ha⟩
    rw [inSubgroup_iff_modulus_smul_eq_zero hP, ha]
    exact modulus_smul_toPoint_mul_generator a

/-- Key validation accepts exactly the decodable points that are nonzero and of order `r`. -/
theorem keyValidatePoint_eq_ok_iff {bytes : ByteArray} {P : G1} :
    keyValidatePoint bytes = .ok P ↔
      uncompress bytes = .ok P ∧ Valid P ∧ toPoint P ≠ 0 ∧ Fr.modulus • toPoint P = 0 := by
  unfold keyValidatePoint
  cases hunc : uncompress bytes with
  | error e =>
    simp only [Bind.bind, Except.bind]
    exact iff_of_false (fun h => by cases h) (fun h => by cases h.1)
  | ok p =>
    have hp := uncompress_valid hunc
    simp only [Bind.bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      Except.ok.injEq]
    by_cases hinf : p.isInfinity = true
    · rw [ite_eq_left hinf]
      refine iff_of_false (fun h => by cases h) ?_
      rintro ⟨rfl, -, hne, -⟩
      exact hne ((isInfinity_eq_true_iff_toPoint_eq_zero hp).mp hinf)
    · rw [ite_eq_right hinf]
      have hne : toPoint p ≠ 0 := fun h => hinf ((isInfinity_eq_true_iff_toPoint_eq_zero hp).mpr h)
      by_cases hsub : inSubgroup p = true
      · rw [ite_eq_right (by simp [hsub])]
        refine ⟨fun h => ?_, fun h => h.1 ▸ rfl⟩
        cases h
        exact ⟨rfl, hp, hne, (inSubgroup_iff_modulus_smul_eq_zero hp).mp hsub⟩
      · rw [ite_eq_left (by simp [hsub])]
        refine iff_of_false (fun h => by cases h) ?_
        rintro ⟨rfl, -, -, hr⟩
        exact hsub ((inSubgroup_iff_modulus_smul_eq_zero hp).mpr hr)

/-- A compressed representative of a nonzero multiple of `g1` passes key validation. -/
theorem keyValidatePoint_compress_of_represents {P : G1} {a : Fr} (hP : Represents P a)
    (ha : a ≠ 0) : ∃ Q, keyValidatePoint (compress P) = .ok Q ∧ Represents Q a := by
  obtain ⟨q, hq, hqp⟩ := uncompress_compress hP.1
  have hv := uncompress_valid hq
  refine ⟨q, keyValidatePoint_eq_ok_iff.mpr ⟨hq, hv, ?_, ?_⟩, hv, hqp.trans hP.2⟩
  · rw [hqp, hP.2, Ne, ← isInfinity_eq_true_iff_toPoint_eq_zero (valid_mul valid_generator a),
      mul_generator_isInfinity_iff]
    exact ha
  · rw [hqp, hP.2]
    exact modulus_smul_toPoint_mul_generator a

/-- The compressed form of a nonzero multiple `a • g1` passes key validation. -/
theorem keyValidatePoint_compress_mul {a : Fr} (ha : a ≠ 0) :
    ∃ P, keyValidatePoint (compress (mul generator a)) = .ok P ∧ Represents P a :=
  keyValidatePoint_compress_of_represents (represents_mul_generator a) ha

end G1

namespace G2

/-- A valid point satisfies the curve equation that the encoder checks. -/
theorem isOnTwist_of_valid {P : G2} (hP : Valid P) : isOnTwist P = true := by
  unfold isOnTwist
  split
  · rfl
  · have h := valid_equation hP
    simp only [rep_x, rep_y, rep_z] at h
    rw [beq_iff_eq]
    linear_combination h

/-- A multiple of the generator lies in the subgroup of order `r`. -/
theorem modulus_smul_toPoint_mul_generator (b : Fr) :
    Fr.modulus • toPoint (mul generator b) = 0 := by
  rw [toPoint_mul valid_generator, smul_comm, modulus_smul_generator, nsmul_zero]

/-- The subgroup check accepts exactly the valid points that represent a multiple of `g2`. -/
theorem inSubgroup_iff_exists_represents {Q : G2} (hQ : Valid Q) :
    inSubgroup Q = true ↔ ∃ b, Represents Q b := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := exists_mul_generator_of_inSubgroup hQ h
    exact ⟨b, hQ, hb⟩
  · rintro ⟨b, -, hb⟩
    rw [inSubgroup_iff_modulus_smul_eq_zero hQ, hb]
    exact modulus_smul_toPoint_mul_generator b

/-- A decoded point is valid. -/
theorem valid_of_uncompress {bytes : ByteArray} {Q : G2} (h : uncompress bytes = .ok Q) :
    Valid Q := by
  rcases uncompress_valid h with rfl | ⟨hz, ht⟩
  · exact valid_zero
  · exact valid_of_isOnTwist_of_z_one hz ht

/-- A compressed representative of `b • g2` decodes to a subgroup point that represents it. -/
theorem uncompress_compress_of_represents {S : G2} {b : Fr} (hS : Represents S b) :
    ∃ Q, uncompress (compress S) = .ok Q ∧ inSubgroup Q = true ∧ Represents Q b := by
  obtain ⟨q, hq, hqp⟩ := uncompress_compress (isOnTwist_of_valid hS.1)
  have hqv := valid_of_uncompress hq
  have hrep : Represents q b :=
    ⟨hqv, ((projectiveEq_eq_true_iff_toPoint_eq hqv hS.1).mp hqp).trans hS.2⟩
  exact ⟨q, hq, (inSubgroup_iff_exists_represents hqv).mpr ⟨b, hrep⟩, hrep⟩

/-- The compressed form of `b • g2` decodes to a point of the subgroup that represents `b • g2`. -/
theorem uncompress_compress_mul_inSubgroup (b : Fr) :
    ∃ Q, uncompress (compress (mul generator b)) = .ok Q ∧ inSubgroup Q = true ∧
      Represents Q b :=
  uncompress_compress_of_represents (represents_mul_generator b)

end G2

/-- The signature subgroup check accepts exactly one set of valid points.

They are the valid points that represent a multiple of `g2`. -/
theorem Signatures.signatureSubgroupCheck_iff {sig : G2} (h : G2.Valid sig) :
    Signatures.signatureSubgroupCheck sig = true ↔ ∃ b, G2.Represents sig b :=
  G2.inSubgroup_iff_exists_represents h

end EthLib.Cryptography.Bls
