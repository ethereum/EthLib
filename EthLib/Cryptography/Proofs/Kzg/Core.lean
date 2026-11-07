module

public import EthLib.Cryptography.Kzg.Core
public import EthLib.Cryptography.Proofs.Kzg.Polynomials

/-!
# Proofs: the input checks of the blob operations

The validators of commitments and proofs accept exactly the valid bytes, and keep them.

The challenge of a blob is a canonical field element.

Each blob operation rejects each malformed input with its own error, before any other work.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants

/-- `validateKzgG1` agrees with `validateKzgG1Point` on whether the input bytes are valid. -/
theorem validateKzgG1_eq_validateKzgG1Point (b : Bytes48) :
    validateKzgG1 b = (validateKzgG1Point b).isOk := by
  rw [validateKzgG1, validateKzgG1Point]
  split
  · rfl
  · rw [Bls.G1.keyValidate]
    cases Bls.G1.keyValidatePoint ⟨b.toArray⟩ <;> rfl

/-- A successful `validateKzgG1Point` implies that `validateKzgG1` holds on the input bytes.

It also implies that the returned `G1` point is in the prime-order subgroup. -/
theorem validateKzgG1Point_ok_valid {b : Bytes48} {p : Bls.G1}
    (h : validateKzgG1Point b = .ok p) :
    validateKzgG1 b = true ∧ Bls.G1.inSubgroup p = true := by
  refine ⟨?_, ?_⟩
  · rw [validateKzgG1_eq_validateKzgG1Point, h]
    rfl
  · rw [validateKzgG1Point] at h
    split at h
    · cases h
      rfl
    · split at h
      · rename_i q hq
        cases h
        simp only [Bls.G1.keyValidatePoint, Bind.bind, Except.bind, pure, Except.pure] at hq
        split at hq
        · cases hq
        · split at hq
          · cases hq
          · split at hq
            · cases hq
            · rename_i hsub
              cases hq
              simpa using hsub
      · cases h

/-- The parser accepts exactly the bytes of the right length, and keeps them. -/
theorem parseBytes_eq_ok_iff {n : Nat} {err : Nat → KzgError} {b : ByteArray}
    {v : Vector UInt8 n} :
    parseBytes n err b = .ok v ↔ v.toArray = b.data := by
  unfold parseBytes
  split
  · rename_i h
    constructor
    · intro he
      cases he
      rfl
    · intro hv
      congr 1
      exact (Vector.toArray_inj.mp (hv.trans rfl)).symm
  · rename_i h
    constructor
    · intro he
      cases he
    · intro hv
      exact absurd (hv ▸ v.size_toArray : b.data.size = n) h

/-- The parser rejects exactly the bytes of another length, with the error for that length. -/
theorem parseBytes_eq_error_iff {n : Nat} {err : Nat → KzgError} {b : ByteArray}
    {e : KzgError} :
    parseBytes n err b = .error e ↔ b.size ≠ n ∧ e = err b.size := by
  unfold parseBytes
  split
  · rename_i h
    constructor
    · intro he
      cases he
    · rintro ⟨hne, _⟩
      exact absurd h hne
  · rename_i h
    constructor
    · intro he
      cases he
      exact ⟨h, rfl⟩
    · rintro ⟨_, rfl⟩
      rfl

/-- `bytesToKzgCommitment` succeeds exactly on valid bytes, and returns them unchanged. -/
theorem bytesToKzgCommitment_ok_iff {b : Bytes48} {c : KZGCommitment} :
    bytesToKzgCommitment b = .ok c ↔ validateKzgG1 b ∧ c = b := by
  rw [bytesToKzgCommitment]
  split
  · rename_i h
    constructor
    · intro he
      cases he
      exact ⟨h, rfl⟩
    · rintro ⟨_, rfl⟩
      rfl
  · rename_i h
    constructor
    · intro he
      cases he
    · rintro ⟨hv, _⟩
      exact absurd hv h

/-- `bytesToKzgProof` succeeds exactly on valid bytes, and returns them unchanged. -/
theorem bytesToKzgProof_ok_iff {b : Bytes48} {p : KZGProof} :
    bytesToKzgProof b = .ok p ↔ validateKzgG1 b ∧ p = b := by
  rw [bytesToKzgProof]
  split
  · rename_i h
    constructor
    · intro he
      cases he
      exact ⟨h, rfl⟩
    · rintro ⟨_, rfl⟩
      rfl
  · rename_i h
    constructor
    · intro he
      cases he
    · rintro ⟨hv, _⟩
      exact absurd hv h

/-- The Fiat-Shamir challenge is a canonical field element. -/
theorem val_computeChallenge_lt (blob : Blob) (commitment : KZGCommitment) :
    (computeChallenge blob commitment).val < Fr.modulus :=
  Fr.val_hashToBlsField_lt _

/-- `g1LincombPoints` rejects mismatched input lengths. -/
theorem g1LincombPoints_length_mismatch {points : Array Bls.G1}
    {scalars : Array Fr} (h : points.size ≠ scalars.size) :
    g1LincombPoints points scalars
      = throw (.lincombLengthMismatch points.size scalars.size) := by
  simp [g1LincombPoints, h, throw_bind]

/-- `g1LincombPoints` of nothing is the identity (the point at infinity). -/
theorem g1LincombPoints_empty :
    g1LincombPoints #[] #[] = pure Bls.G1.zero := by
  simp [g1LincombPoints]

/-- On equal-length inputs, `g1LincombPoints` computes `Bls.G1.msm`. -/
theorem g1LincombPoints_eq_msm {points : Array Bls.G1} {scalars : Array Fr}
    (h : points.size = scalars.size) :
    g1LincombPoints points scalars = pure (Bls.G1.msm points scalars) := by
  have hne : ¬ (points.size ≠ scalars.size) := fun hcontra => hcontra h
  unfold g1LincombPoints
  rw [ite_eq_right hne]
  by_cases h0 : points.size = 0
  · rw [ite_eq_left h0]
    have hm : Bls.G1.msm points scalars = Bls.G1.zero := by
      unfold Bls.G1.msm
      simp [h0]
    rw [hm]
  · rw [ite_eq_right h0]

/-- `verifyBlobKzgProofBatch` rejects a commitments array whose length differs from the blobs array.
-/
theorem verifyBlobKzgProofBatch_commitments_mismatch (setup : TrustedSetup)
    {blobs : Array Blob} {commitmentsBytes : Array Bytes48}
    (proofsBytes : Array Bytes48)
    (h : commitmentsBytes.size ≠ blobs.size) :
    verifyBlobKzgProofBatch setup blobs commitmentsBytes proofsBytes
      = throw (.inputLengthMismatch "commitmentsBytes" blobs.size
          commitmentsBytes.size) := by
  simp [verifyBlobKzgProofBatch, h, throw_bind]

/-- `verifyBlobKzgProofBatch` rejects a proofs array whose length does not match the blobs array.
-/
theorem verifyBlobKzgProofBatch_proofs_mismatch (setup : TrustedSetup)
    {blobs : Array Blob} {commitmentsBytes proofsBytes : Array Bytes48}
    (hc : commitmentsBytes.size = blobs.size)
    (h : proofsBytes.size ≠ blobs.size) :
    verifyBlobKzgProofBatch setup blobs commitmentsBytes proofsBytes
      = throw (.inputLengthMismatch "proofsBytes" blobs.size
          proofsBytes.size) := by
  simp [verifyBlobKzgProofBatch, hc, h, throw_bind]

end EthLib.Cryptography.Kzg
