module

public import EthLib.Cryptography.Kzg.Core
public import EthLib.Cryptography.Proofs.Kzg.Polynomials

/-!
# Proofs: `Core`

The validation surface of the blob-commitment methods: the byte
validators succeed exactly on valid bytes (returning them unchanged),
`computeChallenge` produces a canonical field element, and each entry
point rejects malformed input with exactly the documented error before
doing any real work.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants

/-- `validateKzgG1` agrees with `validateKzgG1Point` on whether the input
bytes are valid. -/
theorem validateKzgG1_eq_validateKzgG1Point (b : Bytes48) :
    validateKzgG1 b = (validateKzgG1Point b).isOk := by
  rw [validateKzgG1, validateKzgG1Point]
  split
  · rfl
  · rw [Bls.G1.keyValidate]
    cases Bls.G1.keyValidatePoint b <;> rfl

/-- A successful `validateKzgG1Point` implies that `validateKzgG1` holds on
the input bytes and the returned `G1` point is in the prime-order subgroup. -/
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

/-- `bytesToKzgCommitment` succeeds exactly on valid bytes, and returns
them unchanged. -/
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

/-- `bytesToKzgProof` succeeds exactly on valid bytes, and returns them
unchanged. -/
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

/-- Serializing the Fiat-Shamir challenge produces a 32-byte field element. -/
theorem computeChallenge_size (blob : Blob) (commitment : KZGCommitment) :
    (blsFieldToBytes (computeChallenge blob commitment)).size =
      BYTES_PER_FIELD_ELEMENT := by
  simp only [blsFieldToBytes, Fr.toBytesBE, ByteArray.size, Array.size_ofFn,
    BYTES_PER_FIELD_ELEMENT]

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

/-- `computeKzgProof` rejects a wrongly-sized blob. -/
theorem computeKzgProof_badBlobSize (setup : TrustedSetup) {blob : Blob} (zBytes : Bytes32)
    (h : blob.size ≠ BYTES_PER_BLOB) :
    computeKzgProof setup blob zBytes = throw (.badBlobSize blob.size) := by
  simp [computeKzgProof, h, throw_bind]

/-- `computeKzgProof` rejects a wrongly-sized evaluation point. -/
theorem computeKzgProof_badFieldElementSize (setup : TrustedSetup) {blob : Blob} {zBytes : Bytes32}
    (hb : blob.size = BYTES_PER_BLOB)
    (h : zBytes.size ≠ BYTES_PER_FIELD_ELEMENT) :
    computeKzgProof setup blob zBytes
      = throw (.badFieldElementSize zBytes.size) := by
  simp [computeKzgProof, hb, h, throw_bind]

/-- `verifyKzgProof` rejects a wrongly-sized commitment. -/
theorem verifyKzgProof_badCommitmentSize (setup : TrustedSetup) {commitmentBytes : Bytes48}
    (zBytes yBytes : Bytes32) (proofBytes : Bytes48)
    (h : commitmentBytes.size ≠ BYTES_PER_COMMITMENT) :
    verifyKzgProof setup commitmentBytes zBytes yBytes proofBytes
      = throw (.badCommitmentSize commitmentBytes.size) := by
  simp [verifyKzgProof, h, throw_bind]

/-- `blobToKzgCommitment` rejects a wrongly-sized blob. -/
theorem blobToKzgCommitment_badBlobSize (setup : TrustedSetup) {blob : Blob}
    (h : blob.size ≠ BYTES_PER_BLOB) :
    blobToKzgCommitment setup blob = throw (.badBlobSize blob.size) := by
  simp [blobToKzgCommitment, h, throw_bind]

/-- `computeBlobKzgProof` rejects a wrongly-sized blob. -/
theorem computeBlobKzgProof_badBlobSize (setup : TrustedSetup) {blob : Blob}
    (commitmentBytes : Bytes48) (h : blob.size ≠ BYTES_PER_BLOB) :
    computeBlobKzgProof setup blob commitmentBytes
      = throw (.badBlobSize blob.size) := by
  simp [computeBlobKzgProof, h, throw_bind]

/-- `verifyBlobKzgProof` rejects a wrongly-sized blob. -/
theorem verifyBlobKzgProof_badBlobSize (setup : TrustedSetup) {blob : Blob}
    (commitmentBytes proofBytes : Bytes48)
    (h : blob.size ≠ BYTES_PER_BLOB) :
    verifyBlobKzgProof setup blob commitmentBytes proofBytes
      = throw (.badBlobSize blob.size) := by
  simp [verifyBlobKzgProof, h, throw_bind]

/-- `verifyBlobKzgProofBatch` rejects a commitments array whose length
does not match the blobs array. -/
theorem verifyBlobKzgProofBatch_commitments_mismatch (setup : TrustedSetup)
    {blobs : Array Blob} {commitmentsBytes : Array Bytes48}
    (proofsBytes : Array Bytes48)
    (h : commitmentsBytes.size ≠ blobs.size) :
    verifyBlobKzgProofBatch setup blobs commitmentsBytes proofsBytes
      = throw (.inputLengthMismatch "commitmentsBytes" blobs.size
          commitmentsBytes.size) := by
  simp [verifyBlobKzgProofBatch, h, throw_bind]

/-- `verifyBlobKzgProofBatch` rejects a proofs array whose length does
not match the blobs array. -/
theorem verifyBlobKzgProofBatch_proofs_mismatch (setup : TrustedSetup)
    {blobs : Array Blob} {commitmentsBytes proofsBytes : Array Bytes48}
    (hc : commitmentsBytes.size = blobs.size)
    (h : proofsBytes.size ≠ blobs.size) :
    verifyBlobKzgProofBatch setup blobs commitmentsBytes proofsBytes
      = throw (.inputLengthMismatch "proofsBytes" blobs.size
          proofsBytes.size) := by
  simp [verifyBlobKzgProofBatch, hc, h, throw_bind]

end EthLib.Cryptography.Kzg
