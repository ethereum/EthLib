module

public import EthLib.Cryptography.Kzg.Cells
public import EthLib.Cryptography.Proofs.Kzg.Polynomials

/-!
# Proofs: the shape and the input checks of the cell operations

The sum of two coefficient arrays spans the longer one.

The coset of a cell has a full cell of points.

The batch challenge is a canonical field element.

Each cell operation rejects each malformed input with its own error, before any other work.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants


/-- A cell's coset has exactly `FIELD_ELEMENTS_PER_CELL` points. -/
theorem size_cosetForCell {cellIndex : CellIndex} {c : Coset}
    (h : cosetForCell cellIndex = .ok c) :
    c.size = FIELD_ELEMENTS_PER_CELL := by
  simp only [cosetForCell, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  · cases h
  · injection h with h
    subst h
    simp

/-- `cosetForCell` rejects an out-of-bounds cell index. -/
theorem cosetForCell_cellIndexOutOfBounds {cellIndex : CellIndex}
    (h : cellIndex ≥ CELLS_PER_EXT_BLOB) :
    cosetForCell cellIndex = .error .cellIndexOutOfBounds := by
  simp [cosetForCell, h, throw, throwThe, MonadExceptOf.throw]

/-- `cosetForCell` succeeds for every `cellIndex < CELLS_PER_EXT_BLOB`.

It returns a coset of size `FIELD_ELEMENTS_PER_CELL`. -/
theorem cosetForCell_ok_of_lt {cellIndex : CellIndex}
    (h : cellIndex < CELLS_PER_EXT_BLOB) :
    ∃ c, cosetForCell cellIndex = .ok c ∧
      c.size = FIELD_ELEMENTS_PER_CELL ∧
      ∀ i < FIELD_ELEMENTS_PER_CELL,
        c[i]! = (rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB)[FIELD_ELEMENTS_PER_CELL * cellIndex + i]! := by
  let domain := rootsOfUnityBrp FIELD_ELEMENTS_PER_EXT_BLOB
  let start := FIELD_ELEMENTS_PER_CELL * cellIndex
  let c : Coset := Array.ofFn (n := FIELD_ELEMENTS_PER_CELL) fun i => domain[start + i.val]!
  have hc : cosetForCell cellIndex = .ok c := by
    unfold cosetForCell
    rw [dite_eq_right (Nat.not_le.mpr h)]
    exact congrArg Except.ok (congrArg Array.ofFn (funext fun i => (getElem!_pos _ _ _).symm))
  refine ⟨c, hc, size_cosetForCell hc, fun i hi => ?_⟩
  rw [getElem!_pos c i (by simp [c, hi])]
  simp [c, domain, start]

/-- `cosetForCell cellIndex` succeeds iff `cellIndex < CELLS_PER_EXT_BLOB`. -/
theorem cosetForCell_ok_iff {cellIndex : CellIndex} :
    (∃ c, cosetForCell cellIndex = .ok c) ↔ cellIndex < CELLS_PER_EXT_BLOB := by
  constructor
  · rintro ⟨c, hc⟩
    exact Decidable.byContradiction fun hge => by
      rw [cosetForCell_cellIndexOutOfBounds (Nat.not_lt.mp hge)] at hc
      cases hc
  · intro hlt
    obtain ⟨c, hc, _, _⟩ := cosetForCell_ok_of_lt hlt
    exact ⟨c, hc⟩

/-- Encoding a cell and decoding it gives back the same field elements. -/
theorem cellToCosetEvals_cosetEvalsToCell
    (ys : CosetEvals) (hsize : ys.size = FIELD_ELEMENTS_PER_CELL) :
    cellToCosetEvals (cosetEvalsToCell ys) = .ok ys := by
  unfold cellToCosetEvals cosetEvalsToCell
  refine (bytesToBlsFields_eq_ok (k := FIELD_ELEMENTS_PER_CELL) (fun i => ys[i.val]!)
    fun i => ?_).trans ?_
  · rw [fieldElementBytes_flatten]
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, bytesToBlsField_blsFieldToBytes]
    rfl
  refine congrArg Except.ok ?_
  apply Array.ext
  · simp [hsize]
  · intro i _ hi
    simp [getElem!_pos ys i hi]

/-- The cell-batch challenge is a canonical field element. -/
theorem val_computeVerifyCellKzgProofBatchChallenge_lt
    (commitments : Array KZGCommitment)
    (commitmentIndices : Array CommitmentIndex)
    (cellIndices : Array CellIndex)
    (cosetsEvals : Array CosetEvals)
    (proofs : Array KZGProof) :
    (computeVerifyCellKzgProofBatchChallenge commitments commitmentIndices
      cellIndices cosetsEvals proofs).val < Fr.modulus := by
  rw [computeVerifyCellKzgProofBatchChallenge]
  exact Fr.val_hashToBlsField_lt _

/-! ## `verifyCellKzgProofBatchImpl` validation -/

/-- Rejects a `cellIndices` array whose length does not match `commitmentIndices`. -/
theorem verifyCellKzgProofBatchImpl_cellIndices_mismatch (setup : TrustedSetup)
    {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    (h : cellIndices.size ≠ commitmentIndices.size) :
    verifyCellKzgProofBatchImpl setup commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw (.inputLengthMismatch "cellIndices" commitmentIndices.size
          cellIndices.size) := by
  simp [verifyCellKzgProofBatchImpl, h, throw_bind]

/-- Rejects a `cosetsEvals` array whose length does not match `commitmentIndices`. -/
theorem verifyCellKzgProofBatchImpl_cosetsEvals_mismatch (setup : TrustedSetup)
    {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    (hcell : cellIndices.size = commitmentIndices.size)
    (h : cosetsEvals.size ≠ commitmentIndices.size) :
    verifyCellKzgProofBatchImpl setup commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw (.inputLengthMismatch "cosetsEvals" commitmentIndices.size
          cosetsEvals.size) := by
  simp [verifyCellKzgProofBatchImpl, hcell, h, throw_bind]

/-- Rejects a `proofs` array whose length does not match `commitmentIndices`. -/
theorem verifyCellKzgProofBatchImpl_proofs_mismatch (setup : TrustedSetup)
    {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    (hcell : cellIndices.size = commitmentIndices.size)
    (hcoset : cosetsEvals.size = commitmentIndices.size)
    (h : proofs.size ≠ commitmentIndices.size) :
    verifyCellKzgProofBatchImpl setup commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw (.inputLengthMismatch "proofs" commitmentIndices.size
          proofs.size) := by
  simp [verifyCellKzgProofBatchImpl, hcell, hcoset, h, throw_bind]

/-- Rejects a commitment index that is out of bounds. -/
theorem verifyCellKzgProofBatchImpl_commitmentIndexOutOfBounds (setup : TrustedSetup)
    {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    (hcell : cellIndices.size = commitmentIndices.size)
    (hcoset : cosetsEvals.size = commitmentIndices.size)
    (hproof : proofs.size = commitmentIndices.size)
    (h : commitmentIndices.any (· ≥ commitments.size) = true) :
    verifyCellKzgProofBatchImpl setup commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw .commitmentIndexOutOfBounds := by
  simp [verifyCellKzgProofBatchImpl, hcell, hcoset, hproof, h, throw_bind]

/-- Rejects a commitments array that contains duplicate entries. -/
theorem verifyCellKzgProofBatchImpl_duplicateCommitments (setup : TrustedSetup)
    {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    (hcell : cellIndices.size = commitmentIndices.size)
    (hcoset : cosetsEvals.size = commitmentIndices.size)
    (hproof : proofs.size = commitmentIndices.size)
    (hcidx : commitmentIndices.any (· ≥ commitments.size) = false)
    (h : commitments.zipIdx.any (fun (c, i) => commitments.idxOf? c ≠ some i) = true) :
    verifyCellKzgProofBatchImpl setup commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw .duplicateCommitments := by
  unfold verifyCellKzgProofBatchImpl
  rw [h, hcidx]
  simp [hcell, hcoset, hproof, throw_bind]

/-- Alias for `verifyCellKzgProofBatchImpl_cellIndices_mismatch`. -/
theorem computeVerifyCellKzgProofBatchChallenge_mismatch_cellIndices (setup : TrustedSetup)
    {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    (h : cellIndices.size ≠ commitmentIndices.size) :
    verifyCellKzgProofBatchImpl setup commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw (.inputLengthMismatch "cellIndices" commitmentIndices.size
          cellIndices.size) :=
  verifyCellKzgProofBatchImpl_cellIndices_mismatch setup h

/-- Alias for `verifyCellKzgProofBatchImpl_cosetsEvals_mismatch`. -/
theorem computeVerifyCellKzgProofBatchChallenge_mismatch_cosetsEvals (setup : TrustedSetup)
    {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    (hcell : cellIndices.size = commitmentIndices.size)
    (h : cosetsEvals.size ≠ commitmentIndices.size) :
    verifyCellKzgProofBatchImpl setup commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw (.inputLengthMismatch "cosetsEvals" commitmentIndices.size
          cosetsEvals.size) :=
  verifyCellKzgProofBatchImpl_cosetsEvals_mismatch setup hcell h

/-- Alias for `verifyCellKzgProofBatchImpl_proofs_mismatch`. -/
theorem computeVerifyCellKzgProofBatchChallenge_mismatch_proofs (setup : TrustedSetup)
    {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    (hcell : cellIndices.size = commitmentIndices.size)
    (hcoset : cosetsEvals.size = commitmentIndices.size)
    (h : proofs.size ≠ commitmentIndices.size) :
    verifyCellKzgProofBatchImpl setup commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw (.inputLengthMismatch "proofs" commitmentIndices.size
          proofs.size) :=
  verifyCellKzgProofBatchImpl_proofs_mismatch setup hcell hcoset h

/-- Alias for `verifyCellKzgProofBatchImpl_commitmentIndexOutOfBounds`. -/
theorem computeVerifyCellKzgProofBatchChallenge_commitmentIndex_oob (setup : TrustedSetup)
    {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    (hcell : cellIndices.size = commitmentIndices.size)
    (hcoset : cosetsEvals.size = commitmentIndices.size)
    (hproof : proofs.size = commitmentIndices.size)
    (h : commitmentIndices.any (· ≥ commitments.size) = true) :
    verifyCellKzgProofBatchImpl setup commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw .commitmentIndexOutOfBounds :=
  verifyCellKzgProofBatchImpl_commitmentIndexOutOfBounds setup hcell hcoset hproof h

/-! ## `verifyCellKzgProofBatch` validation -/

/-- Rejects a `cells` array whose length does not match `commitmentsBytes`. -/
theorem verifyCellKzgProofBatch_cells_mismatch (setup : TrustedSetup)
    {commitmentsBytes : Array Bytes48} {cellIndices : Array CellIndex}
    {cells : Array Cell} {proofsBytes : Array Bytes48}
    (h : cells.size ≠ commitmentsBytes.size) :
    verifyCellKzgProofBatch setup commitmentsBytes cellIndices cells proofsBytes
      = throw (.inputLengthMismatch "cells" commitmentsBytes.size
          cells.size) := by
  simp [verifyCellKzgProofBatch, h, throw_bind]

/-- Rejects a `proofsBytes` array whose length does not match `commitmentsBytes`. -/
theorem verifyCellKzgProofBatch_proofsBytes_mismatch (setup : TrustedSetup)
    {commitmentsBytes : Array Bytes48} {cellIndices : Array CellIndex}
    {cells : Array Cell} {proofsBytes : Array Bytes48}
    (hcells : cells.size = commitmentsBytes.size)
    (h : proofsBytes.size ≠ commitmentsBytes.size) :
    verifyCellKzgProofBatch setup commitmentsBytes cellIndices cells proofsBytes
      = throw (.inputLengthMismatch "proofsBytes" commitmentsBytes.size
          proofsBytes.size) := by
  simp [verifyCellKzgProofBatch, hcells, h, throw_bind]

/-- Rejects a `cellIndices` array whose length does not match `commitmentsBytes`. -/
theorem verifyCellKzgProofBatch_cellIndices_mismatch (setup : TrustedSetup)
    {commitmentsBytes : Array Bytes48} {cellIndices : Array CellIndex}
    {cells : Array Cell} {proofsBytes : Array Bytes48}
    (hcells : cells.size = commitmentsBytes.size)
    (hproofs : proofsBytes.size = commitmentsBytes.size)
    (h : cellIndices.size ≠ commitmentsBytes.size) :
    verifyCellKzgProofBatch setup commitmentsBytes cellIndices cells proofsBytes
      = throw (.inputLengthMismatch "cellIndices" commitmentsBytes.size
          cellIndices.size) := by
  simp [verifyCellKzgProofBatch, hcells, hproofs, h, throw_bind]

/-- Rejects an out-of-bounds cell index in `verifyCellKzgProofBatch`. -/
theorem verifyCellKzgProofBatch_cellIndexOutOfBounds (setup : TrustedSetup)
    {commitmentsBytes : Array Bytes48} {cellIndices : Array CellIndex}
    {cells : Array Cell} {proofsBytes : Array Bytes48}
    (hcells : cells.size = commitmentsBytes.size)
    (hproofs : proofsBytes.size = commitmentsBytes.size)
    (hcidx : cellIndices.size = commitmentsBytes.size)
    (h : cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) = true) :
    verifyCellKzgProofBatch setup commitmentsBytes cellIndices cells proofsBytes
      = throw .cellIndexOutOfBounds := by
  unfold verifyCellKzgProofBatch
  rw [h]
  simp [hcells, hproofs, hcidx, throw_bind]

/-- Alias for `verifyCellKzgProofBatch_cellIndexOutOfBounds`. -/
theorem computeVerifyCellKzgProofBatchChallenge_cellIndex_oob (setup : TrustedSetup)
    {commitmentsBytes : Array Bytes48} {cellIndices : Array CellIndex}
    {cells : Array Cell} {proofsBytes : Array Bytes48}
    (hcells : cells.size = commitmentsBytes.size)
    (hproofs : proofsBytes.size = commitmentsBytes.size)
    (hcidx : cellIndices.size = commitmentsBytes.size)
    (h : cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) = true) :
    verifyCellKzgProofBatch setup commitmentsBytes cellIndices cells proofsBytes
      = throw .cellIndexOutOfBounds :=
  verifyCellKzgProofBatch_cellIndexOutOfBounds setup hcells hproofs hcidx h

/-- `unpackIndicesBE` rejects any byte buffer whose length is not a multiple of 8. -/
theorem unpackIndicesBE_bad_size {b : ByteArray} (h : b.size % 8 ≠ 0) :
    unpackIndicesBE b = throw (.badIndicesBytesSize b.size) := by
  unfold unpackIndicesBE
  simp [h]
  rfl

/-- `unpackIndicesBE` decodes the empty buffer to `#[]`. -/
@[simp] theorem unpackIndicesBE_empty :
    unpackIndicesBE ByteArray.empty = .ok #[] := by
  have hsz : ByteArray.empty.size = 0 := rfl
  unfold unpackIndicesBE
  simp [hsz]
  rfl

end EthLib.Cryptography.Kzg
