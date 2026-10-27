import EthLib.Cryptography.Kzg.Cells
import EthLib.Cryptography.Proofs.Kzg.Polynomials

/-!
# Proofs: `Cells`

Shape properties of the coefficient-form helpers (`addPolynomialcoeff`
spans the longer input, `cosetForCell` yields a full cell of points),
canonicity of the batch challenge, and the validation surface of the
cell-proof entry points: each malformed input is rejected with exactly
the documented error before any real work.
-/

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants


/-- A cell's coset has exactly `FIELD_ELEMENTS_PER_CELL` points. -/
theorem size_cosetForCell {cellIndex : CellIndex} {c : Coset}
    (h : cosetForCell cellIndex = .ok c) :
    c.size = FIELD_ELEMENTS_PER_CELL := by
  simp only [cosetForCell, bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  · cases h
  · injection h with h
    subst h
    simp

/-- `cosetForCell` rejects an out-of-bounds cell index. -/
theorem cosetForCell_cellIndexOutOfBounds {cellIndex : CellIndex}
    (h : cellIndex ≥ CELLS_PER_EXT_BLOB) :
    cosetForCell cellIndex = .error .cellIndexOutOfBounds := by
  simp [cosetForCell, h, Bind.bind, Except.bind]

/-- `cosetForCell` succeeds for every `cellIndex < CELLS_PER_EXT_BLOB`,
returning a coset of size `FIELD_ELEMENTS_PER_CELL`. -/
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
    rw [if_neg (Nat.not_le.mpr h)]
    rfl
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

private theorem size_foldl_cosetEvalsToCell (cosetEvals : CosetEvals) (k : Nat) :
    ((List.range k).foldl (fun bytes i => bytes ++ blsFieldToBytes cosetEvals[i]!)
      ByteArray.empty).size = k * BYTES_PER_FIELD_ELEMENT := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ByteArray.size_append, ih, size_blsFieldToBytes, Nat.succ_mul]

/-- `cosetEvalsToCell` always produces a byte buffer of size `BYTES_PER_CELL`. -/
@[simp] theorem size_cosetEvalsToCell (cosetEvals : CosetEvals) :
    (cosetEvalsToCell cosetEvals).size = BYTES_PER_CELL := by
  unfold cosetEvalsToCell
  rw [← Array.foldl_toList, Array.toList_range, size_foldl_cosetEvalsToCell]
  rfl

private theorem ba_extract_append_of_le {a b : ByteArray} {s e : Nat}
    (he : e ≤ a.size) :
    (a ++ b).extract s e = a.extract s e := by
  have he' : e ≤ a.data.size := he
  apply ByteArray.ext
  rw [ByteArray.data_extract, ByteArray.data_extract, ByteArray.data_append,
      Array.extract_append,
      Array.extract_empty_of_stop_le_start (show e - a.data.size ≤ s - a.data.size by omega),
      Array.append_empty]

private theorem ba_extract_append_exact {a b : ByteArray} :
    (a ++ b).extract a.size (a.size + b.size) = b := by
  have hsz : a.size = a.data.size := rfl
  have hbsz : b.size = b.data.size := rfl
  apply ByteArray.ext
  rw [ByteArray.data_extract, ByteArray.data_append, hsz, hbsz]
  simp [-ByteArray.size_data]

private theorem extract_foldl_cosetEvalsToCell (cosetEvals : CosetEvals)
    (k j : Nat) (hj : j < k) :
    ((List.range k).foldl (fun bytes i => bytes ++ blsFieldToBytes cosetEvals[i]!)
      ByteArray.empty).extract
        (j * BYTES_PER_FIELD_ELEMENT) ((j + 1) * BYTES_PER_FIELD_ELEMENT) =
      blsFieldToBytes cosetEvals[j]! := by
  induction k with
  | zero => exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    let pref := (List.range k).foldl
      (fun bytes i => bytes ++ blsFieldToBytes cosetEvals[i]!) ByteArray.empty
    have hpref_sz : pref.size = k * BYTES_PER_FIELD_ELEMENT :=
      size_foldl_cosetEvalsToCell cosetEvals k
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · rw [ba_extract_append_of_le (a := pref)]
      · exact ih hlt
      · rw [hpref_sz]
        exact Nat.mul_le_mul_right BYTES_PER_FIELD_ELEMENT hlt
    · have h1 : j * BYTES_PER_FIELD_ELEMENT = pref.size := hpref_sz.symm
      have h2 : (j + 1) * BYTES_PER_FIELD_ELEMENT =
          pref.size + (blsFieldToBytes cosetEvals[j]!).size := by
        rw [hpref_sz, size_blsFieldToBytes, Nat.succ_mul]
      rw [h1, h2, ba_extract_append_exact (a := pref)]

/-- Extracting the `j`-th 32-byte field-element chunk from `cosetEvalsToCell`
returns `blsFieldToBytes cosetEvals[j]!`. -/
@[simp] theorem extract_cosetEvalsToCell (cosetEvals : CosetEvals)
    {j : Nat} (hj : j < FIELD_ELEMENTS_PER_CELL) :
    (cosetEvalsToCell cosetEvals).extract
        (j * BYTES_PER_FIELD_ELEMENT) ((j + 1) * BYTES_PER_FIELD_ELEMENT) =
      blsFieldToBytes cosetEvals[j]! := by
  unfold cosetEvalsToCell
  rw [← Array.foldl_toList, Array.toList_range]
  exact extract_foldl_cosetEvalsToCell cosetEvals FIELD_ELEMENTS_PER_CELL j hj

/-- Deserializing the `j`-th 32-byte field-element chunk from `cosetEvalsToCell`
recovers `cosetEvals[j]!`. -/
@[simp] theorem bytesToBlsField_extract_cosetEvalsToCell (cosetEvals : CosetEvals)
    {j : Nat} (hj : j < FIELD_ELEMENTS_PER_CELL) :
    bytesToBlsField ((cosetEvalsToCell cosetEvals).extract
        (j * BYTES_PER_FIELD_ELEMENT) ((j + 1) * BYTES_PER_FIELD_ELEMENT)) =
      .ok cosetEvals[j]! := by
  rw [extract_cosetEvalsToCell cosetEvals hj, bytesToBlsField_blsFieldToBytes]

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

/-- The cell-batch challenge serializes to `BYTES_PER_FIELD_ELEMENT` bytes
and is a canonical field element. -/
theorem size_computeVerifyCellKzgProofBatchChallenge
    (commitments : Array KZGCommitment)
    (commitmentIndices : Array CommitmentIndex)
    (cellIndices : Array CellIndex)
    (cosetsEvals : Array CosetEvals)
    (proofs : Array KZGProof) :
    (blsFieldToBytes (computeVerifyCellKzgProofBatchChallenge commitments
      commitmentIndices cellIndices cosetsEvals proofs)).size =
        BYTES_PER_FIELD_ELEMENT ∧
    (computeVerifyCellKzgProofBatchChallenge commitments commitmentIndices
      cellIndices cosetsEvals proofs).val < Fr.modulus :=
  ⟨by simp only [blsFieldToBytes, Fr.toBytesBE, ByteArray.size, Array.size_ofFn,
        BYTES_PER_FIELD_ELEMENT],
   val_computeVerifyCellKzgProofBatchChallenge_lt _ _ _ _ _⟩

/-- `cellToCosetEvals` rejects a wrongly-sized cell. -/
theorem cellToCosetEvals_badCellSize {cell : Cell}
    (h : cell.size ≠ BYTES_PER_CELL) :
    cellToCosetEvals cell = throw (.badCellSize cell.size) := by
  simp [cellToCosetEvals, h]
  rfl

/-- `computeCells` rejects a wrongly-sized blob. -/
theorem computeCells_badBlobSize {blob : Blob}
    (h : blob.size ≠ BYTES_PER_BLOB) :
    computeCells blob = throw (.badBlobSize blob.size) := by
  simp [computeCells, h]
  rfl

/-- `computeCellsAndKzgProofs` rejects a wrongly-sized blob. -/
theorem computeCellsAndKzgProofs_badBlobSize {blob : Blob}
    (h : blob.size ≠ BYTES_PER_BLOB) :
    computeCellsAndKzgProofs blob = throw (.badBlobSize blob.size) := by
  simp [computeCellsAndKzgProofs, h]
  rfl

/-! ## `verifyCellKzgProofBatchImpl` validation -/

/-- Rejects a `cellIndices` array whose length does not match
`commitmentIndices`. -/
theorem verifyCellKzgProofBatchImpl_cellIndices_mismatch
    {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    (h : cellIndices.size ≠ commitmentIndices.size) :
    verifyCellKzgProofBatchImpl commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw (.inputLengthMismatch "cellIndices" commitmentIndices.size
          cellIndices.size) := by
  simp [verifyCellKzgProofBatchImpl, h]
  rfl

/-- Rejects a `cosetsEvals` array whose length does not match
`commitmentIndices`. -/
theorem verifyCellKzgProofBatchImpl_cosetsEvals_mismatch
    {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    (hcell : cellIndices.size = commitmentIndices.size)
    (h : cosetsEvals.size ≠ commitmentIndices.size) :
    verifyCellKzgProofBatchImpl commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw (.inputLengthMismatch "cosetsEvals" commitmentIndices.size
          cosetsEvals.size) := by
  simp [verifyCellKzgProofBatchImpl, hcell, h]
  rfl

/-- Rejects a `proofs` array whose length does not match
`commitmentIndices`. -/
theorem verifyCellKzgProofBatchImpl_proofs_mismatch
    {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    (hcell : cellIndices.size = commitmentIndices.size)
    (hcoset : cosetsEvals.size = commitmentIndices.size)
    (h : proofs.size ≠ commitmentIndices.size) :
    verifyCellKzgProofBatchImpl commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw (.inputLengthMismatch "proofs" commitmentIndices.size
          proofs.size) := by
  simp [verifyCellKzgProofBatchImpl, hcell, hcoset, h]
  rfl

/-- Rejects a commitment index that is out of bounds. -/
theorem verifyCellKzgProofBatchImpl_commitmentIndexOutOfBounds
    {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    (hcell : cellIndices.size = commitmentIndices.size)
    (hcoset : cosetsEvals.size = commitmentIndices.size)
    (hproof : proofs.size = commitmentIndices.size)
    (h : commitmentIndices.any (· ≥ commitments.size) = true) :
    verifyCellKzgProofBatchImpl commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw .commitmentIndexOutOfBounds := by
  simp [verifyCellKzgProofBatchImpl, hcell, hcoset, hproof, h]
  rfl

/-- Rejects a commitments array that contains duplicate entries. -/
theorem verifyCellKzgProofBatchImpl_duplicateCommitments
    {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    (hcell : cellIndices.size = commitmentIndices.size)
    (hcoset : cosetsEvals.size = commitmentIndices.size)
    (hproof : proofs.size = commitmentIndices.size)
    (hcidx : commitmentIndices.any (· ≥ commitments.size) = false)
    (h : (Array.range commitments.size).any
      (fun i => commitments.idxOf? commitments[i]! ≠ some i) = true) :
    verifyCellKzgProofBatchImpl commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw .duplicateCommitments := by
  unfold verifyCellKzgProofBatchImpl
  rw [h, hcidx]
  simp [hcell, hcoset, hproof]
  rfl

/-- Alias for `verifyCellKzgProofBatchImpl_cellIndices_mismatch`. -/
theorem computeVerifyCellKzgProofBatchChallenge_mismatch_cellIndices
    {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    (h : cellIndices.size ≠ commitmentIndices.size) :
    verifyCellKzgProofBatchImpl commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw (.inputLengthMismatch "cellIndices" commitmentIndices.size
          cellIndices.size) :=
  verifyCellKzgProofBatchImpl_cellIndices_mismatch h

/-- Alias for `verifyCellKzgProofBatchImpl_cosetsEvals_mismatch`. -/
theorem computeVerifyCellKzgProofBatchChallenge_mismatch_cosetsEvals
    {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    (hcell : cellIndices.size = commitmentIndices.size)
    (h : cosetsEvals.size ≠ commitmentIndices.size) :
    verifyCellKzgProofBatchImpl commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw (.inputLengthMismatch "cosetsEvals" commitmentIndices.size
          cosetsEvals.size) :=
  verifyCellKzgProofBatchImpl_cosetsEvals_mismatch hcell h

/-- Alias for `verifyCellKzgProofBatchImpl_proofs_mismatch`. -/
theorem computeVerifyCellKzgProofBatchChallenge_mismatch_proofs
    {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    (hcell : cellIndices.size = commitmentIndices.size)
    (hcoset : cosetsEvals.size = commitmentIndices.size)
    (h : proofs.size ≠ commitmentIndices.size) :
    verifyCellKzgProofBatchImpl commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw (.inputLengthMismatch "proofs" commitmentIndices.size
          proofs.size) :=
  verifyCellKzgProofBatchImpl_proofs_mismatch hcell hcoset h

/-- Alias for `verifyCellKzgProofBatchImpl_commitmentIndexOutOfBounds`. -/
theorem computeVerifyCellKzgProofBatchChallenge_commitmentIndex_oob
    {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    (hcell : cellIndices.size = commitmentIndices.size)
    (hcoset : cosetsEvals.size = commitmentIndices.size)
    (hproof : proofs.size = commitmentIndices.size)
    (h : commitmentIndices.any (· ≥ commitments.size) = true) :
    verifyCellKzgProofBatchImpl commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw .commitmentIndexOutOfBounds :=
  verifyCellKzgProofBatchImpl_commitmentIndexOutOfBounds hcell hcoset hproof h

/-! ## `verifyCellKzgProofBatch` validation -/

/-- Rejects a `cells` array whose length does not match
`commitmentsBytes`. -/
theorem verifyCellKzgProofBatch_cells_mismatch
    {commitmentsBytes : Array Bytes48} {cellIndices : Array CellIndex}
    {cells : Array Cell} {proofsBytes : Array Bytes48}
    (h : cells.size ≠ commitmentsBytes.size) :
    verifyCellKzgProofBatch commitmentsBytes cellIndices cells proofsBytes
      = throw (.inputLengthMismatch "cells" commitmentsBytes.size
          cells.size) := by
  simp [verifyCellKzgProofBatch, h]
  rfl

/-- Rejects a `proofsBytes` array whose length does not match
`commitmentsBytes`. -/
theorem verifyCellKzgProofBatch_proofsBytes_mismatch
    {commitmentsBytes : Array Bytes48} {cellIndices : Array CellIndex}
    {cells : Array Cell} {proofsBytes : Array Bytes48}
    (hcells : cells.size = commitmentsBytes.size)
    (h : proofsBytes.size ≠ commitmentsBytes.size) :
    verifyCellKzgProofBatch commitmentsBytes cellIndices cells proofsBytes
      = throw (.inputLengthMismatch "proofsBytes" commitmentsBytes.size
          proofsBytes.size) := by
  simp [verifyCellKzgProofBatch, hcells, h]
  rfl

/-- Rejects a `cellIndices` array whose length does not match
`commitmentsBytes`. -/
theorem verifyCellKzgProofBatch_cellIndices_mismatch
    {commitmentsBytes : Array Bytes48} {cellIndices : Array CellIndex}
    {cells : Array Cell} {proofsBytes : Array Bytes48}
    (hcells : cells.size = commitmentsBytes.size)
    (hproofs : proofsBytes.size = commitmentsBytes.size)
    (h : cellIndices.size ≠ commitmentsBytes.size) :
    verifyCellKzgProofBatch commitmentsBytes cellIndices cells proofsBytes
      = throw (.inputLengthMismatch "cellIndices" commitmentsBytes.size
          cellIndices.size) := by
  simp [verifyCellKzgProofBatch, hcells, hproofs, h]
  rfl

/-- Rejects a wrongly-sized commitment, reporting the first offender. -/
theorem verifyCellKzgProofBatch_badCommitmentSize
    {commitmentsBytes : Array Bytes48} {cellIndices : Array CellIndex}
    {cells : Array Cell} {proofsBytes : Array Bytes48} {cb : Bytes48}
    (hcells : cells.size = commitmentsBytes.size)
    (hproofs : proofsBytes.size = commitmentsBytes.size)
    (hcidx : cellIndices.size = commitmentsBytes.size)
    (h : commitmentsBytes.find? (fun cb => cb.size != BYTES_PER_COMMITMENT)
      = some cb) :
    verifyCellKzgProofBatch commitmentsBytes cellIndices cells proofsBytes
      = throw (.badCommitmentSize cb.size) := by
  simp [verifyCellKzgProofBatch, hcells, hproofs, hcidx, h]
  rfl

/-- Rejects an out-of-bounds cell index in `verifyCellKzgProofBatch`. -/
theorem verifyCellKzgProofBatch_cellIndexOutOfBounds
    {commitmentsBytes : Array Bytes48} {cellIndices : Array CellIndex}
    {cells : Array Cell} {proofsBytes : Array Bytes48}
    (hcells : cells.size = commitmentsBytes.size)
    (hproofs : proofsBytes.size = commitmentsBytes.size)
    (hcidx : cellIndices.size = commitmentsBytes.size)
    (hcb : commitmentsBytes.find? (fun cb => cb.size != BYTES_PER_COMMITMENT)
      = none)
    (h : cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) = true) :
    verifyCellKzgProofBatch commitmentsBytes cellIndices cells proofsBytes
      = throw .cellIndexOutOfBounds := by
  unfold verifyCellKzgProofBatch
  rw [hcb, h]
  simp [hcells, hproofs, hcidx]
  rfl

/-- Alias for `verifyCellKzgProofBatch_cellIndexOutOfBounds`. -/
theorem computeVerifyCellKzgProofBatchChallenge_cellIndex_oob
    {commitmentsBytes : Array Bytes48} {cellIndices : Array CellIndex}
    {cells : Array Cell} {proofsBytes : Array Bytes48}
    (hcells : cells.size = commitmentsBytes.size)
    (hproofs : proofsBytes.size = commitmentsBytes.size)
    (hcidx : cellIndices.size = commitmentsBytes.size)
    (hcb : commitmentsBytes.find? (fun cb => cb.size != BYTES_PER_COMMITMENT)
      = none)
    (h : cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) = true) :
    verifyCellKzgProofBatch commitmentsBytes cellIndices cells proofsBytes
      = throw .cellIndexOutOfBounds :=
  verifyCellKzgProofBatch_cellIndexOutOfBounds hcells hproofs hcidx hcb h

/-- Rejects a wrongly-sized cell, reporting the first offender. -/
theorem verifyCellKzgProofBatch_badCellSize
    {commitmentsBytes : Array Bytes48} {cellIndices : Array CellIndex}
    {cells : Array Cell} {proofsBytes : Array Bytes48} {c : Cell}
    (hcells : cells.size = commitmentsBytes.size)
    (hproofs : proofsBytes.size = commitmentsBytes.size)
    (hcidx : cellIndices.size = commitmentsBytes.size)
    (hcb : commitmentsBytes.find? (fun cb => cb.size != BYTES_PER_COMMITMENT)
      = none)
    (hbound : cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) = false)
    (h : cells.find? (fun c => c.size != BYTES_PER_CELL) = some c) :
    verifyCellKzgProofBatch commitmentsBytes cellIndices cells proofsBytes
      = throw (.badCellSize c.size) := by
  unfold verifyCellKzgProofBatch
  rw [hcb, hbound, h]
  simp [hcells, hproofs, hcidx]
  rfl

/-- Rejects a wrongly-sized proof, reporting the first offender. -/
theorem verifyCellKzgProofBatch_badProofSize
    {commitmentsBytes : Array Bytes48} {cellIndices : Array CellIndex}
    {cells : Array Cell} {proofsBytes : Array Bytes48} {pb : Bytes48}
    (hcells : cells.size = commitmentsBytes.size)
    (hproofs : proofsBytes.size = commitmentsBytes.size)
    (hcidx : cellIndices.size = commitmentsBytes.size)
    (hcb : commitmentsBytes.find? (fun cb => cb.size != BYTES_PER_COMMITMENT)
      = none)
    (hbound : cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) = false)
    (hcellsz : cells.find? (fun c => c.size != BYTES_PER_CELL) = none)
    (h : proofsBytes.find? (fun pb => pb.size != BYTES_PER_PROOF) = some pb) :
    verifyCellKzgProofBatch commitmentsBytes cellIndices cells proofsBytes
      = throw (.badProofSize pb.size) := by
  unfold verifyCellKzgProofBatch
  rw [hcb, hbound, hcellsz, h]
  simp [hcells, hproofs, hcidx]
  rfl

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
