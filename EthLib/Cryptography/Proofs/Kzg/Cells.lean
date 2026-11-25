module

public import EthLib.Base.Proofs.List
public import EthLib.Cryptography.Kzg.Cells
public import EthLib.Cryptography.Proofs.Kzg.Polynomials
import Batteries.Data.Array.Lemmas

/-!
# Proofs: the shape and the input checks of the cell operations

The sum of two coefficient arrays spans the longer one.

The coset of a cell has a full cell of points.

The batch challenge is a canonical field element.

Each cell operation rejects each malformed input with its own error, before any other work.

A buffer of indices decodes to a list exactly when it holds their 8-byte encodings, in order.

Commitments are ordered by their bytes, with the laws that a search tree needs.
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
    cosetForCell cellIndex = .error (.cellIndexOutOfBounds cellIndex) := by
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

/-! ## The order of commitments -/

/-- Commitments compare as their bytes, so the order is transitive. -/
instance : Std.TransOrd KZGCommitment where
  -- Both laws are those of the order on byte vectors.
  eq_swap := Std.OrientedCmp.eq_swap (cmp := fun a b : Vector UInt8 48 => compare a b)
  isLE_trans := Std.TransCmp.isLE_trans (cmp := fun a b : Vector UInt8 48 => compare a b)

/-- Commitments compare as equal exactly when they are equal. -/
instance : Std.LawfulEqOrd KZGCommitment where
  -- Equal bytes make equal commitments.
  eq_of_compare h :=
    congrArg KZGCommitment.mk
      (Std.LawfulEqCmp.eq_of_compare (cmp := fun a b : Vector UInt8 48 => compare a b) h)

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

/-- Rejects a commitment index that is out of bounds, and names the first one. -/
theorem verifyCellKzgProofBatchImpl_commitmentIndexOutOfBounds (setup : TrustedSetup)
    {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof} {index : CommitmentIndex}
    (hcell : cellIndices.size = commitmentIndices.size)
    (hcoset : cosetsEvals.size = commitmentIndices.size)
    (hproof : proofs.size = commitmentIndices.size)
    (found : commitmentIndices.find? (· ≥ commitments.size) = some index) :
    verifyCellKzgProofBatchImpl setup commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw (.commitmentIndexOutOfBounds index commitments.size) := by
  have h : commitmentIndices.any (· ≥ commitments.size) = true :=
    Base.any_eq_true_of_find?_eq_some found
  simp [verifyCellKzgProofBatchImpl, hcell, hcoset, hproof, h, found, throw_bind]

/-- Rejects a commitments array that contains duplicate entries. -/
theorem verifyCellKzgProofBatchImpl_duplicateCommitments (setup : TrustedSetup)
    {commitments : Array KZGCommitment}
    {commitmentIndices : Array CommitmentIndex} {cellIndices : Array CellIndex}
    {cosetsEvals : Array CosetEvals} {proofs : Array KZGProof}
    (hcell : cellIndices.size = commitmentIndices.size)
    (hcoset : cosetsEvals.size = commitmentIndices.size)
    (hproof : proofs.size = commitmentIndices.size)
    (hcidx : commitmentIndices.any (· ≥ commitments.size) = false)
    {entry : KZGCommitment × Nat}
    (found : commitments.zipIdx.find? (fun (c, i) => commitments.idxOf? c ≠ some i)
      = some entry) :
    verifyCellKzgProofBatchImpl setup commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw (.duplicateCommitments entry.2) := by
  -- The search of the array is the search of its list, so the scan finds the same place.
  have h : Base.firstRepeatIndex commitments.toList = some entry.2 := by
    rw [Base.firstRepeatIndex_eq_find?, ← Array.toList_zipIdx, Array.find?_toList]
    simp only [Array.idxOf?_toList, found, Option.map_some]
  unfold verifyCellKzgProofBatchImpl
  simp [hcell, hcoset, hproof, hcidx, h, throw_bind]

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
    {index : CommitmentIndex}
    (found : commitmentIndices.find? (· ≥ commitments.size) = some index) :
    verifyCellKzgProofBatchImpl setup commitments commitmentIndices cellIndices
        cosetsEvals proofs
      = throw (.commitmentIndexOutOfBounds index commitments.size) :=
  verifyCellKzgProofBatchImpl_commitmentIndexOutOfBounds setup hcell hcoset hproof found

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

/-- Rejects an out-of-bounds cell index in `verifyCellKzgProofBatch`, and names the first one. -/
theorem verifyCellKzgProofBatch_cellIndexOutOfBounds (setup : TrustedSetup)
    {commitmentsBytes : Array Bytes48} {cellIndices : Array CellIndex}
    {cells : Array Cell} {proofsBytes : Array Bytes48} {index : CellIndex}
    (hcells : cells.size = commitmentsBytes.size)
    (hproofs : proofsBytes.size = commitmentsBytes.size)
    (hcidx : cellIndices.size = commitmentsBytes.size)
    (found : cellIndices.find? (· ≥ CELLS_PER_EXT_BLOB) = some index) :
    verifyCellKzgProofBatch setup commitmentsBytes cellIndices cells proofsBytes
      = throw (.cellIndexOutOfBounds index) := by
  have h : cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) = true :=
    Base.any_eq_true_of_find?_eq_some found
  unfold verifyCellKzgProofBatch
  rw [h]
  simp [hcells, hproofs, hcidx, found, throw_bind]

/-- Alias for `verifyCellKzgProofBatch_cellIndexOutOfBounds`. -/
theorem computeVerifyCellKzgProofBatchChallenge_cellIndex_oob (setup : TrustedSetup)
    {commitmentsBytes : Array Bytes48} {cellIndices : Array CellIndex}
    {cells : Array Cell} {proofsBytes : Array Bytes48}
    (hcells : cells.size = commitmentsBytes.size)
    (hproofs : proofsBytes.size = commitmentsBytes.size)
    (hcidx : cellIndices.size = commitmentsBytes.size)
    {index : CellIndex}
    (found : cellIndices.find? (· ≥ CELLS_PER_EXT_BLOB) = some index) :
    verifyCellKzgProofBatch setup commitmentsBytes cellIndices cells proofsBytes
      = throw (.cellIndexOutOfBounds index) :=
  verifyCellKzgProofBatch_cellIndexOutOfBounds setup hcells hproofs hcidx found

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

/-- A buffer of a multiple of 8 bytes decodes to one index per 8 bytes, in order. -/
private theorem unpackIndicesBE_eq_ok_of_mod_eq_zero {b : ByteArray} (h : b.size % 8 = 0) :
    unpackIndicesBE b = .ok ((List.range (b.size / 8)).map fun i =>
      Base.ByteOrder.ofBE ((b.data.toList.drop (i * 8)).take 8)).toArray := by
  unfold unpackIndicesBE
  simp only [h, bne_self_eq_false, Bool.false_eq_true, ite_false]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop, Array.mkEmpty_eq, pure_bind]
  have hsteps : (b.size / 8 - 0 + 1 - 1) / 1 = b.size / 8 := by omega
  have hwidth : ∀ a : Nat, (a + 1) * 8 - a * 8 = 8 := fun a => by omega
  -- The loop pushes one index per step, so it appends the list of the indices.
  simp only [hsteps, hwidth, ← List.range_eq_range', List.foldl_push_eq_append]
  simp
  rfl

/-- A buffer decodes to a list of indices exactly when it is their encodings, in order.

Each index is below `2^64`, and its encoding is 8 bytes, the most significant first.

So the decoding reads all 8 bytes of each index, and drops or adds no byte of the buffer. -/
theorem unpackIndicesBE_eq_ok_iff (b : ByteArray) (xs : Array Nat) :
    unpackIndicesBE b = .ok xs ↔
      (∀ x ∈ xs, x < 2 ^ 64) ∧ b.data.toList
        = xs.toList.flatMap (fun x => (Base.ByteOrder.toBE 8 x).toList) := by
  have h64 : (2 : Nat) ^ 64 = 256 ^ 8 := rfl
  constructor
  · intro hok
    by_cases h : b.size % 8 = 0
    · rw [unpackIndicesBE_eq_ok_of_mod_eq_zero h] at hok
      obtain rfl := (Except.ok.inj hok).symm
      refine ⟨fun x hx => ?_, ?_⟩
      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hx)
        have hlt := Base.ByteOrder.ofBE_lt ((b.data.toList.drop (i * 8)).take 8)
        have hle : 256 ^ ((b.data.toList.drop (i * 8)).take 8).length ≤ 2 ^ 64 :=
          h64 ▸ Nat.pow_le_pow_right (by decide) (List.length_take_le _ _)
        omega
      · have hlen : b.data.toList.length = 8 * (b.size / 8) := by
          rw [Array.length_toList]
          exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h)).symm
        rw [List.toList_toArray, Base.ByteOrder.flatMap_toBE_map_range_ofBE hlen]
    · rw [unpackIndicesBE_bad_size h] at hok
      cases hok
  · rintro ⟨hlt, heq⟩
    have hlen : b.size = 8 * xs.size := by
      have hsize : b.data.toList.length = b.size := Array.length_toList
      rw [← hsize, heq, Base.ByteOrder.length_flatMap_toBE, Array.length_toList]
    rw [unpackIndicesBE_eq_ok_of_mod_eq_zero (by omega), show b.size / 8 = xs.toList.length by
      rw [Array.length_toList]; omega, heq,
      Base.ByteOrder.map_range_ofBE_flatMap_toBE
        fun x hx => h64 ▸ hlt x (Array.mem_toList_iff.mp hx)]

end EthLib.Cryptography.Kzg
