module

public import EthLib.Cryptography.Exports.Kzg
import all EthLib.Cryptography.Exports.Kzg
import all EthLib.Base.Exports.Result
import EthLib.Cryptography.Proofs.Kzg.Cells
import EthLib.Cryptography.Proofs.Kzg.Recovery

/-!
# Proofs: the index bound checks of `Cryptography.Exports.Kzg`

The exports of the cell operations refuse an index out of range with the error that names the first.

That refusal needs each buffer of indices to encode its list, and each earlier check to pass.

The verification and the recovery also need the embedded trusted setup to decode.
-/

public section

namespace EthLib.Cryptography.Kzg.Exports

open EthLib.Exports (toResult)
open EthLib.Cryptography.Kzg.Constants

/-- Buffers that each read and decode as a commitment read together, and each value decodes. -/
private theorem mapM_parseCommitment_exists {commitments : Array ByteArray}
    (hcommitments : ∀ b ∈ commitments, ∃ c, (parseCommitment b >>= bytesToKzgCommitment) = .ok c) :
    ∃ parsed, commitments.mapM parseCommitment = .ok parsed ∧ parsed.size = commitments.size ∧
      ∀ c ∈ parsed, ∃ k, bytesToKzgCommitment c = .ok k := by
  obtain ⟨parsed, hparsed⟩ := Base.array_mapM_exists_ok (f := parseCommitment) fun b hb => by
    obtain ⟨c, hc⟩ := hcommitments b hb
    cases h : parseCommitment b with
    | error e =>
      rw [h] at hc
      cases hc
    | ok y => exact ⟨y, rfl⟩
  refine ⟨parsed, hparsed, (Base.array_mapM_ok hparsed).1, fun c hc => ?_⟩
  obtain ⟨b, hb, hread⟩ := Base.array_mapM_ok_mem hparsed c hc
  obtain ⟨k, hk⟩ := hcommitments b hb
  rw [hread, Base.ok_bind] at hk
  exact ⟨k, hk⟩

/-- The setup that the exports read is the one decoded from the embedded hex. -/
private theorem embeddedSetup_eq_ofHex : embeddedSetup () = TrustedSetup.ofHex := by
  -- A definitional check of this equation took over 6 GiB of memory, so each step rewrites.
  rw [embeddedSetup, embeddedSetupThunk, Thunk.get]

/-- The batch challenge export names the first commitment index past the last commitment, code 11.

Both index buffers must hold the 8-byte big-endian encodings of their indices, each below `2^64`.

The two lists of indices, the coset evaluations and the proofs must have one length.

Each commitment must decode as a point. -/
theorem computeVerifyCellKzgProofBatchChallengeExport_commitmentIndexOutOfBounds
    {commitments : Array ByteArray} {commitmentIndicesBE cellIndicesBE : ByteArray}
    {cosetsEvals proofs : Array ByteArray} {commitmentIndices cellIndices : Array Nat}
    {index : Nat}
    (hcommitmentIndices : (∀ x ∈ commitmentIndices, x < 2 ^ 64) ∧
      commitmentIndicesBE.data.toList =
        commitmentIndices.toList.flatMap fun x => (Base.ByteOrder.toBE 8 x).toList)
    (hcellIndices : (∀ x ∈ cellIndices, x < 2 ^ 64) ∧
      cellIndicesBE.data.toList =
        cellIndices.toList.flatMap fun x => (Base.ByteOrder.toBE 8 x).toList)
    (hcidx : cellIndices.size = commitmentIndices.size)
    (hcosets : cosetsEvals.size = commitmentIndices.size)
    (hproofs : proofs.size = commitmentIndices.size)
    (hcommitments : ∀ b ∈ commitments, ∃ c, (parseCommitment b >>= bytesToKzgCommitment) = .ok c)
    (found : commitmentIndices.find? (· ≥ commitments.size) = some index) :
    computeVerifyCellKzgProofBatchChallengeExport commitments commitmentIndicesBE cellIndicesBE
        cosetsEvals proofs
      = toResult none (.error (KzgError.commitmentIndexOutOfBounds index commitments.size)) := by
  obtain ⟨parsed, hparsed, hsize, decodes⟩ := mapM_parseCommitment_exists hcommitments
  have hany : commitmentIndices.any (· ≥ commitments.size) = true :=
    Base.any_eq_true_of_find?_eq_some found
  unfold computeVerifyCellKzgProofBatchChallengeExport
  simp only [(unpackIndicesBE_eq_ok_iff _ _).mpr hcommitmentIndices,
    (unpackIndicesBE_eq_ok_iff _ _).mpr hcellIndices, hcidx, hcosets, hproofs, hparsed,
    ne_eq, not_true_eq_false, ↓reduceIte, bind, Except.bind]
  -- The read commitments decode, one for each.
  split
  · rename_i heq
    refine absurd heq (Base.array_mapM_ne_error fun x hx => ?_)
    obtain ⟨k, hk⟩ := decodes x.1 (Array.fst_mem_of_mem_zipIdx hx)
    exact ⟨k, by simp only [hk, pure, Except.pure]⟩
  · rename_i decoded heq
    have hdecoded : decoded.size = commitments.size := by
      rw [(Base.array_mapM_ok heq).1, Array.size_zipIdx, hsize]
    simp only [hdecoded, hany, ↓reduceIte, found, Option.getD_some, throw, throwThe,
      MonadExceptOf.throw]

/-- The batch challenge export names the first cell index of 128 or more, code 12.

Both index buffers must hold the 8-byte big-endian encodings of their indices, each below `2^64`.

The two lists of indices, the coset evaluations and the proofs must have one length.

Each commitment must decode as a point, and each commitment index must name a commitment. -/
theorem computeVerifyCellKzgProofBatchChallengeExport_cellIndexOutOfBounds
    {commitments : Array ByteArray} {commitmentIndicesBE cellIndicesBE : ByteArray}
    {cosetsEvals proofs : Array ByteArray} {commitmentIndices cellIndices : Array Nat}
    {index : Nat}
    (hcommitmentIndices : (∀ x ∈ commitmentIndices, x < 2 ^ 64) ∧
      commitmentIndicesBE.data.toList =
        commitmentIndices.toList.flatMap fun x => (Base.ByteOrder.toBE 8 x).toList)
    (hcellIndices : (∀ x ∈ cellIndices, x < 2 ^ 64) ∧
      cellIndicesBE.data.toList =
        cellIndices.toList.flatMap fun x => (Base.ByteOrder.toBE 8 x).toList)
    (hcidx : cellIndices.size = commitmentIndices.size)
    (hcosets : cosetsEvals.size = commitmentIndices.size)
    (hproofs : proofs.size = commitmentIndices.size)
    (hcommitments : ∀ b ∈ commitments, ∃ c, (parseCommitment b >>= bytesToKzgCommitment) = .ok c)
    (hbound : ∀ x ∈ commitmentIndices, x < commitments.size)
    (found : cellIndices.find? (· ≥ CELLS_PER_EXT_BLOB) = some index) :
    computeVerifyCellKzgProofBatchChallengeExport commitments commitmentIndicesBE cellIndicesBE
        cosetsEvals proofs
      = toResult none (.error (KzgError.cellIndexOutOfBounds index)) := by
  obtain ⟨parsed, hparsed, hsize, decodes⟩ := mapM_parseCommitment_exists hcommitments
  have hpass : commitmentIndices.any (· ≥ commitments.size) = false :=
    Array.any_eq_false'.mpr fun x hx => by simpa using hbound x hx
  -- The search over the cell indices stops at their count, the count of commitment indices.
  have hany : cellIndices.any (· ≥ CELLS_PER_EXT_BLOB) 0 commitmentIndices.size = true := by
    rw [← hcidx]
    exact Base.any_eq_true_of_find?_eq_some found
  unfold computeVerifyCellKzgProofBatchChallengeExport
  simp only [(unpackIndicesBE_eq_ok_iff _ _).mpr hcommitmentIndices,
    (unpackIndicesBE_eq_ok_iff _ _).mpr hcellIndices, hcidx, hcosets, hproofs, hparsed,
    ne_eq, not_true_eq_false, ↓reduceIte, bind, Except.bind]
  -- The read commitments decode, one for each.
  split
  · rename_i heq
    refine absurd heq (Base.array_mapM_ne_error fun x hx => ?_)
    obtain ⟨k, hk⟩ := decodes x.1 (Array.fst_mem_of_mem_zipIdx hx)
    exact ⟨k, by simp only [hk, pure, Except.pure]⟩
  · rename_i decoded heq
    have hdecoded : decoded.size = commitments.size := by
      rw [(Base.array_mapM_ok heq).1, Array.size_zipIdx, hsize]
    simp only [hdecoded, hpass, hany, Bool.false_eq_true, ↓reduceIte, found, Option.getD_some,
      throw, throwThe, MonadExceptOf.throw]

/-- The cell verification export names the first cell index of 128 or more, code 12.

It needs the embedded setup to decode, and one cell, one proof and one index per commitment.

Each commitment, cell and proof must have its byte length.

The index buffer must hold the 8-byte big-endian encodings of the indices, each below `2^64`. -/
theorem verifyCellKzgProofBatchExport_cellIndexOutOfBounds {setup : TrustedSetup}
    {commitments : Array ByteArray} {cellIndicesBE : ByteArray} {cells proofs : Array ByteArray}
    {cellIndices : Array Nat} {index : Nat}
    (hsetup : TrustedSetup.ofHex = .ok setup)
    (hcellIndices : (∀ x ∈ cellIndices, x < 2 ^ 64) ∧
      cellIndicesBE.data.toList =
        cellIndices.toList.flatMap fun x => (Base.ByteOrder.toBE 8 x).toList)
    (hcommitmentBytes : ∀ b ∈ commitments, b.size = BYTES_PER_COMMITMENT)
    (hcellBytes : ∀ b ∈ cells, b.size = BYTES_PER_CELL)
    (hproofBytes : ∀ b ∈ proofs, b.size = BYTES_PER_PROOF)
    (hcells : cells.size = commitments.size)
    (hproofs : proofs.size = commitments.size)
    (hcidx : cellIndices.size = commitments.size)
    (found : cellIndices.find? (· ≥ CELLS_PER_EXT_BLOB) = some index) :
    verifyCellKzgProofBatchExport commitments cellIndicesBE cells proofs
      = toResult none (.error (KzgError.cellIndexOutOfBounds index)) := by
  obtain ⟨parsedCommitments, hc⟩ := Base.array_mapM_exists_ok (f := parseCommitment)
    fun b hb => ⟨_, Base.exactBytes_of_size_eq _ (hcommitmentBytes b hb)⟩
  obtain ⟨parsedCells, hce⟩ := Base.array_mapM_exists_ok (f := parseCell)
    fun b hb => ⟨_, Base.exactBytes_of_size_eq _ (hcellBytes b hb)⟩
  obtain ⟨parsedProofs, hp⟩ := Base.array_mapM_exists_ok (f := parseProof)
    fun b hb => ⟨_, Base.exactBytes_of_size_eq _ (hproofBytes b hb)⟩
  have rejected := verifyCellKzgProofBatch_cellIndexOutOfBounds setup
    (by rw [(Base.array_mapM_ok hce).1, (Base.array_mapM_ok hc).1, hcells])
    (by rw [(Base.array_mapM_ok hp).1, (Base.array_mapM_ok hc).1, hproofs])
    (by rw [(Base.array_mapM_ok hc).1, hcidx]) found
  unfold verifyCellKzgProofBatchExport runKzgWithSetup
  simp only [embeddedSetup_eq_ofHex, hsetup, (unpackIndicesBE_eq_ok_iff _ _).mpr hcellIndices,
    hc, hce, hp, rejected, Base.ok_bind]
  rfl

/-- The recovery export names the first cell index of 128 or more, code 12.

It needs the embedded setup to decode, and one cell of its byte length per index.

The index buffer must hold the 8-byte big-endian encodings of the indices, each below `2^64`.

There must be at least half of the cells of an extended blob, and at most all of them. -/
theorem recoverCellsAndKzgProofsExport_cellIndexOutOfBounds {setup : TrustedSetup}
    {cellIndicesBE : ByteArray} {cells : Array ByteArray} {cellIndices : Array Nat} {index : Nat}
    (hsetup : TrustedSetup.ofHex = .ok setup)
    (hcellIndices : (∀ x ∈ cellIndices, x < 2 ^ 64) ∧
      cellIndicesBE.data.toList =
        cellIndices.toList.flatMap fun x => (Base.ByteOrder.toBE 8 x).toList)
    (hcellBytes : ∀ b ∈ cells, b.size = BYTES_PER_CELL)
    (hlen : cells.size = cellIndices.size)
    (hmin : ¬cellIndices.size < CELLS_PER_EXT_BLOB / 2)
    (hmax : ¬cellIndices.size > CELLS_PER_EXT_BLOB)
    (found : cellIndices.find? (· ≥ CELLS_PER_EXT_BLOB) = some index) :
    recoverCellsAndKzgProofsExport cellIndicesBE cells
      = toResult none (.error (KzgError.cellIndexOutOfBounds index)) := by
  obtain ⟨parsedCells, hce⟩ := Base.array_mapM_exists_ok (f := parseCell)
    fun b hb => ⟨_, Base.exactBytes_of_size_eq _ (hcellBytes b hb)⟩
  have rejected := recoverCellsAndKzgProofs_cellIndexOutOfBounds setup
    (by rw [(Base.array_mapM_ok hce).1, hlen]) hmin hmax found
  unfold recoverCellsAndKzgProofsExport runKzgWithSetup
  simp only [embeddedSetup_eq_ofHex, hsetup, (unpackIndicesBE_eq_ok_iff _ _).mpr hcellIndices,
    hce, rejected, Base.ok_bind]
  rfl

end EthLib.Cryptography.Kzg.Exports
