module

public import EthLib.Consensus.DataAvailability.Column
public import EthLib.Consensus.Proofs.Containers.Block
public import EthLib.Consensus.Proofs.DataAvailability.Blob
public import EthLib.Serialization.Proofs.Ssz.Typed.ForkKind
public import EthLib.Serialization.Proofs.Ssz.Typed.Since
public import EthLib.Cryptography.Proofs.Kzg.RecoveryRoundTrip
public import EthLib.Cryptography.Proofs.Kzg.PeerDasColumnGames

/-!
# Proofs: the data column sidecars

Each container has distinct field names, and converts to and from its fields.

So its bytes decode back to it.

Two sidecars whose branches verify for one body root carry one root of commitments.

Otherwise the two climbs to the body root hash two different messages to one SHA-256 output.

The check of the proofs of a sidecar is the batch check of one column.

The games of columns of PeerDAS state position-binding and code-binding for that check.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

instance : NeZero Cryptography.Kzg.Constants.BYTES_PER_CELL := ⟨by decide⟩

/-- The field names of a sidecar are distinct at every fork. -/
theorem DataColumnSidecar.names_nodup {fork : Fork} : (DataColumnSidecar.names fork).Nodup := by
  have all : (["index", "column", "kzg_commitments", "kzg_proofs", "signed_block_header",
      "kzg_commitments_inclusion_proof", "slot", "beacon_block_root"] : List String).Nodup := by
    decide
  refine all.sublist ?_
  unfold DataColumnSidecar.names
  exact ((((List.Sublist.refl ["index", "column"]).append (untilNames_sublist _)).append
    (List.Sublist.refl _)).append (untilNames_sublist _)).append (sinceNames_sublist _)

instance {preset : Preset} {fork : Fork}
    [NeZero preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat] :
    LawfulSszType (DataColumnSidecar preset fork) :=
  .container
    ⟨by
      by_cases before : fork < Fork.glamsterdam
      · simp [DataColumnSidecar.names, sinceNames, untilNames, SszFields.descs, before,
          not_glamsterdam_le before]
      · simp [DataColumnSidecar.names, sinceNames, untilNames, SszFields.descs, before,
          not_lt_glamsterdam before],
     by simp [DataColumnSidecar.names],
     firstDuplicate_of_nodup _ DataColumnSidecar.names_nodup⟩
    (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType MatrixEntry := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance {preset : Preset} : LawfulSszType (DataColumnsByRootIdentifier preset) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

/-- Two sidecars that verify for one body root carry one root of commitments.

Otherwise the two climbs hash two different messages to one SHA-256 output. -/
theorem verifyDataColumnSidecarInclusionProof_binding {preset : Preset} {fork : Fork}
    {beforeGloas : fork < .glamsterdam} {first second : DataColumnSidecar preset fork}
    (sameRoot : (first.signedBlockHeader beforeGloas).message.bodyRoot =
      (second.signedBlockHeader beforeGloas).message.bodyRoot)
    (firstValid : verifyDataColumnSidecarInclusionProof preset beforeGloas first = true)
    (secondValid : verifyDataColumnSidecarInclusionProof preset beforeGloas second = true) :
    ∃ leaf other index, SszType.hashTreeRoot (first.kzgCommitments beforeGloas) = .ok leaf ∧
      SszType.hashTreeRoot (second.kzgCommitments beforeGloas) = .ok other ∧
      (leaf = other ∨ ∃ a ∈ branchMessages index 0 leaf.toArray
          ((first.kzgCommitmentsInclusionProof beforeGloas).toList.map Vector.toArray),
        ∃ b ∈ branchMessages index 0 other.toArray
          ((second.kzgCommitmentsInclusionProof beforeGloas).toList.map Vector.toArray),
          a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
          Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
            Cryptography.Hash.Sha256.hash (ByteArray.mk b)) := by
  unfold verifyDataColumnSidecarInclusionProof at firstValid secondValid
  cases gindex : blobKzgCommitmentsGindex preset fork with
  | error fault => simp [gindex] at firstValid
  | ok g =>
    cases leafRoot : SszType.hashTreeRoot (first.kzgCommitments beforeGloas) with
    | error fault => simp [gindex, leafRoot] at firstValid
    | ok leaf =>
      cases otherRoot : SszType.hashTreeRoot (second.kzgCommitments beforeGloas) with
      | error fault => simp [gindex, otherRoot] at secondValid
      | ok other =>
        cases subtree : getSubtreeIndex g with
        | error fault => simp [gindex, leafRoot, subtree] at firstValid
        | ok index =>
          simp only [gindex, leafRoot, subtree] at firstValid
          simp only [gindex, otherRoot, subtree, ← sameRoot] at secondValid
          exact ⟨leaf, other, index, rfl, rfl, isValidMerkleBranch_binding firstValid secondValid⟩

/-- At Fulu and the BPO forks, the depth of the inclusion proof is that of the commitment list.

The depth of a node is the floor of the base-2 logarithm of its generalized index.

The generalized index comes from the type of the body at the fork. -/
theorem kzgCommitmentsInclusionProofDepth_eq {preset : Preset} {fork : Fork}
    (named : preset = .mainnet ∨ preset = .minimal) (fulu : .fusaka ≤ fork)
    (beforeGloas : fork < .glamsterdam) :
    ∃ gindex, blobKzgCommitmentsGindex preset fork = .ok gindex ∧
      Nat.log2 gindex = preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat := by
  suffices computed : (blobKzgCommitmentsGindex preset fork).toOption = some 27 by
    refine ⟨27, ?_, ?_⟩
    · cases h : blobKzgCommitmentsGindex preset fork <;> simp_all [Except.toOption]
    · rcases named with rfl | rfl <;> rfl
  rcases named with rfl | rfl <;> cases fork <;> first
    | exact absurd fulu (by decide) | exact absurd beforeGloas (by decide) | decide +kernel

section Matrix

open Cryptography.Kzg Cryptography.Kzg.Constants

/-- A computed blob gives the cells and proofs of a polynomial of 4096 coefficients. -/
theorem computeCellsAndKzgProofs_ok_fk20 {setup : TrustedSetup} {blob : Blob}
    {result : Array Cell × Array KZGProof}
    (computed : computeCellsAndKzgProofs setup blob = .ok result) :
    ∃ p : PolynomialCoeff, p.size = FIELD_ELEMENTS_PER_BLOB ∧
      result = fk20CellsAndProofs setup p := by
  cases decoded : blobToPolynomial blob with
  | error e =>
    unfold computeCellsAndKzgProofs at computed
    rw [decoded] at computed
    cases computed
  | ok poly =>
    rw [computeCellsAndKzgProofs_ok_eq setup decoded] at computed
    refine ⟨polynomialEvalToCoeff poly, ?_, (Except.ok.inj computed).symm⟩
    rw [size_polynomialEvalToCoeff, size_blobToPolynomial blob poly decoded]

/-- The flattened list of rows that are empty except one is that one row. -/
theorem flatten_map_range_ite {α : Type} (row : List α) {i n : Nat} (inside : i < n) :
    ((List.range n).map fun j => if j = i then row else []).flatten = row := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.flatten_append]
    by_cases last : i = n
    · subst last
      have empty : ((List.range i).map fun j => if j = i then row else []).flatten = [] := by
        rw [List.flatten_eq_nil_iff]
        intro l member
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp member
        simp [Nat.ne_of_lt (List.mem_range.mp hj)]
      simp [empty]
    · rw [ih (by omega)]
      simp [Ne.symm last]

/-- A strictly ascending list of indices passes the order check of recovery. -/
theorem ascending_check_false {indices : List Nat} (sorted : indices.Pairwise (· < ·)) :
    (Array.range (indices.toArray.size - 1)).any
      (fun i => indices.toArray[i + 1]! ≤ indices.toArray[i]!) = false := by
  rw [Array.any_eq_false]
  intro i hi
  simp only [Array.size_range, List.size_toArray] at hi
  have hlt := List.pairwise_iff_getElem.mp sorted i (i + 1) (by omega) (by omega) (by omega)
  simp only [Array.getElem_range, decide_eq_true_eq, not_le]
  rw [getElem!_pos _ i (by simp; omega), getElem!_pos _ (i + 1) (by simp; omega)]
  simpa using hlt

private theorem toNat_toUInt64_of_lt {n : Nat} (small : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' small]

/-- The entries of a row that a filter of columns keeps: one for each kept column, in order. -/
theorem filter_matrixRow (keep : DataAvailability.ColumnIndex → Bool) (row : RowIndex)
    (cells : Array Cell) (proofs : Array KZGProof) :
    (matrixRow row cells proofs).filter (fun e => keep e.columnIndex) =
      ((List.range CELLS_PER_EXT_BLOB).filter fun c => keep c.toUInt64).map fun c =>
        ⟨cells[c]!, proofs[c]!, c.toUInt64, row⟩ := by
  unfold matrixRow
  rw [List.filter_map]
  rfl

/-- Recovering the matrix of some blobs from the columns that a filter keeps gives the matrix.

The filter must keep at least half of the 128 columns.

The number of blobs fits in 64 bits, the type of a row index. -/
theorem recoverMatrix_computeMatrix {setup : TrustedSetup} {blobs : List Blob}
    {matrix : List MatrixEntry} (computed : computeMatrix setup blobs = .ok matrix)
    (keep : DataAvailability.ColumnIndex → Bool)
    (enough : CELLS_PER_EXT_BLOB / 2 ≤
      ((List.range CELLS_PER_EXT_BLOB).filter fun c => keep c.toUInt64).length)
    (fits : blobs.length < 2 ^ 64) :
    recoverMatrix setup (matrix.filter fun e => keep e.columnIndex) blobs.length.toUInt64 =
      .ok matrix := by
  cases computedRows : blobs.zipIdx.mapM fun (blob, row) => computeMatrixRow setup blob row with
  | error e =>
    rw [computeMatrix, computedRows] at computed
    cases computed
  | ok rows =>
  rw [computeMatrix, computedRows] at computed
  cases computed
  -- Each row of the matrix holds the cells and proofs of a polynomial of 4096 coefficients.
  have hlen : rows.length = blobs.length := by
    have := Base.mapM_ok_length computedRows
    simp only [List.length_zipIdx] at this
    omega
  have hrow : ∀ i (hi : i < blobs.length), ∃ p : PolynomialCoeff,
      p.size = FIELD_ELEMENTS_PER_BLOB ∧
      rows[i]'(hlen ▸ hi) =
        matrixRow i.toUInt64 (fk20CellsAndProofs setup p).1 (fk20CellsAndProofs setup p).2 := by
    intro i hi
    have step := Base.mapM_ok_getElem computedRows i (by rw [List.length_zipIdx]; exact hi)
    simp only [List.getElem_zipIdx, Nat.zero_add, computeMatrixRow] at step
    cases computedCp : computeCellsAndKzgProofs setup blobs[i] with
    | error e =>
      rw [computedCp] at step
      cases step
    | ok cp =>
      rw [computedCp] at step
      obtain ⟨p, hp, rfl⟩ := computeCellsAndKzgProofs_ok_fk20 computedCp
      exact ⟨p, hp, (Except.ok.inj step).symm⟩
  -- Row `j` of the kept entries is the part of row `j` of the matrix that the filter keeps.
  have hselect : ∀ j < blobs.length,
      ((rows.flatten.filter fun e => keep e.columnIndex).filter
          fun e => decide (e.rowIndex = j.toUInt64)) =
        rows[j]!.filter fun e => keep e.columnIndex := by
    intro j hj
    have hrows : rows.flatten = ((List.range blobs.length).map fun k => rows[k]!).flatten := by
      congr 1
      apply List.ext_getElem (by simp [hlen])
      intro k h₁ h₂
      simp only [List.getElem_map, List.getElem_range]
      rw [getElem!_pos rows k h₁]
    rw [hrows, List.filter_flatten, List.filter_flatten, List.map_map, List.map_map]
    rw [← flatten_map_range_ite (rows[j]!.filter fun e => keep e.columnIndex) hj]
    congr 1
    apply List.map_congr_left
    intro k hk
    have hk' := List.mem_range.mp hk
    obtain ⟨p, _, hpk⟩ := hrow k hk'
    simp only [Function.comp, getElem!_pos rows k (hlen ▸ hk'), hpk, filter_matrixRow]
    by_cases same : k = j
    · subst same
      simp only [↓reduceIte]
      rw [getElem!_pos rows k (hlen ▸ hk'), hpk,
        filter_matrixRow, List.filter_eq_self.mpr]
      intro e he
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp he
      simp
    · simp only [same, ↓reduceIte]
      rw [List.filter_eq_nil_iff]
      intro e he
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp he
      have differ : k.toUInt64 ≠ j.toUInt64 := fun eq => same (by
        have := congrArg UInt64.toNat eq
        rwa [toNat_toUInt64_of_lt (by omega), toNat_toUInt64_of_lt (by omega)] at this)
      simpa using differ
  -- The kept columns are ascending and below 128.
  have hkeptlt : ∀ c ∈ (List.range CELLS_PER_EXT_BLOB).filter (fun c => keep c.toUInt64),
      c < CELLS_PER_EXT_BLOB := fun c hc => List.mem_range.mp (List.mem_filter.mp hc).1
  have hsorted : ((List.range CELLS_PER_EXT_BLOB).filter fun c => keep c.toUInt64).Pairwise
      (· < ·) := List.pairwise_lt_range.filter _
  unfold recoverMatrix
  rw [toNat_toUInt64_of_lt fits]
  rw [Base.mapM_eq_ok_map (g := fun j => rows[j]!) ?_]
  · have hrows : ((List.range blobs.length).map fun j => rows[j]!) = rows := by
      apply List.ext_getElem (by simp [hlen])
      intro k h₁ h₂
      simp only [List.getElem_map, List.getElem_range]
      rw [getElem!_pos rows k h₂]
    rw [hrows]
    rfl
  intro j hj
  have hj' := List.mem_range.mp hj
  obtain ⟨p, hp, hpj⟩ := hrow j hj'
  simp only [hselect j hj', getElem!_pos rows j (hlen ▸ hj'), hpj, filter_matrixRow, List.map_map]
  have hidx : List.map ((fun x => UInt64.toNat x.columnIndex) ∘ fun c =>
      (⟨(fk20CellsAndProofs setup p).1[c]!, (fk20CellsAndProofs setup p).2[c]!, c.toUInt64,
        j.toUInt64⟩ : MatrixEntry))
      ((List.range CELLS_PER_EXT_BLOB).filter fun c => keep c.toUInt64) =
      (List.range CELLS_PER_EXT_BLOB).filter fun c => keep c.toUInt64 := by
    conv_rhs => rw [← List.map_id ((List.range CELLS_PER_EXT_BLOB).filter fun c => keep c.toUInt64)]
    apply List.map_congr_left
    intro c hc
    exact toNat_toUInt64_of_lt (Nat.lt_trans (hkeptlt c hc) (by decide))
  have hcells : (List.map ((fun x => x.cell) ∘ fun c =>
      (⟨(fk20CellsAndProofs setup p).1[c]!, (fk20CellsAndProofs setup p).2[c]!, c.toUInt64,
        j.toUInt64⟩ : MatrixEntry))
      ((List.range CELLS_PER_EXT_BLOB).filter fun c => keep c.toUInt64)).toArray =
      ((List.range CELLS_PER_EXT_BLOB).filter fun c => keep c.toUInt64).toArray.map
        fun c => (fk20CellsAndProofs setup p).1[c]! := by
    simp
  have hbound : ((List.range CELLS_PER_EXT_BLOB).filter fun c => keep c.toUInt64).toArray.any
      (· ≥ CELLS_PER_EXT_BLOB) = false := by
    rw [Array.any_eq_false]
    intro i hi
    simpa using hkeptlt _ (List.getElem_mem (by simpa using hi))
  rw [hidx, hcells, recoverCellsAndKzgProofs_fk20 setup hp (by simpa using enough) hbound
    (ascending_check_false hsorted)]
  rfl

/-- **The check of the proofs of a sidecar is the batch check of its column.**

The column holds the commitments of the sidecar, its index, its cells and its proofs.

Before Gloas, the type of the commitments allows at most `MAX_BLOB_COMMITMENTS_PER_BLOCK` of them.

A check that returns a verdict has as many cells as commitments, so the column has at most as many.
-/
theorem verifyDataColumnSidecarKzgProofs_eq_verify {preset : Preset} {fork : Fork}
    (setup : TrustedSetup) (sidecar : DataColumnSidecar preset fork)
    (bidCommitments : Since .glamsterdam fork (BlobKZGCommitments preset fork)) :
    verifyDataColumnSidecarKzgProofs setup sidecar bidCommitments =
      ColumnBatch.verify setup ⟨(sidecar.commitments bidCommitments).data, sidecar.index.toNat,
        sidecar.column.data, sidecar.kzgProofs.data⟩ :=
  rfl

end Matrix

end EthLib.Consensus
