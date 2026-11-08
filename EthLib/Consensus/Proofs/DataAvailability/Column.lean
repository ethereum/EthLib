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

/-- Two lists of commitments whose branches verify for one body root have one root.

Otherwise the two climbs hash two different messages to one SHA-256 output. -/
theorem verifyKzgCommitmentsInclusionProof_binding {preset : Preset} {fork : Fork}
    {first second : BlobKZGCommitments preset fork}
    {firstBranch secondBranch : Vector Bytes32 preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat}
    {bodyRoot : Root}
    (firstValid : verifyKzgCommitmentsInclusionProof preset first firstBranch bodyRoot = true)
    (secondValid : verifyKzgCommitmentsInclusionProof preset second secondBranch bodyRoot = true) :
    ∃ leaf other index, SszType.hashTreeRoot first = .ok leaf ∧
      SszType.hashTreeRoot second = .ok other ∧
      (leaf = other ∨ ∃ a ∈ branchMessages index 0 leaf.toArray
          (firstBranch.toList.map Vector.toArray),
        ∃ b ∈ branchMessages index 0 other.toArray (secondBranch.toList.map Vector.toArray),
          a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
          Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
            Cryptography.Hash.Sha256.hash (ByteArray.mk b)) := by
  unfold verifyKzgCommitmentsInclusionProof at firstValid secondValid
  cases gindex : blobKzgCommitmentsGindex preset fork with
  | error fault => simp [gindex] at firstValid
  | ok g =>
    cases leafRoot : SszType.hashTreeRoot first with
    | error fault => simp [gindex, leafRoot] at firstValid
    | ok leaf =>
      cases otherRoot : SszType.hashTreeRoot second with
      | error fault => simp [gindex, otherRoot] at secondValid
      | ok other =>
        cases subtree : getSubtreeIndex g with
        | error fault => simp [gindex, leafRoot, subtree] at firstValid
        | ok index =>
          simp only [gindex, leafRoot, subtree] at firstValid
          simp only [gindex, otherRoot, subtree] at secondValid
          exact ⟨leaf, other, index, rfl, rfl, isValidMerkleBranch_binding firstValid secondValid⟩

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
  rw [sameRoot] at firstValid
  exact verifyKzgCommitmentsInclusionProof_binding firstValid secondValid

/-- Two partial headers that verify for one body root carry one root of commitments.

Otherwise the two climbs hash two different messages to one SHA-256 output. -/
theorem verifyPartialDataColumnHeaderInclusionProof_binding {preset : Preset} {fork : Fork}
    {first second : PartialDataColumnHeader preset fork}
    (sameRoot : first.signedBlockHeader.message.bodyRoot =
      second.signedBlockHeader.message.bodyRoot)
    (firstValid : verifyPartialDataColumnHeaderInclusionProof preset first = true)
    (secondValid : verifyPartialDataColumnHeaderInclusionProof preset second = true) :
    ∃ leaf other index, SszType.hashTreeRoot first.kzgCommitments = .ok leaf ∧
      SszType.hashTreeRoot second.kzgCommitments = .ok other ∧
      (leaf = other ∨ ∃ a ∈ branchMessages index 0 leaf.toArray
          (first.kzgCommitmentsInclusionProof.toList.map Vector.toArray),
        ∃ b ∈ branchMessages index 0 other.toArray
          (second.kzgCommitmentsInclusionProof.toList.map Vector.toArray),
          a.size = 64 ∧ b.size = 64 ∧ a ≠ b ∧
          Cryptography.Hash.Sha256.hash (ByteArray.mk a) =
            Cryptography.Hash.Sha256.hash (ByteArray.mk b)) := by
  unfold verifyPartialDataColumnHeaderInclusionProof at firstValid secondValid
  rw [sameRoot] at firstValid
  exact verifyKzgCommitmentsInclusionProof_binding firstValid secondValid

instance {preset : Preset} {fork : Fork}
    [NeZero preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat] :
    LawfulSszType (PartialDataColumnHeader preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

/-- The field names of a partial sidecar are distinct at every fork. -/
theorem PartialDataColumnSidecar.names_nodup {fork : Fork} :
    (PartialDataColumnSidecar.names fork).Nodup := by
  have all : (["cells_present_bitmap", "partial_column", "kzg_proofs", "header"] :
      List String).Nodup := by decide
  exact all.sublist ((List.Sublist.refl _).append (untilNames_sublist _))

instance {preset : Preset} {fork : Fork}
    [NeZero preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH.toNat] :
    LawfulSszType (PartialDataColumnSidecar preset fork) :=
  .container
    ⟨by
      by_cases before : fork < Fork.glamsterdam
      · simp [PartialDataColumnSidecar.names, untilNames, SszFields.descs, before]
      · simp [PartialDataColumnSidecar.names, untilNames, SszFields.descs, before],
     by simp [PartialDataColumnSidecar.names],
     firstDuplicate_of_nodup _ PartialDataColumnSidecar.names_nodup⟩
    (fun _ => rfl) (fun _ => rfl)

instance {preset : Preset} {fork : Fork} :
    LawfulSszType (PartialDataColumnPartsMetadata preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

/-- The field names of a group are distinct at every fork. -/
theorem PartialDataColumnGroupID.names_nodup {fork : Fork} :
    (PartialDataColumnGroupID.names fork).Nodup := by
  have all : (["beacon_block_root", "slot"] : List String).Nodup := by decide
  exact all.sublist ((List.Sublist.refl _).append (sinceNames_sublist _))

instance {fork : Fork} : LawfulSszType (PartialDataColumnGroupID fork) :=
  .container
    ⟨by
      by_cases before : fork < Fork.glamsterdam
      · simp [PartialDataColumnGroupID.names, sinceNames, SszFields.descs,
          not_glamsterdam_le before]
      · simp [PartialDataColumnGroupID.names, sinceNames, SszFields.descs,
          not_lt_glamsterdam before],
     by simp [PartialDataColumnGroupID.names],
     firstDuplicate_of_nodup _ PartialDataColumnGroupID.names_nodup⟩
    (fun _ => rfl) (fun _ => rfl)

/-- A bitmap with every bit set names every blob, in order. -/
theorem PartialDataColumnSidecar.blobIndices_of_all {preset : Preset} {fork : Fork}
    {sidecar : PartialDataColumnSidecar preset fork}
    (all : ∀ bit ∈ sidecar.cellsPresentBitmap.bits, bit = true) :
    sidecar.blobIndices = Array.range sidecar.cellsPresentBitmap.bits.size := by
  unfold PartialDataColumnSidecar.blobIndices
  rw [Array.filter_eq_self.mpr fun x member => all x.1 (Array.fst_mem_of_mem_zipIdx member)]
  exact Array.ext (by simp) fun i _ _ => by simp

/-- With every bit set and one bit per blob, the partial check is the check of a whole column.

So a partial sidecar that carries every cell passes exactly when the full column would. -/
theorem verifyPartialDataColumnSidecarKzgProofs_of_all {preset : Preset} {fork : Fork}
    {setup : Cryptography.Kzg.TrustedSetup} {sidecar : PartialDataColumnSidecar preset fork}
    {commitments : BlobKZGCommitments preset fork} {columnIndex : DataAvailability.ColumnIndex}
    (all : ∀ bit ∈ sidecar.cellsPresentBitmap.bits, bit = true)
    (oneEach : sidecar.cellsPresentBitmap.bits.size = commitments.data.size) :
    verifyPartialDataColumnSidecarKzgProofs setup sidecar commitments columnIndex =
      Cryptography.Kzg.verifyCellKzgProofBatch setup commitments.data
        (Array.replicate commitments.data.size columnIndex.toNat) sidecar.partialColumn.data
        sidecar.kzgProofs.data := by
  unfold verifyPartialDataColumnSidecarKzgProofs
  rw [PartialDataColumnSidecar.blobIndices_of_all all, oneEach]
  -- Every index below the count has its commitment, so the lookup gives the list back.
  have fetched : ∀ indices : List Nat, (∀ i ∈ indices, i < commitments.data.size) →
      indices.mapM (fun index =>
        if inside : index < commitments.data.size then
          (pure commitments.data[index] : Except Cryptography.Kzg.KzgError _)
        else throw .commitmentIndexOutOfBounds) =
        pure (indices.map fun i => commitments.data[i]!) := by
    intro indices inside
    induction indices with
    | nil => rfl
    | cons i rest ih =>
      have here : i < commitments.data.size := inside i (by simp)
      rw [List.mapM_cons, ih fun j member => inside j (by simp [member])]
      simp [here, getElem!_pos]
  have whole : (List.range commitments.data.size).map (fun i => commitments.data[i]!) =
      commitments.data.toList :=
    List.ext_getElem (by simp) fun i inside _ => by
      simp only [List.length_map, List.length_range] at inside
      simp [getElem!_pos commitments.data i inside]
  simp only [Array.mapM_eq_mapM_toList, Array.toList_range, Array.size_range]
  rw [fetched _ fun i member => List.mem_range.mp member, whole]
  rfl

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

/-- The entries of a row of 128 cells and 128 proofs: one for each column, in order. -/
theorem matrixRow_eq_finRange (row : RowIndex) {cells : Array Cell} {proofs : Array KZGProof}
    (cellsSize : cells.size = CELLS_PER_EXT_BLOB) (proofsSize : proofs.size = CELLS_PER_EXT_BLOB) :
    matrixRow row cells proofs =
      (List.finRange CELLS_PER_EXT_BLOB).map fun c =>
        ⟨cells[c.val]'(by simp [cellsSize]), proofs[c.val]'(by simp [proofsSize]),
          c.val.toUInt64, row⟩ := by
  unfold matrixRow
  apply List.ext_getElem (by simp [cellsSize, proofsSize])
  intro i _ _
  simp

/-- The entries of a row that a filter of columns keeps: one for each kept column, in order.

The row has 128 cells and 128 proofs. -/
theorem filter_matrixRow (keep : DataAvailability.ColumnIndex → Bool) (row : RowIndex)
    {cells : Array Cell} {proofs : Array KZGProof}
    (cellsSize : cells.size = CELLS_PER_EXT_BLOB) (proofsSize : proofs.size = CELLS_PER_EXT_BLOB) :
    (matrixRow row cells proofs).filter (fun e => keep e.columnIndex) =
      ((List.finRange CELLS_PER_EXT_BLOB).filter fun c => keep c.val.toUInt64).map fun c =>
        ⟨cells[c.val]'(by simp [cellsSize]), proofs[c.val]'(by simp [proofsSize]),
          c.val.toUInt64, row⟩ := by
  rw [matrixRow_eq_finRange row cellsSize proofsSize, List.filter_map]
  rfl

/-- The kept entries of a row that FK20 computes, read by column index. -/
private theorem filter_matrixRow_fk20 (keep : DataAvailability.ColumnIndex → Bool)
    (row : RowIndex) (setup : TrustedSetup) {p : PolynomialCoeff}
    (hp : p.size = FIELD_ELEMENTS_PER_BLOB) :
    (matrixRow row (fk20CellsAndProofs setup p).1 (fk20CellsAndProofs setup p).2).filter
        (fun e => keep e.columnIndex) =
      ((List.range CELLS_PER_EXT_BLOB).filter fun c => keep c.toUInt64).map fun c =>
        ⟨(fk20CellsAndProofs setup p).1[c]!, (fk20CellsAndProofs setup p).2[c]!, c.toUInt64,
          row⟩ := by
  obtain ⟨cellsSize, proofsSize⟩ :=
    size_fk20CellsAndProofs setup (polynomialCoeff := p) (by rw [hp]; decide)
  have range : List.range CELLS_PER_EXT_BLOB = (List.finRange CELLS_PER_EXT_BLOB).map Fin.val :=
    List.ext_getElem (by simp) (by simp)
  rw [filter_matrixRow keep row cellsSize proofsSize, range, List.filter_map, List.map_map]
  apply List.map_congr_left
  intro c _
  simp [getElem!_pos, cellsSize, proofsSize]

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
    obtain ⟨p, hp, hpk⟩ := hrow k hk'
    simp only [Function.comp, getElem!_pos rows k (hlen ▸ hk'), hpk, filter_matrixRow_fk20 _ _ _ hp]
    by_cases same : k = j
    · subst same
      simp only [↓reduceIte]
      rw [getElem!_pos rows k (hlen ▸ hk'), hpk,
        filter_matrixRow_fk20 _ _ _ hp, List.filter_eq_self.mpr]
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
  simp only [hselect j hj', getElem!_pos rows j (hlen ▸ hj'), hpj, filter_matrixRow_fk20 _ _ _ hp,
    List.map_map]
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
