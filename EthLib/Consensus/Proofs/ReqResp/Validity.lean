module

public import EthLib.Consensus.ReqResp.Validity

/-!
# `Consensus.Proofs.ReqResp.Validity`

What the validity of a response says about its blocks or sidecars.

- A valid response to a request for blocks by range has at most the count of blocks.
- Its blocks lie in the requested slots, with slots that increase along the whole list.
- When the step is 1, each block names the one before it as its parent, so the blocks form a chain.
- A valid response to a request for blocks by root has at most as many blocks as requested roots.
- The root of each of its blocks is a requested root.
- A valid response to a request for sidecars by range lies in the requested slots.
- Along the whole list, its sidecars increase in slot, then in index within one block.
- Two of its sidecars at the same slot name the same block.
- For blobs, the indices of the sidecars of one block are 0, 1, 2 and so on.
- For columns, each index is a requested column.
- A valid response to a request for sidecars by root has at most as many sidecars as requested.
- Each of its sidecars is one that the request names.
-/

@[expose] public section

namespace EthLib.Consensus.Proofs.ReqResp.Validity

open EthLib.Consensus

/-- The slots of a list increase from each block to the next exactly when the check passes. -/
theorem slotsAscending_iff (blocks : List ResponseBlock) :
    ResponseBlock.slotsAscending blocks = true ↔
      ∀ i (h : i + 1 < blocks.length), blocks[i].slot < blocks[i + 1].slot := by
  induction blocks with
  | nil => simp [ResponseBlock.slotsAscending]
  | cons a rest ih =>
    cases rest with
    | nil => simp [ResponseBlock.slotsAscending]
    | cons b rest =>
      simp only [ResponseBlock.slotsAscending, Bool.and_eq_true, decide_eq_true_eq, ih]
      constructor
      · rintro ⟨first, next⟩ i h
        cases i with
        | zero => simpa using first
        | succ i => exact next i (by simp at h ⊢; omega)
      · intro all
        exact ⟨by simpa using all 0 (by simp),
          fun i h => all (i + 1) (by simp at h ⊢; omega)⟩

/-- Each block of a list names the one before it as its parent exactly when the check passes. -/
theorem parentsLinked_iff (blocks : List ResponseBlock) :
    ResponseBlock.parentsLinked blocks = true ↔
      ∀ i (h : i + 1 < blocks.length), blocks[i + 1].parentRoot = blocks[i].root := by
  induction blocks with
  | nil => simp [ResponseBlock.parentsLinked]
  | cons a rest ih =>
    cases rest with
    | nil => simp [ResponseBlock.parentsLinked]
    | cons b rest =>
      simp only [ResponseBlock.parentsLinked, Bool.and_eq_true, beq_iff_eq, ih]
      constructor
      · rintro ⟨first, next⟩ i h
        cases i with
        | zero => simpa using first
        | succ i => exact next i (by simp at h ⊢; omega)
      · intro all
        exact ⟨by simpa using all 0 (by simp),
          fun i h => all (i + 1) (by simp at h ⊢; omega)⟩

/-- When the slots increase from each block to the next, they increase along the whole list. -/
theorem pairwise_of_slotsAscending {blocks : List ResponseBlock}
    (ascending : ResponseBlock.slotsAscending blocks = true) :
    blocks.Pairwise (fun a b => a.slot < b.slot) := by
  induction blocks with
  | nil => exact List.Pairwise.nil
  | cons a rest ih =>
    cases rest with
    | nil => exact List.pairwise_singleton _ _
    | cons b rest =>
      simp only [ResponseBlock.slotsAscending, Bool.and_eq_true, decide_eq_true_eq] at ascending
      have tail := ih ascending.2
      refine List.Pairwise.cons ?_ tail
      intro c mem
      rcases List.mem_cons.mp mem with rfl | mem
      · exact ascending.1
      · exact UInt64.lt_trans ascending.1 (List.rel_of_pairwise_cons tail mem)

/-- The rules that a valid response to a request for blocks by range meets, and no others. -/
theorem isValidBlocksByRangeResponse_iff (config : Config) (fork : Base.Fork)
    (request : BeaconBlocksByRangeRequest) (blocks : List ResponseBlock) :
    isValidBlocksByRangeResponse config fork request blocks = true ↔
      blocks.length ≤ request.count.toNat ∧
      blocks.length ≤ (config.maxRequestBlocks fork).toNat ∧
      (∀ block ∈ blocks, request.startSlot.toNat ≤ block.slot.toNat ∧
        block.slot.toNat < request.startSlot.toNat + request.count.toNat) ∧
      (∀ i (h : i + 1 < blocks.length), blocks[i].slot < blocks[i + 1].slot) ∧
      (request.step = 1 →
        ∀ i (h : i + 1 < blocks.length), blocks[i + 1].parentRoot = blocks[i].root) := by
  simp only [isValidBlocksByRangeResponse, BeaconBlocksByRangeRequest.containsSlot,
    Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, List.all_eq_true,
    slotsAscending_iff, parentsLinked_iff, slotInRange, UInt64.le_iff_toNat_le, and_assoc,
    Decidable.imp_iff_not_or]

/-- A valid response to a request for blocks by range with step 1 is a chain in the requested slots.

It has at most the count of blocks, and its slots increase along the whole list. -/
theorem chain_of_isValidBlocksByRangeResponse {config : Config} {fork : Base.Fork}
    {request : BeaconBlocksByRangeRequest} {blocks : List ResponseBlock}
    (valid : isValidBlocksByRangeResponse config fork request blocks = true)
    (step : request.step = 1) :
    blocks.length ≤ request.count.toNat ∧
      (∀ block ∈ blocks, request.startSlot.toNat ≤ block.slot.toNat ∧
        block.slot.toNat < request.startSlot.toNat + request.count.toNat) ∧
      blocks.Pairwise (fun a b => a.slot < b.slot) ∧
      ∀ i (h : i + 1 < blocks.length), blocks[i + 1].parentRoot = blocks[i].root := by
  obtain ⟨count, -, slots, ascending, linked⟩ :=
    (isValidBlocksByRangeResponse_iff config fork request blocks).mp valid
  exact ⟨count, slots, pairwise_of_slotsAscending ((slotsAscending_iff blocks).mpr ascending),
    linked step⟩

/-- The rules that a valid response to a request for blocks by root meets, and no others. -/
theorem isValidBlocksByRootResponse_iff {config : Config} {fork : Base.Fork}
    (request : BeaconBlocksByRootRequest config fork) (blocks : List ResponseBlock) :
    isValidBlocksByRootResponse request blocks = true ↔
      blocks.length ≤ request.data.size ∧ ∀ block ∈ blocks, block.root ∈ request.data := by
  simp [isValidBlocksByRootResponse, List.all_eq_true]

/-- A relation holds between each item and the next exactly when the check passes. -/
theorem allAdjacent_iff {α : Type} (r : α → α → Bool) (items : List α) :
    allAdjacent r items = true ↔
      ∀ i (h : i + 1 < items.length), r items[i] items[i + 1] = true := by
  induction items with
  | nil => simp [allAdjacent]
  | cons a rest ih =>
    cases rest with
    | nil => simp [allAdjacent]
    | cons b rest =>
      simp only [allAdjacent, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨first, next⟩ i h
        cases i with
        | zero => simpa using first
        | succ i => exact next i (by simp at h ⊢; omega)
      · intro all
        exact ⟨by simpa using all 0 (by simp),
          fun i h => all (i + 1) (by simp at h ⊢; omega)⟩

/-- When each item relates to the next, a transitive relation that follows holds along the list. -/
theorem pairwise_of_allAdjacent {α : Type} {r : α → α → Bool} {s : α → α → Prop}
    (step : ∀ a b, r a b = true → s a b) (trans : ∀ a b c, s a b → s b c → s a c)
    {items : List α} (adjacent : allAdjacent r items = true) : items.Pairwise s := by
  induction items with
  | nil => exact List.Pairwise.nil
  | cons a rest ih =>
    cases rest with
    | nil => exact List.pairwise_singleton _ _
    | cons b rest =>
      simp only [allAdjacent, Bool.and_eq_true] at adjacent
      have tail := ih adjacent.2
      refine List.Pairwise.cons ?_ tail
      intro c mem
      rcases List.mem_cons.mp mem with rfl | mem
      · exact step _ _ adjacent.1
      · exact trans _ _ _ (step _ _ adjacent.1) (List.rel_of_pairwise_cons tail mem)

/-- A slot lies in a range exactly when it is at least the start and below the start plus count. -/
theorem slotInRange_iff (startSlot : Slot) (count : UInt64) (slot : Slot) :
    slotInRange startSlot count slot = true ↔
      startSlot.toNat ≤ slot.toNat ∧ slot.toNat < startSlot.toNat + count.toNat := by
  simp [slotInRange, UInt64.le_iff_toNat_le]

/-- A blob sidecar may follow another exactly when it is the next blob of the same block.

It may also be the first blob of a block at a later slot. -/
theorem nextBlob_iff (a b : ResponseSidecar) :
    ResponseSidecar.nextBlob a b = true ↔
      (a.slot = b.slot ∧ b.blockRoot = a.blockRoot ∧ b.index.toNat = a.index.toNat + 1) ∨
        (a.slot < b.slot ∧ b.index = 0) := by
  unfold ResponseSidecar.nextBlob
  by_cases same : a.slot = b.slot
  · simp [same]
  · simp [same]

/-- A column sidecar may follow another exactly when it is a later column of the same block.

It may also belong to a block at a later slot. -/
theorem nextColumn_iff (a b : ResponseSidecar) :
    ResponseSidecar.nextColumn a b = true ↔
      (a.slot = b.slot ∧ b.blockRoot = a.blockRoot ∧ a.index < b.index) ∨ a.slot < b.slot := by
  unfold ResponseSidecar.nextColumn
  by_cases same : a.slot = b.slot
  · simp [same]
  · simp [same]

/-- One sidecar comes before another: at a lower slot, or in the same block with a lower index. -/
def SidecarBefore (a b : ResponseSidecar) : Prop :=
  a.slot < b.slot ∨ (a.slot = b.slot ∧ a.blockRoot = b.blockRoot ∧ a.index < b.index)

/-- Coming before is transitive. -/
theorem sidecarBefore_trans (a b c : ResponseSidecar) :
    SidecarBefore a b → SidecarBefore b c → SidecarBefore a c := by
  rintro (ab | ⟨ab, rab, iab⟩) (bc | ⟨bc, rbc, ibc⟩)
  · exact Or.inl (UInt64.lt_trans ab bc)
  · exact Or.inl (bc ▸ ab)
  · exact Or.inl (ab ▸ bc)
  · exact Or.inr ⟨ab.trans bc, rab.trans rbc, UInt64.lt_trans iab ibc⟩

/-- The rules that a valid response to a request for blob sidecars by range meets, and no others. -/
theorem isValidBlobSidecarsByRangeResponse_iff (config : Config) (fork : Base.Fork)
    (request : BlobSidecarsByRangeRequest) (sidecars : List ResponseSidecar) :
    isValidBlobSidecarsByRangeResponse config fork request sidecars = true ↔
      sidecars.length ≤ request.count.toNat * (config.maxRequestBlobsPerBlock fork).toNat ∧
      sidecars.length ≤ (computeMaxRequestBlobSidecars config fork).toNat ∧
      (∀ sidecar ∈ sidecars, request.startSlot.toNat ≤ sidecar.slot.toNat ∧
        sidecar.slot.toNat < request.startSlot.toNat + request.count.toNat) ∧
      (∀ h : 0 < sidecars.length, sidecars[0].index = 0) ∧
      (∀ i (h : i + 1 < sidecars.length),
        (sidecars[i].slot = sidecars[i + 1].slot ∧
          sidecars[i + 1].blockRoot = sidecars[i].blockRoot ∧
          sidecars[i + 1].index.toNat = sidecars[i].index.toNat + 1) ∨
        (sidecars[i].slot < sidecars[i + 1].slot ∧ sidecars[i + 1].index = 0)) := by
  simp only [isValidBlobSidecarsByRangeResponse, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, slotInRange_iff, allAdjacent_iff, nextBlob_iff, and_assoc]
  cases sidecars with
  | nil => simp
  | cons first rest => simp

/-- In a valid response to a request for blob sidecars by range, each sidecar comes before the
sidecars after it.

So the sidecars of one slot name one block. -/
theorem pairwise_of_isValidBlobSidecarsByRangeResponse {config : Config} {fork : Base.Fork}
    {request : BlobSidecarsByRangeRequest} {sidecars : List ResponseSidecar}
    (valid : isValidBlobSidecarsByRangeResponse config fork request sidecars = true) :
    sidecars.Pairwise SidecarBefore := by
  simp only [isValidBlobSidecarsByRangeResponse, Bool.and_eq_true] at valid
  refine pairwise_of_allAdjacent (fun a b next => ?_) sidecarBefore_trans valid.2
  rcases (nextBlob_iff a b).mp next with ⟨slot, root, index⟩ | ⟨slot, -⟩
  · refine Or.inr ⟨slot, root.symm, ?_⟩
    rw [UInt64.lt_iff_toNat_lt]
    omega
  · exact Or.inl slot

/-- The rules that a valid response to a request for column sidecars by range meets, and no
others. -/
theorem isValidDataColumnSidecarsByRangeResponse_iff (preset : Preset) (config : Config)
    (request : DataColumnSidecarsByRangeRequest preset) (sidecars : List ResponseSidecar) :
    isValidDataColumnSidecarsByRangeResponse preset config request sidecars = true ↔
      sidecars.length ≤ request.count.toNat * preset.NUMBER_OF_COLUMNS.toNat ∧
      sidecars.length ≤ (computeMaxRequestDataColumnSidecars preset config).toNat ∧
      (∀ sidecar ∈ sidecars, (request.startSlot.toNat ≤ sidecar.slot.toNat ∧
        sidecar.slot.toNat < request.startSlot.toNat + request.count.toNat) ∧
        sidecar.index ∈ request.columns.data) ∧
      (∀ i (h : i + 1 < sidecars.length),
        (sidecars[i].slot = sidecars[i + 1].slot ∧
          sidecars[i + 1].blockRoot = sidecars[i].blockRoot ∧
          sidecars[i].index < sidecars[i + 1].index) ∨
        sidecars[i].slot < sidecars[i + 1].slot) := by
  simp only [isValidDataColumnSidecarsByRangeResponse, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, slotInRange_iff, allAdjacent_iff, nextColumn_iff, Array.contains_iff_mem,
    and_assoc]

/-- In a valid response to a request for column sidecars by range, each sidecar comes before the
sidecars after it.

So the sidecars of one slot name one block, and no column repeats in a block. -/
theorem pairwise_of_isValidDataColumnSidecarsByRangeResponse {preset : Preset} {config : Config}
    {request : DataColumnSidecarsByRangeRequest preset} {sidecars : List ResponseSidecar}
    (valid : isValidDataColumnSidecarsByRangeResponse preset config request sidecars = true) :
    sidecars.Pairwise SidecarBefore := by
  simp only [isValidDataColumnSidecarsByRangeResponse, Bool.and_eq_true] at valid
  refine pairwise_of_allAdjacent (fun a b next => ?_) sidecarBefore_trans valid.2
  rcases (nextColumn_iff a b).mp next with ⟨slot, root, index⟩ | slot
  · exact Or.inr ⟨slot, root.symm, index⟩
  · exact Or.inl slot

/-- The rules that a valid response to a request for blob sidecars by root meets, and no others. -/
theorem isValidBlobSidecarsByRootResponse_iff {config : Config} {fork : Base.Fork}
    (request : BlobSidecarsByRootRequest config fork) (sidecars : List ResponseSidecar) :
    isValidBlobSidecarsByRootResponse request sidecars = true ↔
      sidecars.length ≤ request.data.size ∧
        ∀ sidecar ∈ sidecars, ⟨sidecar.blockRoot, sidecar.index⟩ ∈ request.data := by
  simp [isValidBlobSidecarsByRootResponse, List.all_eq_true]

/-- The number of columns that a request by root names is the sum over its blocks. -/
theorem columnCount_eq {preset : Preset} {config : Config}
    (request : DataColumnSidecarsByRootRequest preset config) :
    request.columnCount = (request.data.toList.map (·.columns.data.size)).sum := by
  unfold DataColumnSidecarsByRootRequest.columnCount
  rw [← Array.foldl_toList]
  generalize request.data.toList = identifiers
  suffices ∀ start, identifiers.foldl
      (fun total identifier => total + identifier.columns.data.size) start =
      start + (identifiers.map (·.columns.data.size)).sum by simpa using this 0
  induction identifiers with
  | nil => simp
  | cons head rest ih => intro start; simp [ih]; omega

/-- The rules that a valid response to a request for column sidecars by root meets, and no others.
-/
theorem isValidDataColumnSidecarsByRootResponse_iff {preset : Preset} {config : Config}
    (request : DataColumnSidecarsByRootRequest preset config) (sidecars : List ResponseSidecar) :
    isValidDataColumnSidecarsByRootResponse request sidecars = true ↔
      sidecars.length ≤ (request.data.toList.map (·.columns.data.size)).sum ∧
        ∀ sidecar ∈ sidecars, ∃ identifier ∈ request.data,
          identifier.blockRoot = sidecar.blockRoot ∧ sidecar.index ∈ identifier.columns.data := by
  simp [isValidDataColumnSidecarsByRootResponse, columnCount_eq, List.all_eq_true,
    Array.any_eq_true', -Array.any_eq_true]

end EthLib.Consensus.Proofs.ReqResp.Validity
