module

public import EthLib.Consensus.ReqResp.Validity

/-!
# `Consensus.Proofs.ReqResp.Validity`

What the validity of a response says about its blocks.

- A valid response to a request for blocks by range has at most the count of blocks.
- Its blocks lie in the requested slots, with slots that increase along the whole list.
- When the step is 1, each block names the one before it as its parent, so the blocks form a chain.
- A valid response to a request for blocks by root has at most as many blocks as requested roots.
- The root of each of its blocks is a requested root.
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
    slotsAscending_iff, parentsLinked_iff, UInt64.le_iff_toNat_le, and_assoc,
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

end EthLib.Consensus.Proofs.ReqResp.Validity
