module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.ForkChoice.FastConfirmation
public import EthLib.Consensus.Proofs.ForkChoice.Store

/-!
# Proofs: the fast confirmation rule

An empty range of slots weighs nothing, and so does a sum over no items.

A range that covers a whole epoch weighs the whole active balance.

At each slot the tracked heads move on by one: the current head becomes the previous one.

The update keeps the confirmed block.

A restart keeps the old confirmed block or takes the one confirmed before the restart.

From Gloas the payload status of the head does not change which blocks are in its chain.

The fast confirmation of a slot records the head of the store, at every fork.

The safe execution block is the payload of the confirmed block, and from Gloas its bid's parent.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Fork}

/-- A range that starts after it ends weighs nothing. -/
theorem estimateCommitteeWeightBetweenSlots_of_gt {totalActiveBalance : Gwei}
    {startSlot endSlot : Slot} (empty : endSlot < startSlot) :
    estimateCommitteeWeightBetweenSlots preset totalActiveBalance startSlot endSlot = .ok 0 := by
  simp [estimateCommitteeWeightBetweenSlots, empty, pure, Except.pure]

/-- A range that covers a whole epoch weighs the whole active balance. -/
theorem estimateCommitteeWeightBetweenSlots_of_covered {totalActiveBalance : Gwei}
    {startSlot endSlot : Slot}
    (covered : isFullValidatorSetCovered preset startSlot endSlot = .ok true) :
    estimateCommitteeWeightBetweenSlots preset totalActiveBalance startSlot endSlot =
      .ok totalActiveBalance := by
  -- A covered range ends in a later epoch than its first slot, so it is not empty.
  have ordered : startSlot ≤ endSlot := by
    have steps := covered
    simp only [isFullValidatorSetCovered, bind_ok_iff, mapError_ok_iff] at steps
    obtain ⟨afterFirst, first, lastOfFirst, last, afterEnd, after, later⟩ := steps
    have one : (1 : UInt64).toNat = 1 := rfl
    rw [Uint64.addChecked_ok_iff] at first after
    rw [Uint64.subChecked_ok_iff] at last
    rw [one] at last after
    have later : (lastOfFirst / preset.SLOTS_PER_EPOCH).toNat <
        (afterEnd / preset.SLOTS_PER_EPOCH).toNat := by
      simpa [pure, Except.pure, computeEpochAtSlot, UInt64.lt_iff_toNat_lt] using later
    rw [UInt64.toNat_div, UInt64.toNat_div] at later
    have below : lastOfFirst.toNat < afterEnd.toNat :=
      Nat.lt_of_not_ge fun ge => absurd later (Nat.not_lt.mpr (Nat.div_le_div_right ge))
    have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by
      rcases Nat.eq_zero_or_pos preset.SLOTS_PER_EPOCH.toNat with zero | positive
      · simp [zero] at later
      · exact positive
    rw [UInt64.le_iff_toNat_le]
    omega
  have notGt : ¬ endSlot < startSlot := UInt64.not_lt.mpr ordered
  simp [estimateCommitteeWeightBetweenSlots, notGt, covered, bind, Except.bind, pure, Except.pure]

/-- A sum over no items is zero. -/
theorem sumGwei_nil {α : Type} {weight : α → Except ForkChoiceError Gwei} :
    sumGwei [] weight = .ok 0 := by
  simp [sumGwei, bind, Except.bind, pure, Except.pure]

namespace Store

variable {config : Config} {store : Store preset fork}

/-- At each slot the tracked heads move on: the current head becomes the previous one. -/
theorem updateFastConfirmationVariables_heads {fcr after : FastConfirmationStore} {head : Root}
    (updated : store.updateFastConfirmationVariables config fcr head = .ok after) :
    (after.previousSlotHead, after.currentSlotHead) = (fcr.currentSlotHead, head) := by
  unfold updateFastConfirmationVariables at updated
  simp only [bind_ok_iff] at updated
  obtain ⟨_, -, _, -, _, -, updated⟩ := updated
  split at updated <;> simp only [bind_ok_iff] at updated <;>
    obtain ⟨_, -, updated⟩ := updated <;> split at updated <;>
    (simp only [pure, Except.pure, Except.ok.injEq] at updated; subst updated; rfl)

/-- The update of the tracked variables leaves the confirmed block as it was. -/
theorem updateFastConfirmationVariables_confirmedRoot {fcr after : FastConfirmationStore}
    {head : Root}
    (updated : store.updateFastConfirmationVariables config fcr head = .ok after) :
    after.confirmedRoot = fcr.confirmedRoot := by
  unfold updateFastConfirmationVariables at updated
  simp only [bind_ok_iff] at updated
  obtain ⟨_, -, _, -, _, -, updated⟩ := updated
  split at updated <;> simp only [bind_ok_iff] at updated <;>
    obtain ⟨_, -, updated⟩ := updated <;> split at updated <;>
    (simp only [pure, Except.pure, Except.ok.injEq] at updated; subst updated; rfl)

/-- A restart keeps the old confirmed block, or takes the block confirmed before the restart. -/
theorem getRestartResilientConfirmedRoot_eq_or {fcr : FastConfirmationStore}
    {head rootBeforeRestart root : Root}
    (restarted : store.getRestartResilientConfirmedRoot config fcr head rootBeforeRestart =
      .ok root) :
    root = fcr.confirmedRoot ∨ root = rootBeforeRestart := by
  unfold getRestartResilientConfirmedRoot at restarted
  simp only [bind_ok_iff] at restarted
  obtain ⟨_, -, _, -, restarted⟩ := restarted
  split at restarted
  · simp only [pure, Except.pure, Except.ok.injEq] at restarted
    exact Or.inl restarted.symm
  · simp only [bind_ok_iff] at restarted
    obtain ⟨_, -, restarted⟩ := restarted
    split at restarted
    · simp only [pure, Except.pure, Except.ok.injEq] at restarted
      exact Or.inl restarted.symm
    · simp only [bind_ok_iff] at restarted
      obtain ⟨_, -, restarted⟩ := restarted
      split at restarted
      · simp only [pure, Except.pure, Except.ok.injEq] at restarted
        exact Or.inl restarted.symm
      · simp only [pure, Except.pure, Except.ok.injEq] at restarted
        exact Or.inr restarted.symm

/-- From Gloas the payload status of the head does not change whether a block is in its chain.

So a head given by its root, as a pending node, answers as the head that the fork choice finds. -/
theorem isAncestor_head_pending (gloas : .glamsterdam ≤ fork) (head : ForkChoiceNode)
    (root : Root) :
    store.isAncestor head ⟨root, .pending⟩ =
      store.isAncestor ⟨head.root, .pending⟩ ⟨root, .pending⟩ := by
  rw [isAncestor_pending gloas, isAncestor_pending gloas]
  simp only [bind, Except.bind]
  split
  · rfl
  · rename_i ancestorBlock _
    have same := getAncestor_root (store := store) head .pending ancestorBlock.slot
    revert same
    cases store.getAncestor head ancestorBlock.slot <;>
      cases store.getAncestor ⟨head.root, .pending⟩ ancestorBlock.slot <;>
      simp_all [Functor.map, Except.map, pure, Except.pure]

/-- The fast confirmation of a slot records the head of the store as the head of the slot.

The head of the slot before becomes the previous head. -/
theorem onFastConfirmation_heads {fcr after : FastConfirmationStore}
    (confirmed : store.onFastConfirmation config fcr = .ok after) :
    ∃ head, store.getHead config = .ok head ∧
      (after.previousSlotHead, after.currentSlotHead) = (fcr.currentSlotHead, head.root) := by
  unfold onFastConfirmation at confirmed
  simp only [bind_ok_iff] at confirmed
  obtain ⟨head, found, updated, update, root, -, confirmed⟩ := confirmed
  simp only [pure, Except.pure, Except.ok.injEq] at confirmed
  subst confirmed
  exact ⟨head, found, updateFastConfirmationVariables_heads (after := updated) update⟩

/-- Before Gloas the safe execution block is the payload of the confirmed block. -/
theorem getSafeExecutionBlockHash_of_lt {fcr : FastConfirmationStore}
    {bellatrix : .bellatrix ≤ fork} (before : fork < .glamsterdam) :
    store.getSafeExecutionBlockHash fcr bellatrix =
      (fun block => (block.body.executionPayload ⟨bellatrix, before⟩).blockHash) <$>
        store.block fcr.confirmedRoot := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le.mpr before
  simp only [getSafeExecutionBlockHash, notGloas, ↓reduceDIte, bind, Except.bind, pure,
    Except.pure, Functor.map, Except.map]

/-- From Gloas the safe execution block is the parent payload of the bid of the confirmed block. -/
theorem getSafeExecutionBlockHash_of_gloas {fcr : FastConfirmationStore}
    {bellatrix : .bellatrix ≤ fork} (gloas : .glamsterdam ≤ fork) :
    store.getSafeExecutionBlockHash fcr bellatrix =
      (fun block => (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash) <$>
        store.block fcr.confirmedRoot := by
  simp only [getSafeExecutionBlockHash, gloas, ↓reduceDIte, bind, Except.bind, pure,
    Except.pure, Functor.map, Except.map]

end Store

end EthLib.Consensus
