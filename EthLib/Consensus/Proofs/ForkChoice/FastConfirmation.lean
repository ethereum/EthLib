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

/-- A sum over no items is zero. -/
theorem sumGwei_nil {α : Type} {weight : α → Except ForkChoiceError Gwei} :
    sumGwei [] weight = .ok 0 := by
  simp [sumGwei, bind, Except.bind, pure, Except.pure]

namespace Store

variable {config : Config} {store : Store preset fork}

/-- A range that starts after it ends weighs nothing. -/
theorem computeCommitteeWeightBetweenSlots_of_gt {head : Root}
    {balanceSource : BeaconState preset fork} {startSlot endSlot : Slot}
    (empty : endSlot < startSlot) :
    store.computeCommitteeWeightBetweenSlots head balanceSource startSlot endSlot = .ok 0 := by
  simp [computeCommitteeWeightBetweenSlots, computeCommitteeWeightAndMembers, empty, bind,
    Except.bind, pure, Except.pure]

/-- A range that covers a whole epoch weighs the total active balance of the source. -/
theorem computeCommitteeWeightBetweenSlots_of_covered {head : Root}
    {balanceSource : BeaconState preset fork} {startSlot endSlot : Slot}
    (covered : isFullValidatorSetCovered preset startSlot endSlot = .ok true) :
    store.computeCommitteeWeightBetweenSlots head balanceSource startSlot endSlot =
      (getTotalActiveBalance balanceSource).mapError .accessor := by
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
  simp only [computeCommitteeWeightBetweenSlots, computeCommitteeWeightAndMembers, notGt,
    covered, ↓reduceIte]
  cases (getTotalActiveBalance balanceSource) <;> rfl

/-- A range of slots that starts after it ends has no members of its committees. -/
theorem getCommitteesBetweenSlots_of_gt {head : Root} {startSlot endSlot : Slot}
    (empty : endSlot < startSlot) :
    store.getCommitteesBetweenSlots head startSlot endSlot = .ok ∅ := by
  have below : endSlot.toNat + 1 < 2 ^ 64 := by
    have := UInt64.lt_iff_toNat_lt.mp empty
    have := startSlot.toNat_lt
    omega
  have afterEndOk : Uint64.addChecked endSlot 1 = .ok (endSlot + 1) := by
    rw [Uint64.addChecked_ok_iff]
    refine ⟨by simpa using below, ?_⟩
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by simpa using below)]
  have zero : (endSlot + 1).toNat - startSlot.toNat = 0 := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by simpa using below)]
    have := UInt64.lt_iff_toNat_lt.mp empty
    simp only [UInt64.toNat_one]
    omega
  simp only [getCommitteesBetweenSlots, afterEndOk, Except.mapError, bind, Except.bind, zero,
    List.range_zero, List.foldlM_nil, pure, Except.pure]

/-- The members that come with a committee weight are those of the committees of its range. -/
theorem getCommitteesBetweenSlots_of_computeCommitteeWeightAndMembers {head : Root}
    {balanceSource : BeaconState preset fork} {startSlot endSlot : Slot} {weight : Gwei}
    {participants : Std.TreeSet ValidatorIndex}
    (computed : store.computeCommitteeWeightAndMembers head balanceSource startSlot endSlot =
      .ok (weight, some participants)) :
    store.getCommitteesBetweenSlots head startSlot endSlot = .ok participants := by
  simp only [computeCommitteeWeightAndMembers] at computed
  split at computed
  · simp [pure, Except.pure] at computed
  · rw [bind_ok_iff] at computed
    obtain ⟨covered, -, computed⟩ := computed
    cases covered
    · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok_iff, mapError_ok_iff] at computed
      obtain ⟨found, foundOk, _, -, _, -, final⟩ := computed
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at final
      exact final.2 ▸ foundOk
    · simp only [↓reduceIte, bind_ok_iff, mapError_ok_iff] at computed
      obtain ⟨_, -, final⟩ := computed
      simp [pure, Except.pure] at final

/-- The adversary of a range reads the committee weight, its share, then the equivocators.

That holds for every input, errors included, so reading the members once changes nothing. -/
theorem computeAdversarialWeight_eq_spec {config : Config} {head : Root}
    {balanceSource : BeaconState preset fork} {startSlot endSlot : Slot} :
    store.computeAdversarialWeight config head balanceSource startSlot endSlot = (do
      let w ← store.computeCommitteeWeightBetweenSlots head balanceSource startSlot endSlot
      let s ← (Uint64.mulChecked (w / 100) config.CONFIRMATION_BYZANTINE_THRESHOLD).mapError .arith
      let e ← store.getEquivocationScore head balanceSource startSlot endSlot
      return Uint64.saturatingSub s e) := by
  unfold computeAdversarialWeight computeCommitteeWeightBetweenSlots
  rcases pair : store.computeCommitteeWeightAndMembers head balanceSource startSlot endSlot with
    _ | ⟨w, _ | m⟩
  · rfl
  · simp only [bind, Except.bind, pure, Except.pure, getEquivocationScore]
    split <;> try rfl
    split <;> rfl
  · have := getCommitteesBetweenSlots_of_computeCommitteeWeightAndMembers pair
    simp [bind, Except.bind, pure, Except.pure, getEquivocationScore, this]

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

/-- Before Gloas the execution block of a block of the store is its payload. -/
theorem executionBlockHashAt_of_lt {root : Root} {bellatrix : .bellatrix ≤ fork}
    (before : fork < .glamsterdam) :
    store.executionBlockHashAt root bellatrix =
      (fun block => (block.body.executionPayload ⟨bellatrix, before⟩).blockHash) <$>
        store.block root := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le.mpr before
  simp only [executionBlockHashAt, notGloas, ↓reduceDIte, bind, Except.bind, pure,
    Except.pure, Functor.map, Except.map]

/-- From Gloas the execution block of a block of the store is the parent payload of its bid. -/
theorem executionBlockHashAt_of_gloas {root : Root} {bellatrix : .bellatrix ≤ fork}
    (gloas : .glamsterdam ≤ fork) :
    store.executionBlockHashAt root bellatrix =
      (fun block => (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash) <$>
        store.block root := by
  simp only [executionBlockHashAt, gloas, ↓reduceDIte, bind, Except.bind, pure,
    Except.pure, Functor.map, Except.map]

/-- Before Gloas the safe execution block is the payload of the confirmed block. -/
theorem getSafeExecutionBlockHash_of_lt {fcr : FastConfirmationStore}
    {bellatrix : .bellatrix ≤ fork} (before : fork < .glamsterdam) :
    store.getSafeExecutionBlockHash fcr bellatrix =
      (fun block => (block.body.executionPayload ⟨bellatrix, before⟩).blockHash) <$>
        store.block fcr.confirmedRoot :=
  store.executionBlockHashAt_of_lt before

/-- From Gloas the safe execution block is the parent payload of the bid of the confirmed block. -/
theorem getSafeExecutionBlockHash_of_gloas {fcr : FastConfirmationStore}
    {bellatrix : .bellatrix ≤ fork} (gloas : .glamsterdam ≤ fork) :
    store.getSafeExecutionBlockHash fcr bellatrix =
      (fun block => (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash) <$>
        store.block fcr.confirmedRoot :=
  store.executionBlockHashAt_of_gloas gloas

/-- Before Gloas the finalized execution block is the payload of the finalized block. -/
theorem getFinalizedExecutionBlockHash_of_lt {bellatrix : .bellatrix ≤ fork}
    (before : fork < .glamsterdam) :
    store.getFinalizedExecutionBlockHash bellatrix =
      (fun block => (block.body.executionPayload ⟨bellatrix, before⟩).blockHash) <$>
        store.block store.finalizedCheckpoint.root :=
  store.executionBlockHashAt_of_lt before

/-- From Gloas the finalized execution block is the parent payload of the finalized bid. -/
theorem getFinalizedExecutionBlockHash_of_gloas {bellatrix : .bellatrix ≤ fork}
    (gloas : .glamsterdam ≤ fork) :
    store.getFinalizedExecutionBlockHash bellatrix =
      (fun block => (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash) <$>
        store.block store.finalizedCheckpoint.root :=
  store.executionBlockHashAt_of_gloas gloas

end Store

end EthLib.Consensus
