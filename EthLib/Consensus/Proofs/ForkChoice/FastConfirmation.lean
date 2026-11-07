module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.ForkChoice.FastConfirmation

/-!
# Proofs: the fast confirmation rule

An empty range of slots weighs nothing, and so does a sum over no items.

A range that covers a whole epoch weighs the whole active balance.

At each slot the tracked heads move on by one: the current head becomes the previous one.

The update keeps the confirmed block.

A restart keeps the old confirmed block or takes the one confirmed before the restart.

From Gloas the rule fails as not yet specified.
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

/-- From Gloas the fast confirmation rule is not yet specified here, so it fails. -/
theorem onFastConfirmation_of_gloas {fcr : FastConfirmationStore} (gloas : .glamsterdam ≤ fork) :
    store.onFastConfirmation config fcr = .error (.forkNotYetSpecified fork) := by
  simp [onFastConfirmation, gloas, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

end Store

end EthLib.Consensus
