module

public import EthLib.Base.Except
public import EthLib.Consensus.ForkChoice.FastConfirmation

/-!
# Proofs: the fast confirmation rule

An empty range of slots weighs nothing, and so does a sum over no items.

A range that covers a whole epoch weighs the whole active balance.

At each slot the tracked heads move on by one: the current head becomes the previous one.

The update keeps the confirmed block.

A restart picks the old confirmed block or the one before it.

The store at the start holds the finalized checkpoint in each field.

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

/-- A range that covers a whole epoch weighs the whole active balance.

The range must not be empty. -/
theorem estimateCommitteeWeightBetweenSlots_of_covered {totalActiveBalance : Gwei}
    {startSlot endSlot : Slot}
    (covered : isFullValidatorSetCovered preset startSlot endSlot = .ok true)
    (ordered : startSlot ≤ endSlot) :
    estimateCommitteeWeightBetweenSlots preset totalActiveBalance startSlot endSlot =
      .ok totalActiveBalance := by
  have notGt : ¬ endSlot < startSlot := UInt64.not_lt.mpr ordered
  simp [estimateCommitteeWeightBetweenSlots, notGt, covered, bind, Except.bind, pure, Except.pure]

/-- A sum over no items is zero. -/
theorem sumGwei_nil {α : Type} {weight : α → Except ForkChoiceError Gwei} :
    sumGwei [] weight = .ok 0 := by
  simp [sumGwei, bind, Except.bind, pure, Except.pure]

/-- The store at the start holds the finalized checkpoint, or its root, in each field. -/
theorem getFastConfirmationStore_fields (store : Store preset fork) :
    (getFastConfirmationStore store).confirmedRoot = store.finalizedCheckpoint.root ∧
    (getFastConfirmationStore store).previousEpochObservedJustifiedCheckpoint =
      store.finalizedCheckpoint ∧
    (getFastConfirmationStore store).currentEpochObservedJustifiedCheckpoint =
      store.finalizedCheckpoint ∧
    (getFastConfirmationStore store).previousEpochGreatestUnrealizedCheckpoint =
      store.finalizedCheckpoint ∧
    (getFastConfirmationStore store).previousSlotHead = store.finalizedCheckpoint.root ∧
    (getFastConfirmationStore store).currentSlotHead = store.finalizedCheckpoint.root :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

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
