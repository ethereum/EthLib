module

public import EthLib.Base.Except
public import EthLib.Consensus.ForkChoice.FastConfirmation

/-!
# Proofs: the fast confirmation rule

An empty range of slots weighs nothing.

At each slot the tracked heads move on by one: the current head becomes the previous one.

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

/-- From Gloas the fast confirmation rule is not yet specified here, so it fails. -/
theorem onFastConfirmation_of_gloas {fcr : FastConfirmationStore} (gloas : .glamsterdam ≤ fork) :
    store.onFastConfirmation config fcr = .error (.forkNotYetSpecified fork) := by
  simp [onFastConfirmation, gloas, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

end Store

end EthLib.Consensus
