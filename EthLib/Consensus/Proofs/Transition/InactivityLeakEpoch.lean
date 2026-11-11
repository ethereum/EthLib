module

public import EthLib.Consensus.Proofs.Transition.InactivityLeak
public import EthLib.Consensus.Proofs.Transition.Invariants

/-!
# Proofs: an epoch stays in the leak unless finality advances

The leak test reads only the slot and the epoch of the finalized checkpoint.

Justification and finalization keep the slot, as does the full epoch transition.

So either step keeps the test when the finalized epoch stays fixed.

With ordered, settled checkpoints, the finalized epoch never decreases.

A leaking state therefore still leaks after an epoch transition unless finality advances.

This is the finality condition of the leak described by [Pavloff et al.][pat], Section 4.

It does not derive the balance, score or effective-balance traces of the leak bounds.

[pat]: https://arxiv.org/abs/2404.16363v2
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

private theorem leak_eq_of_slot_finalized (slot : after.slot = state.slot)
    (finalized : after.finalizedCheckpoint.epoch = state.finalizedCheckpoint.epoch) :
    isInInactivityLeak after = isInInactivityLeak state := by
  simp only [isInInactivityLeak, getFinalityDelay, getPreviousEpoch, getCurrentEpoch, slot,
    finalized]

private theorem justification_slot
    (computed : processJustificationAndFinalization state = .ok after) :
    after.slot = state.slot := by
  obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · rfl
  · -- Restoring the checkpoint fields does not change the slot.
    have kept := congrArg (fun s : BeaconState preset fork => s.slot)
      (weighJustificationAndFinalization_checkpoints weighed).2.2.2
    exact kept

/-- Justification and finalization keep the leak test when the finalized epoch stays fixed. -/
theorem processJustificationAndFinalization_isInInactivityLeak_eq
    (computed : processJustificationAndFinalization state = .ok after)
    (finalized : after.finalizedCheckpoint.epoch = state.finalizedCheckpoint.epoch) :
    isInInactivityLeak after = isInInactivityLeak state :=
  leak_eq_of_slot_finalized (justification_slot computed) finalized

/-- A successful epoch transition keeps the leak test when the finalized epoch stays fixed. -/
theorem processEpoch_isInInactivityLeak_eq {config : Config} {checks : SignatureChecks}
    (computed : processEpoch config checks state = .ok after)
    (finalized : after.finalizedCheckpoint.epoch = state.finalizedCheckpoint.epoch) :
    isInInactivityLeak after = isInInactivityLeak state := by
  obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame computed
  exact leak_eq_of_slot_finalized (frame.slot.trans (justification_slot justifiedOk)) finalized

/-- An epoch transition from a leaking state advances finality or leaves the state in the leak.

The checkpoints must be ordered, and the current justified epoch at most the previous epoch. -/
theorem processEpoch_finalized_lt_or_isInInactivityLeak {config : Config}
    {checks : SignatureChecks} (ordered : CheckpointsOrdered state)
    (settled : state.currentJustifiedCheckpoint.epoch ≤ getPreviousEpoch state)
    (leak : isInInactivityLeak state = .ok true)
    (computed : processEpoch config checks state = .ok after) :
    state.finalizedCheckpoint.epoch < after.finalizedCheckpoint.epoch ∨
      isInInactivityLeak after = .ok true := by
  by_cases advanced : state.finalizedCheckpoint.epoch < after.finalizedCheckpoint.epoch
  · exact .inl advanced
  obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame computed
  have monotone := (processJustificationAndFinalization_ordered ordered settled justifiedOk).2
  rw [← frame.finalized] at monotone
  have same := UInt64.le_antisymm (UInt64.not_lt.mp advanced) monotone
  exact .inr ((processEpoch_isInInactivityLeak_eq computed same).trans leak)

end EthLib.Consensus
