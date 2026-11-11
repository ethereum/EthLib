module

public import EthLib.Consensus.Proofs.Transition.Invariants

/-!
# Proofs: the chain stays in the leak unless finality advances

The leak test reads only the slot and the finalized epoch.

A later slot, with a finalized epoch no later, therefore keeps a leak.

Justification and finalization keep the slot.

The steps of an epoch read the leak test on the state that justification returns.

Some read it later in the epoch, with the same slot and the same finalized checkpoint.

That state still leaks unless the finalized epoch rises.

So does the state after one slot, which ends at a later slot.

In [Pavloff et al.][pat], Section 4, the leak starts after four epochs without finalization.

Their Section 5.1 ends it at the next finalization; that direction is not proved here.

The balance, score and effective-balance traces of the leak bounds are not derived here.

[pat]: https://arxiv.org/abs/2404.16363v2
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-- A leak holds at every later slot whose finalized epoch is no later. -/
theorem isInInactivityLeak_of_slot_le (leak : isInInactivityLeak state = .ok true)
    (later : state.slot.toNat ≤ after.slot.toNat)
    (finalized : after.finalizedCheckpoint.epoch ≤ state.finalizedCheckpoint.epoch) :
    isInInactivityLeak after = .ok true := by
  obtain ⟨delay, delayOk, big⟩ := isInInactivityLeak_ok_iff.mp leak
  obtain ⟨settled, value⟩ := getFinalityDelay_ok_iff.mp delayOk
  have before := getPreviousEpoch_toNat state
  have now := getPreviousEpoch_toNat after
  rw [getCurrentEpoch_toNat] at before now
  have grows : state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤
      after.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := Nat.div_le_div_right later
  have lt := UInt64.lt_iff_toNat_lt.mp (big.mp rfl)
  have lower := UInt64.le_iff_toNat_le.mp finalized
  have le : after.finalizedCheckpoint.epoch ≤ getPreviousEpoch after := by
    rw [UInt64.le_iff_toNat_le]
    omega
  have sub := UInt64.toNat_sub_of_le _ _ le
  refine isInInactivityLeak_ok_iff.mpr ⟨getPreviousEpoch after - after.finalizedCheckpoint.epoch,
    getFinalityDelay_ok_iff.mpr ⟨UInt64.le_iff_toNat_le.mp le, sub⟩, ?_⟩
  simp only [true_iff]
  rw [UInt64.lt_iff_toNat_lt, sub]
  omega

/-- An epoch transition from a leaking state advances finality, or its steps read a leak.

The steps after justification and finalization read the leak test on the state it returns.

Some read it on a later state, with the same slot and the same finalized checkpoint. -/
theorem processEpoch_finalized_lt_or_isInInactivityLeak {config : Config}
    {checks : SignatureChecks} (leak : isInInactivityLeak state = .ok true)
    (computed : processEpoch config checks state = .ok after) :
    ∃ justified, processJustificationAndFinalization state = .ok justified ∧
      (state.finalizedCheckpoint.epoch < after.finalizedCheckpoint.epoch ∨
        isInInactivityLeak justified = .ok true) := by
  obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame computed
  refine ⟨justified, justifiedOk, ?_⟩
  rw [frame.finalized]
  by_cases advanced : state.finalizedCheckpoint.epoch < justified.finalizedCheckpoint.epoch
  · exact .inl advanced
  exact .inr (isInInactivityLeak_of_slot_le leak
    (by rw [processJustificationAndFinalization_slot justifiedOk]; exact Nat.le_refl _)
    (UInt64.not_lt.mp advanced))

/-- One slot from a leaking state advances finality, or ends in a state that still leaks. -/
theorem advanceSlot_finalized_lt_or_isInInactivityLeak {config : Config}
    {checks : SignatureChecks} (leak : isInInactivityLeak state = .ok true)
    (computed : advanceSlot config checks state = .ok after) :
    state.finalizedCheckpoint.epoch < after.finalizedCheckpoint.epoch ∨
      isInInactivityLeak after = .ok true := by
  by_cases advanced : state.finalizedCheckpoint.epoch < after.finalizedCheckpoint.epoch
  · exact .inl advanced
  exact .inr (isInInactivityLeak_of_slot_le leak
    (by have := advanceSlot_slot computed; omega) (UInt64.not_lt.mp advanced))

end EthLib.Consensus
