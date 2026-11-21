module

public import EthLib.Consensus.Proofs.BeaconApi.StateQueries
public import EthLib.Consensus.Proofs.Transition.MixesKept

/-!
# Proofs: the RANDAO answer of a past epoch stays fixed through the state transition

The transition writes the entry of an epoch only during that epoch, and at the reset into it.

So the step out of an epoch, and every later step, keep its entry while the state holds it.

An answer to the RANDAO query for a past epoch is then the mix that the chain wrote in that epoch.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-- Two epochs less than a period apart, in that order, sit at different entries. -/
private theorem mod_ne_of_lt {period early late : Nat} (lt : early < late)
    (near : late < early + period) : late % period ≠ early % period := by
  intro same
  have apart : period ∣ late - early := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq same)
  have := Nat.le_of_dvd (by omega) apart
  omega

/-- A write at an epoch reached after a held past epoch keeps the mix of that past epoch. -/
private theorem read_of_mixesKeptBut {written epoch : Epoch}
    {middle : BeaconState preset fork} (kept : MixesKeptBut written state middle)
    (lt : epoch.toNat < written.toNat)
    (near : written.toNat < epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) :
    readCircular middle.randaoMixes.elements epoch =
      readCircular state.randaoMixes.elements epoch := by
  apply kept epoch
  intro same
  have entries := congrArg UInt64.toNat same
  simp only [UInt64.toNat_mod] at entries
  exact mod_ne_of_lt lt near entries.symm

/-- One slot keeps the mix of each epoch up to the current one, still held after the slot. -/
private theorem advanceSlot_read (computed : advanceSlot config checks state = .ok after)
    {epoch : Epoch} (reached : epoch.toNat ≤ (getCurrentEpoch state).toNat)
    (near : (getCurrentEpoch after).toNat <
      epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) :
    readCircular after.randaoMixes.elements epoch =
      readCircular state.randaoMixes.elements epoch := by
  have kept := mixesKeptBut_advanceSlot computed
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have cachedMixes : cached.randaoMixes = state.randaoMixes := by rw [cachedEq]
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    -- At the end of an epoch, the slot writes the entry of the next epoch, after the given one.
    have epochs := nextSlot_epoch_of_boundary sum boundary
    have reachedNext : (getCurrentEpoch { epoched with slot := next }).toNat =
        (getCurrentEpoch state).toNat + 1 := by
      rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
      exact epochs
    exact read_of_mixesKeptBut kept (by omega) near
  · -- Within an epoch, the slot writes no mix.
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    show readCircular cached.randaoMixes.elements epoch = _
    rw [cachedMixes]

/-- A run of slots keeps the mix of each epoch up to the current one, still held at its end. -/
private theorem advanceSlots_read :
    ∀ (count : Nat) {state after : BeaconState preset fork},
      advanceSlots config checks count state = .ok after → ∀ {epoch : Epoch},
      epoch.toNat ≤ (getCurrentEpoch state).toNat →
      (getCurrentEpoch after).toNat < epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat →
      readCircular after.randaoMixes.elements epoch =
        readCircular state.randaoMixes.elements epoch
  | 0, _, _, computed, _, _, _ => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    rw [computed]
  | count + 1, state, after, computed, epoch, reached, near => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨middle, first, rest⟩ := computed
    -- The current epoch never moves back along the run.
    have before : (getCurrentEpoch state).toNat ≤ (getCurrentEpoch middle).toNat := by
      rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, advanceSlot_slot first]
      exact Nat.div_le_div_right (Nat.le_succ _)
    have later : (getCurrentEpoch middle).toNat ≤ (getCurrentEpoch after).toNat := by
      rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, advanceSlots_slot count rest]
      exact Nat.div_le_div_right (Nat.le_add_right _ _)
    rw [advanceSlots_read count rest (by omega) near]
    exact advanceSlot_read first reached (by omega)

/-- Two states that hold an epoch alike and read the same mix for it answer alike. -/
private theorem stateRandao_congr {epoch : Epoch}
    (held : holdsRandaoMix after epoch = holdsRandaoMix state epoch)
    (read : getRandaoMix after epoch = getRandaoMix state epoch) :
    stateRandao after (some epoch) = stateRandao state (some epoch) := by
  simp only [stateRandao, Option.getD_some, held, read]

/-- A run of slots keeps the RANDAO answer of each epoch up to the current one.

The epoch must still be held by the state after the run.

The run writes only the entries of the epochs after the current one, at their resets. -/
theorem stateRandao_processSlots {slot : Slot}
    (computed : processSlots config checks state slot = .ok after) {epoch : Epoch}
    (reached : epoch ≤ getCurrentEpoch state) (held : holdsRandaoMix after epoch = true) :
    stateRandao after (some epoch) = stateRandao state (some epoch) := by
  unfold processSlots at computed
  simp only [bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, -, run⟩ := computed
  have later : (getCurrentEpoch state).toNat ≤ (getCurrentEpoch after).toNat := by
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, advanceSlots_slot _ run]
    exact Nat.div_le_div_right (Nat.le_add_right _ _)
  have reachedNat := UInt64.le_iff_toNat_le.mp reached
  have near := held
  simp only [holdsRandaoMix, Bool.and_eq_true, decide_eq_true_eq] at near
  -- The epoch is held before the run too, since the current epoch only moves forward.
  have heldState : holdsRandaoMix state epoch = true := by
    simp only [holdsRandaoMix, Bool.and_eq_true, decide_eq_true_eq]
    omega
  apply stateRandao_congr
  · rw [held, heldState]
  · exact advanceSlots_read _ run reachedNat near.2

/-- The state transition keeps the RANDAO answer of each epoch up to the current one.

The epoch must come before the epoch of the block, and still be held by the state after it.

The slots write only the entries of the epochs after the current one, at their resets.

The block writes only the entry of its own epoch, which the epoch is not. -/
theorem stateRandao_stateTransition {signed : SignedBeaconBlock preset fork}
    {validateResult : Bool}
    (computed : stateTransition config checks engine state signed validateResult = .ok after)
    {epoch : Epoch} (reached : epoch ≤ getCurrentEpoch state)
    (past : epoch < getCurrentEpoch after) (held : holdsRandaoMix after epoch = true) :
    stateRandao after (some epoch) = stateRandao state (some epoch) := by
  obtain ⟨advanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok computed
  -- The block keeps the slot, so the current epoch.
  have same : getCurrentEpoch after = getCurrentEpoch advanced := by
    simp only [getCurrentEpoch, (frame_processBlock blockOk).slot]
  have heldAdvanced : holdsRandaoMix advanced epoch = true := by
    rwa [holdsRandaoMix, ← same]
  rw [← stateRandao_processSlots slotsOk reached heldAdvanced]
  have pastNat := UInt64.lt_iff_toNat_lt.mp past
  rw [same] at pastNat
  have near := held
  simp only [holdsRandaoMix, Bool.and_eq_true, decide_eq_true_eq, same] at near
  -- The block writes only the entry of its own epoch, which is not the past one.
  apply stateRandao_congr
  · rw [holdsRandaoMix, holdsRandaoMix, same]
  · exact read_of_mixesKeptBut (mixesKeptBut_processBlock blockOk) (by omega) near.2

end EthLib.Consensus.BeaconApi
