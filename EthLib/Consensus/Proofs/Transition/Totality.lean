module

public import EthLib.Consensus.Proofs.Containers.Misc
public import EthLib.Consensus.Proofs.Transition.StateTransition

/-!
# Proofs: the steps of a slot that never fail

Advancing a state to a later slot fails on an overflow, a read out of range or a full list.

This file shows that some of its steps never fail, under small hypotheses.

The caching of a slot succeeds when the state is lawful and a next slot exists.

Its circular buffers of roots must have a positive length.

The resets of an epoch succeed when a next slot exists and their buffers have a positive length.

The update of the history succeeds while its list has room for one more entry.

The rotation of the pending attestations, before Altair, always succeeds.

Every step below keeps the slot, so a next slot still exists after it.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz SszType

variable {preset : Preset} {fork : Base.Fork} {state : BeaconState preset fork}

/-- The current epoch is at most the slot, at every length of an epoch. -/
theorem getCurrentEpoch_toNat_le (state : BeaconState preset fork) :
    (getCurrentEpoch state).toNat ≤ state.slot.toNat := by
  rw [getCurrentEpoch_toNat]
  exact Nat.div_le_self _ _

/-- A next slot gives a next epoch. -/
private theorem nextEpoch_ok (state : BeaconState preset fork)
    (fits : state.slot.toNat + 1 < 2 ^ 64) :
    ∃ next, addChecked (getCurrentEpoch state) 1 = .ok next := by
  have le := getCurrentEpoch_toNat_le state
  exact ⟨_, addChecked_of_lt (by simp; omega)⟩

/-- A length of a circular buffer with a positive length on naturals is nonzero. -/
private theorem ne_zero_of_toNat {n : UInt64} [NeZero n.toNat] : n ≠ 0 :=
  fun h => NeZero.ne n.toNat (by rw [h]; rfl)

/-- A write to a rooted circular buffer of positive length succeeds. -/
private theorem writeCircularRooted_ok {α : Type} [SszType α] {n : UInt64}
    [NeZero n.toNat] (buffer : RootedVector α n.toNat) (i : UInt64) (value : α) :
    ∃ after, writeCircularRooted buffer i value = .ok after := by
  simp [writeCircularRooted, ne_zero_of_toNat (n := n)]

/-- From Gloas: the availability of the next payload is cleared when a next slot exists.

The circular buffer of availability bits must have a positive length. -/
theorem unsetNextPayloadAvailability_total [NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat]
    (gloas : .glamsterdam ≤ fork) (fits : state.slot.toNat + 1 < 2 ^ 64) :
    ∃ after, unsetNextPayloadAvailability state gloas = .ok after := by
  have next : addChecked state.slot 1 = .ok (state.slot + 1) :=
    addChecked_of_lt (by simpa using fits)
  simp only [unsetNextPayloadAvailability, liftArith, next, Except.mapError,
    writeCircular_of_ne_zero _ _ _ (ne_zero_of_toNat (n := preset.SLOTS_PER_HISTORICAL_ROOT)),
    bind, Except.bind]
  exact ⟨_, rfl⟩

/-- The caching of a slot succeeds when the state is lawful and a next slot exists.

The circular buffers of roots must have a positive length. -/
theorem processSlot_total [LawfulSszType (BeaconState preset fork)]
    [NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat] (fits : state.slot.toNat + 1 < 2 ^ 64) :
    ∃ after, processSlot state = .ok after := by
  obtain ⟨root, hr⟩ := hashTreeRoot_total state
  obtain ⟨w, hw⟩ := writeCircularRooted_ok state.stateRoots state.slot root
  simp only [processSlot, liftSsz, hr, liftAccessor, hw, Except.mapError, bind, Except.bind]
  obtain ⟨header, hH⟩ : ∃ header : BeaconBlockHeader,
      header = if state.latestBlockHeader.stateRoot = Vector.replicate 32 0 then
        { state.latestBlockHeader with stateRoot := root } else state.latestBlockHeader :=
    ⟨_, rfl⟩
  rw [← hH]
  obtain ⟨r, hr'⟩ := hashTreeRoot_total header
  obtain ⟨w', hw'⟩ := writeCircularRooted_ok state.blockRoots state.slot r
  simp only [hr', hw']
  split
  · rename_i gloas
    obtain ⟨a, ha⟩ := unsetNextPayloadAvailability_total
      (state := { state with latestBlockHeader := header, blockRoots := w', stateRoots := w })
      gloas fits
    simp only [ha]
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- The reset of the slashed balances succeeds when a next slot exists.

The circular buffer of slashed balances must have a positive length. -/
theorem processSlashingsReset_total [NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat]
    (fits : state.slot.toNat + 1 < 2 ^ 64) : ∃ after, processSlashingsReset state = .ok after := by
  obtain ⟨next, ok⟩ := nextEpoch_ok state fits
  obtain ⟨w, hw⟩ := writeCircularRooted_ok state.slashings next 0
  simp only [processSlashingsReset, liftAccessor, liftArith, ok, hw, Except.mapError, bind,
    Except.bind]
  exact ⟨_, rfl⟩

/-- The reset of the RANDAO mixes succeeds when a next slot exists.

The circular buffer of mixes must have a positive length. -/
theorem processRandaoMixesReset_total [NeZero preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat]
    (fits : state.slot.toNat + 1 < 2 ^ 64) :
    ∃ after, processRandaoMixesReset state = .ok after := by
  obtain ⟨next, ok⟩ := nextEpoch_ok state fits
  have current : ∃ mix, getRandaoMix state (getCurrentEpoch state) = .ok mix :=
    ⟨_, by
      rw [getRandaoMix, readCircular,
        dite_eq_right (ne_zero_of_toNat (n := preset.EPOCHS_PER_HISTORICAL_VECTOR))]⟩
  obtain ⟨mix, hm⟩ := current
  obtain ⟨w, hw⟩ := writeCircularRooted_ok state.randaoMixes next mix
  simp only [processRandaoMixesReset, liftAccessor, liftArith, ok, hm, hw, Except.mapError, bind,
    Except.bind]
  exact ⟨_, rfl⟩

/-- Before Heze: the reset of the votes on the deposit contract succeeds when a next slot exists. -/
theorem processEth1DataReset_total (before : fork < .hegota)
    (fits : state.slot.toNat + 1 < 2 ^ 64) :
    ∃ after, processEth1DataReset before state = .ok after := by
  obtain ⟨next, ok⟩ := nextEpoch_ok state fits
  simp only [processEth1DataReset, liftAccessor, liftArith, ok, Except.mapError, bind,
    Except.bind]
  split <;> exact ⟨_, rfl⟩

/-- Before Capella: the update of the historical roots succeeds while their list has room.

A next slot must exist, and the circular buffers of roots must have a positive length. -/
theorem processHistoricalRootsUpdate_total [NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat]
    (before : fork < .shapella) (fits : state.slot.toNat + 1 < 2 ^ 64)
    (room : state.historicalRoots.data.size < preset.HISTORICAL_ROOTS_LIMIT.toNat) :
    ∃ after, processHistoricalRootsUpdate state = .ok after := by
  obtain ⟨next, ok⟩ := nextEpoch_ok state fits
  have not : ¬ Fork.shapella ≤ fork := Nat.not_le.mpr before
  simp only [processHistoricalRootsUpdate, not, ite_false, liftAccessor, liftArith, ok,
    Except.mapError, bind, Except.bind]
  split
  · obtain ⟨root, hr⟩ := hashTreeRoot_total (HistoricalBatch.mk state.blockRoots state.stateRoots)
    simp only [liftSsz, hr, appendHistoricalRoot, room, Except.mapError]
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- From Capella: the update of the historical summaries succeeds while their list has room.

A next slot must exist, and the circular buffers of roots must have a positive length. -/
theorem processHistoricalSummariesUpdate_total [NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat]
    (capella : .shapella ≤ fork) (fits : state.slot.toNat + 1 < 2 ^ 64)
    (room : (state.historicalSummaries capella).data.size < preset.HISTORICAL_ROOTS_LIMIT.toNat) :
    ∃ after, processHistoricalSummariesUpdate state capella = .ok after := by
  obtain ⟨next, ok⟩ := nextEpoch_ok state fits
  simp only [processHistoricalSummariesUpdate, liftAccessor, liftArith, ok, Except.mapError, bind,
    Except.bind]
  split
  · obtain ⟨r₁, h₁⟩ := hashTreeRoot_total state.blockRoots
    obtain ⟨r₂, h₂⟩ := hashTreeRoot_total state.stateRoots
    simp only [liftSsz, h₁, h₂, Except.mapError]
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- Before Altair: the rotation of the pending attestations always succeeds. -/
theorem processParticipationRecordUpdates_total (before : fork < .altair) :
    ∃ after, processParticipationRecordUpdates state = .ok after := by
  have : ¬ Fork.altair ≤ fork := Nat.not_le.mpr before
  simp only [processParticipationRecordUpdates, this, ite_false, pure, Except.pure]
  exact ⟨_, rfl⟩

end EthLib.Consensus
