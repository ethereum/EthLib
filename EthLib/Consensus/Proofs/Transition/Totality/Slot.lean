module

public import EthLib.Consensus.Proofs.Accessors
public import EthLib.Consensus.Proofs.Containers.Misc
public import EthLib.Consensus.Transition.StateTransition

/-!
# Proofs: the caching of a slot, the resets of an epoch and the update of the history succeed

Advancing a state to a later slot can fail, for example on an overflow or on a full list.

This file shows that some of its steps succeed, under small hypotheses.

Each hypothesis is one that a run of slots can carry from one step to the next.

So each step assumes that a next slot exists, even where a next epoch would be enough.

The caching of a slot succeeds when a next slot exists.

The SSZ type of the state is assumed lawful, and its buffers of roots have a positive length.

The resets of an epoch succeed when a next slot exists.

Those that write a circular buffer also need it to have a positive length.

The update of the history succeeds while its list has room for one more entry.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz SszType

variable {preset : Preset} {fork : Base.Fork} {state : BeaconState preset fork}

/-- From Gloas: clearing the availability of the next payload succeeds when a next slot exists.

The circular buffer of availability bits must have a positive length. -/
theorem unsetNextPayloadAvailability_total [NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat]
    (gloas : .glamsterdam ≤ fork) (fits : state.slot.toNat + 1 < 2 ^ 64) :
    ∃ after, unsetNextPayloadAvailability state gloas = .ok after := by
  have next : addChecked state.slot 1 = .ok (state.slot + 1) :=
    addChecked_of_lt (by simpa using fits)
  obtain ⟨bits, written⟩ := writeCircular_total
    (state.executionPayloadAvailability gloas).bits (state.slot + 1) false
  simp only [unsetNextPayloadAvailability, liftArith, next, written, Except.mapError, bind,
    Except.bind]
  exact ⟨_, rfl⟩

/-- The caching of a slot succeeds when a next slot exists.

The SSZ type of the state is assumed lawful, which holds when its fixed lengths are positive.

The circular buffers of roots must have a positive length.

Before Gloas the step succeeds without a next slot.

The hypothesis is kept at every fork, so that a run of slots can supply it. -/
theorem processSlot_total [LawfulSszType (BeaconState preset fork)]
    [NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat] (fits : state.slot.toNat + 1 < 2 ^ 64) :
    ∃ after, processSlot state = .ok after := by
  obtain ⟨root, hr⟩ := hashTreeRoot_total state
  obtain ⟨w, hw⟩ := writeCircularRooted_total state.stateRoots state.slot root
  simp only [processSlot, liftSsz, hr, liftAccessor, hw, Except.mapError, bind, Except.bind]
  obtain ⟨header, hH⟩ : ∃ header : BeaconBlockHeader,
      header = if state.latestBlockHeader.stateRoot = Vector.replicate 32 0 then
        { state.latestBlockHeader with stateRoot := root } else state.latestBlockHeader :=
    ⟨_, rfl⟩
  rw [← hH]
  obtain ⟨r, hr'⟩ := hashTreeRoot_total header
  obtain ⟨w', hw'⟩ := writeCircularRooted_total state.blockRoots state.slot r
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
  obtain ⟨next, ok⟩ := addChecked_getCurrentEpoch_one_total state fits
  obtain ⟨w, hw⟩ := writeCircularRooted_total state.slashings next 0
  simp only [processSlashingsReset, liftAccessor, liftArith, ok, hw, Except.mapError, bind,
    Except.bind]
  exact ⟨_, rfl⟩

/-- The reset of the RANDAO mixes succeeds when a next slot exists.

The circular buffer of mixes must have a positive length. -/
theorem processRandaoMixesReset_total [NeZero preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat]
    (fits : state.slot.toNat + 1 < 2 ^ 64) :
    ∃ after, processRandaoMixesReset state = .ok after := by
  obtain ⟨next, ok⟩ := addChecked_getCurrentEpoch_one_total state fits
  obtain ⟨mix, hm⟩ := readCircular_total state.randaoMixes.elements (getCurrentEpoch state)
  obtain ⟨w, hw⟩ := writeCircularRooted_total state.randaoMixes next mix
  simp only [processRandaoMixesReset, getRandaoMix, liftAccessor, liftArith, ok, hm, hw,
    Except.mapError, bind, Except.bind]
  exact ⟨_, rfl⟩

/-- Before Heze: the reset of the votes on the deposit contract succeeds when a next slot exists. -/
theorem processEth1DataReset_total (before : fork < .hegota)
    (fits : state.slot.toNat + 1 < 2 ^ 64) :
    ∃ after, processEth1DataReset before state = .ok after := by
  obtain ⟨next, ok⟩ := addChecked_getCurrentEpoch_one_total state fits
  simp only [processEth1DataReset, liftAccessor, liftArith, ok, Except.mapError, bind,
    Except.bind]
  split <;> exact ⟨_, rfl⟩

/-- Before Capella: the update of the historical roots succeeds while their list has room.

A next slot must exist. -/
theorem processHistoricalRootsUpdate_total (before : fork < .shapella)
    (fits : state.slot.toNat + 1 < 2 ^ 64)
    (room : state.historicalRoots.data.size < preset.HISTORICAL_ROOTS_LIMIT.toNat) :
    ∃ after, processHistoricalRootsUpdate state = .ok after := by
  obtain ⟨next, ok⟩ := addChecked_getCurrentEpoch_one_total state fits
  have nextPos : next ≠ 0 := by
    intro zero
    have grown := (addChecked_ok_iff.mp ok).2
    rw [zero] at grown
    have : (getCurrentEpoch state).toNat + 1 = 0 := by simpa using grown.symm
    omega
  have notCapella : ¬ Fork.shapella ≤ fork := Nat.not_le.mpr before
  by_cases empty : preset.SLOTS_PER_HISTORICAL_ROOT = 0
  · have noSpan : ¬ next % (preset.SLOTS_PER_HISTORICAL_ROOT / preset.SLOTS_PER_EPOCH) = 0 := by
      rw [empty]
      simpa using nextPos
    simp only [processHistoricalRootsUpdate, notCapella, ite_false, liftAccessor, liftArith, ok,
      Except.mapError, bind, Except.bind, noSpan]
    exact ⟨_, rfl⟩
  · haveI : NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat :=
      ⟨fun zero => empty (UInt64.toNat_inj.mp (by simpa using zero))⟩
    simp only [processHistoricalRootsUpdate, notCapella, ite_false, liftAccessor, liftArith, ok,
      Except.mapError, bind, Except.bind]
    split
    · obtain ⟨root, hr⟩ :=
        hashTreeRoot_total (HistoricalBatch.mk state.blockRoots state.stateRoots)
      simp only [liftSsz, hr, appendHistoricalRoot, room, Except.mapError]
      exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-- From Capella: the update of the historical summaries succeeds while their list has room.

A next slot must exist. -/
theorem processHistoricalSummariesUpdate_total (capella : .shapella ≤ fork)
    (fits : state.slot.toNat + 1 < 2 ^ 64)
    (room : (state.historicalSummaries capella).data.size < preset.HISTORICAL_ROOTS_LIMIT.toNat) :
    ∃ after, processHistoricalSummariesUpdate state capella = .ok after := by
  obtain ⟨next, ok⟩ := addChecked_getCurrentEpoch_one_total state fits
  have nextPos : next ≠ 0 := by
    intro zero
    have grown := (addChecked_ok_iff.mp ok).2
    rw [zero] at grown
    have : (getCurrentEpoch state).toNat + 1 = 0 := by simpa using grown.symm
    omega
  by_cases empty : preset.SLOTS_PER_HISTORICAL_ROOT = 0
  · have noSpan : ¬ next % (preset.SLOTS_PER_HISTORICAL_ROOT / preset.SLOTS_PER_EPOCH) = 0 := by
      rw [empty]
      simpa using nextPos
    simp only [processHistoricalSummariesUpdate, liftAccessor, liftArith, ok, Except.mapError,
      bind, Except.bind, noSpan]
    exact ⟨_, rfl⟩
  · haveI : NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat :=
      ⟨fun zero => empty (UInt64.toNat_inj.mp (by simpa using zero))⟩
    simp only [processHistoricalSummariesUpdate, liftAccessor, liftArith, ok, Except.mapError,
      bind, Except.bind]
    split
    · obtain ⟨blocks, hb⟩ := hashTreeRoot_total state.blockRoots
      obtain ⟨states, hs⟩ := hashTreeRoot_total state.stateRoots
      simp only [liftSsz, hb, hs, Except.mapError]
      exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

end EthLib.Consensus
