module

public import EthLib.Consensus.Proofs.Accessors
public import EthLib.Consensus.Proofs.Containers.Misc
public import EthLib.Consensus.Transition.ForkBoundary
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

One slot then succeeds when a next slot exists and, at the end of an epoch, the epoch succeeds.

A run of slots succeeds when each state it reaches allows the next step.

Those conditions on the reached states are where the bounds of a run are applied.
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

/-- One slot succeeds when a next slot exists and, at the end of an epoch, the epoch succeeds.

The epoch transition runs on the state with the roots of the slot cached.

The SSZ type of the state is assumed lawful, and the buffers of roots have a positive length. -/
theorem advanceSlot_exists_ok {config : Config} {checks : SignatureChecks}
    [LawfulSszType (BeaconState preset fork)] [NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat]
    (fits : state.slot.toNat + 1 < 2 ^ 64)
    (epoch : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
      ∀ cached, processSlot state = .ok cached →
        ∃ epoched, processEpoch config checks cached = .ok epoched) :
    ∃ after, advanceSlot config checks state = .ok after := by
  obtain ⟨cached, cachedOk⟩ := processSlot_total fits
  have next : addChecked state.slot 1 = .ok (state.slot + 1) :=
    addChecked_of_lt (by simpa using fits)
  have sum : (state.slot + 1).toNat = state.slot.toNat + 1 := by
    have := (addChecked_ok_iff.mp next).2
    simpa using this
  simp only [advanceSlot, liftAccessor, liftArith, next, cachedOk, Except.mapError, bind,
    Except.bind]
  by_cases boundary : (state.slot + 1) % preset.SLOTS_PER_EPOCH = 0
  · have boundaryNat : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 := by
      have := congrArg UInt64.toNat boundary
      rwa [UInt64.toNat_mod, sum] at this
    obtain ⟨epoched, epochedOk⟩ := epoch boundaryNat cached cachedOk
    simp only [epochIfLast, boundary, ↓reduceIte, epochedOk]
    exact ⟨_, rfl⟩
  · simp only [epochIfLast, boundary, ↓reduceIte, pure, Except.pure]
    exact ⟨_, rfl⟩

/-- A run of slots within one fork succeeds when each state it reaches allows one more slot.

Each state that the run reaches before its end must have a next slot.

At the end of an epoch, the epoch transition must succeed on that state with its roots cached. -/
theorem advanceSlots_exists_ok {config : Config} {checks : SignatureChecks}
    [LawfulSszType (BeaconState preset fork)] [NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat] :
    ∀ {count : Nat} {state : BeaconState preset fork},
      (∀ steps < count, ∀ reached, advanceSlots config checks steps state = .ok reached →
        reached.slot.toNat + 1 < 2 ^ 64 ∧
          ((reached.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 →
            ∀ cached, processSlot reached = .ok cached →
              ∃ epoched, processEpoch config checks cached = .ok epoched)) →
      ∃ after, advanceSlots config checks count state = .ok after
  | 0, state, _ => ⟨state, rfl⟩
  | count + 1, state, allowed => by
    obtain ⟨fits, epoch⟩ := allowed 0 (Nat.succ_pos _) state rfl
    obtain ⟨next, nextOk⟩ := advanceSlot_exists_ok fits epoch
    obtain ⟨after, afterOk⟩ := advanceSlots_exists_ok (count := count) (state := next)
      fun steps below reached reachedOk => allowed (steps + 1) (by omega) reached (by
        simp only [advanceSlots, nextOk, bind, Except.bind]
        exact reachedOk)
    exact ⟨after, by simp only [advanceSlots, nextOk, bind, Except.bind]; exact afterOk⟩

/-- A run of slots across forks succeeds when each state it reaches allows one more step.

A step is one slot, then the upgrades that are due at the slot it reaches. -/
theorem advanceSlotsAcross_exists_ok {config : Config} {checks : SignatureChecks} :
    ∀ {count : Nat} {forked : ForkedBeaconState preset},
      (∀ steps < count, ∀ reached, advanceSlotsAcross config checks steps forked = .ok reached →
        ∃ next, advanceSlotAcross config checks reached = .ok next) →
      ∃ after, advanceSlotsAcross config checks count forked = .ok after
  | 0, forked, _ => ⟨forked, rfl⟩
  | count + 1, forked, allowed => by
    obtain ⟨next, nextOk⟩ := allowed 0 (Nat.succ_pos _) forked rfl
    obtain ⟨after, afterOk⟩ := advanceSlotsAcross_exists_ok (count := count) (forked := next)
      fun steps below reached reachedOk => allowed (steps + 1) (by omega) reached (by
        simp only [advanceSlotsAcross, nextOk, bind, Except.bind]
        exact reachedOk)
    exact ⟨after, by simp only [advanceSlotsAcross, nextOk, bind, Except.bind]; exact afterOk⟩

/-- The advance to a later slot across forks succeeds when each state it reaches allows a step.

The run has as many steps as the later slot is ahead of the state. -/
theorem processSlotsAcross_exists_ok {config : Config} {checks : SignatureChecks}
    {forked : ForkedBeaconState preset} {slot : Slot} (later : forked.state.slot < slot)
    (step : ∀ steps < slot.toNat - forked.state.slot.toNat, ∀ reached,
      advanceSlotsAcross config checks steps forked = .ok reached →
        ∃ next, advanceSlotAcross config checks reached = .ok next) :
    ∃ after, processSlotsAcross config checks forked slot = .ok after := by
  obtain ⟨after, afterOk⟩ := advanceSlotsAcross_exists_ok step
  refine ⟨after, ?_⟩
  have ensured : ensure (forked.state.slot < slot)
      (TransitionError.slotNotAfter slot forked.state.slot) = .ok () := ensure_ok_iff.mpr later
  simp only [processSlotsAcross, ensured, bind, Except.bind]
  exact afterOk

end EthLib.Consensus
