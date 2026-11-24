module

public import EthLib.Consensus.BeaconApi.Committees
public import EthLib.Consensus.Gossip.SyncCommittee
public import EthLib.Consensus.Proofs.Accessors
public import EthLib.Consensus.Proofs.PayloadTimeliness
public import EthLib.Consensus.Proofs.ShufflePermutation
public import EthLib.Consensus.Proofs.Time
public import EthLib.Consensus.Proofs.BeaconApi.Responses
public import EthLib.Serialization.Proofs.Ssz.Typed.Collections
public import EthLib.Serialization.Proofs.Ssz.Typed.Container
import EthLib.Consensus.Proofs.BeaconApi.Encoding
import EthLib.Serialization.Proofs.Ssz.Typed.Bounds

/-!
# Proofs: the committee answers of the Beacon API

The beacon, sync and payload timeliness committee answers: what each holds, and when each refuses.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base

variable {preset : Preset} {fork : Fork}

/-! ## Beacon committees -/

/-- For a slot of the epoch of a shuffle, the beacon committee is cut from that shuffle. -/
private theorem getBeaconCommittee_of_shuffle {state : BeaconState preset fork} {epoch : Epoch}
    {active : Array ValidatorIndex} {shuffled : Array UInt64}
    (shuffleOk : attesterShuffle state epoch = .ok (active, shuffled)) {slot : Slot}
    (slotEpoch : computeEpochAtSlot preset slot = epoch) (index : CommitteeIndex) :
    getBeaconCommittee state slot index =
      beaconCommitteeOf preset slot index (getCommitteeCountPerSlot state epoch) active
        shuffled := by
  subst slotEpoch
  simp only [getBeaconCommittee, shuffleOk, bind, Except.bind]

/-- The positions of the rows of a grid, row after row, are the positions below its size. -/
private theorem flatMap_range_rows (rows width : Nat) :
    (List.range rows).flatMap (fun row => (List.range width).map (row * width + ·)) =
      List.range (rows * width) := by
  induction rows with
  | zero => simp
  | succ rows ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton, Nat.succ_mul,
      List.range_add]

/-- A committee is in the answer exactly when it is a beacon committee of the epoch that matches.

Its slot is in the epoch, its index is below the count of a slot, and it matches each filter.

Its members are those of the beacon committee of its slot and index. -/
theorem epochCommittees_mem {state : BeaconState preset fork} {epoch : Epoch}
    {index : Option CommitteeIndex} {slot : Option Slot} {committees : List Committee}
    (computed : epochCommittees state epoch index slot = .ok committees)
    {committee : Committee} :
    committee ∈ committees ↔
      computeEpochAtSlot preset committee.slot = epoch ∧
      committee.index < getCommitteeCountPerSlot state epoch ∧
      (∀ named ∈ index, named = committee.index) ∧ (∀ named ∈ slot, named = committee.slot) ∧
      getBeaconCommittee state committee.slot committee.index = .ok committee.validators := by
  simp only [epochCommittees, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨slots, slotsOk, ⟨active, shuffled⟩, shuffleOk, mapped⟩ := computed
  constructor
  · intro mem
    obtain ⟨⟨s, i⟩, posMem, made⟩ := mapM_ok_mem mapped committee mem
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at made
    obtain ⟨validators, validatorsOk, rfl⟩ := made
    simp only [List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_range,
      Prod.mk.injEq] at posMem
    obtain ⟨s', ⟨sMem, sFilter⟩, i', ⟨⟨n, nLt, rfl⟩, iFilter⟩, rfl, rfl⟩ := posMem
    have sEpoch := mem_epochSlots slotsOk sMem
    refine ⟨sEpoch, ?_, ?_, ?_,
      by rw [getBeaconCommittee_of_shuffle shuffleOk sEpoch]; exact validatorsOk⟩
    · have := (getCommitteeCountPerSlot state epoch).toNat_lt
      simp only [UInt64.lt_iff_toNat_lt, Nat.toUInt64_eq, UInt64.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by omega)]
      exact nLt
    · cases index <;> simp_all
    · cases slot <;> simp_all
  · rintro ⟨sEpoch, iLt, iFilter, sFilter, committeeOk⟩
    -- A committee with a value comes from a positive count, so an epoch has a slot.
    have positive : preset.SLOTS_PER_EPOCH ≠ 0 := by
      intro zero
      obtain ⟨_, _, count, _, _, countEq, countOk⟩ := getBeaconCommittee_ok committeeOk
      apply count_ne_zero_of_computeCommittee countOk
      apply UInt64.toNat_inj.mp
      rw [countEq, zero]
      simp
    have sMem := mem_epochSlots_of_epoch positive slotsOk sEpoch
    have iNat : committee.index.toNat.toUInt64 = committee.index := by simp
    have posMem : (committee.slot, committee.index) ∈
        (slots.filter fun s => slot.all (· == s)).flatMap fun s =>
          (((List.range (getCommitteeCountPerSlot state epoch).toNat).map Nat.toUInt64).filter
            fun i => index.all (· == i)).map (s, ·) := by
      simp only [List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_range, Prod.mk.injEq]
      refine ⟨committee.slot, ⟨sMem, ?_⟩, committee.index,
        ⟨⟨committee.index.toNat, UInt64.lt_iff_toNat_lt.mp iLt, iNat⟩, ?_⟩, rfl, rfl⟩
      · cases slot <;> simp_all
      · cases index <;> simp_all
    obtain ⟨found, foundMem, made⟩ := exists_mem_of_mapM_ok mapped posMem
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at made
    obtain ⟨validators, validatorsOk, rfl⟩ := made
    rw [getBeaconCommittee_of_shuffle shuffleOk sEpoch, validatorsOk, Except.ok.injEq]
      at committeeOk
    rw [committeeOk] at foundMem
    exact foundMem

/-- Without a filter, the committees of an epoch hold each active validator exactly once. -/
theorem epochCommittees_partition {state : BeaconState preset fork} {epoch : Epoch}
    {committees : List Committee}
    (computed : epochCommittees state epoch none none = .ok committees)
    -- An epoch must have at least one slot.
    (positive : preset.SLOTS_PER_EPOCH ≠ 0)
    -- The number of active validators times the number of committees of the epoch fits in 64 bits.
    (fits : (getActiveValidatorIndices state epoch).length *
      ((getCommitteeCountPerSlot state epoch).toNat * preset.SLOTS_PER_EPOCH.toNat) < 2 ^ 64) :
    -- The members of the committees, put end to end, are a permutation of the active validators.
    (committees.flatMap (·.validators.toList)).Perm (getActiveValidatorIndices state epoch) := by
  simp only [epochCommittees, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨slots, slotsOk, ⟨active, shuffled⟩, shuffleOk, mapped⟩ := computed
  have keepAll : ∀ {α : Type} (list : List α), list.filter (fun _ => true) = list :=
    fun _ => List.filter_eq_self.mpr fun _ _ => rfl
  simp only [Option.all_none, keepAll] at mapped
  obtain ⟨seed, seedOk, _, rfl⟩ := attesterShuffle_ok shuffleOk
  -- Each position of the epoch gives the committee that its place in the epoch numbers.
  have atPosition : ∀ x ∈ slots.flatMap (fun s =>
      ((List.range (getCommitteeCountPerSlot state epoch).toNat).map Nat.toUInt64).map (s, ·)),
      ∃ validators position count,
        beaconCommitteeOf preset x.1 x.2 (getCommitteeCountPerSlot state epoch)
          (getActiveValidatorIndices state epoch).toArray shuffled = .ok validators ∧
        position.toNat = (x.1 % preset.SLOTS_PER_EPOCH).toNat *
          (getCommitteeCountPerSlot state epoch).toNat + x.2.toNat ∧
        count.toNat = (getCommitteeCountPerSlot state epoch).toNat *
          preset.SLOTS_PER_EPOCH.toNat ∧
        computeCommittee preset (getActiveValidatorIndices state epoch).toArray seed position
          count = .ok validators := by
    intro x member
    obtain ⟨committee, _, made⟩ := exists_mem_of_mapM_ok mapped member
    simp only [bind_ok_iff, pure, Except.pure] at made
    obtain ⟨validators, validatorsOk, _⟩ := made
    have xEpoch : computeEpochAtSlot preset x.1 = epoch := by
      simp only [List.mem_flatMap, List.mem_map] at member
      obtain ⟨s, sMem, _, _, rfl⟩ := member
      exact mem_epochSlots slotsOk sMem
    have viaGet := validatorsOk
    rw [← getBeaconCommittee_of_shuffle shuffleOk xEpoch] at viaGet
    obtain ⟨seed', position, count, seedOk', positionEq, countEq, committeeOk⟩ :=
      getBeaconCommittee_ok viaGet
    rw [xEpoch, seedOk, Except.ok.injEq] at seedOk'
    subst seedOk'
    rw [xEpoch] at positionEq countEq committeeOk
    exact ⟨validators, position, count, validatorsOk, positionEq, countEq, committeeOk⟩
  obtain ⟨slotsFit, slotsEq⟩ := epochSlots_eq_ok_iff.mp slotsOk
  have lengthPos : 0 < preset.SLOTS_PER_EPOCH.toNat :=
    Nat.pos_of_ne_zero fun zero => positive (UInt64.toNat_inj.mp (by simpa using zero))
  have perPos : 0 < (getCommitteeCountPerSlot state epoch).toNat :=
    UInt64.le_iff_toNat_le.mp (one_le_getCommitteeCountPerSlot state epoch)
  -- The first committee of the epoch fixes the count and bounds the active validators.
  have firstMem : (epoch * preset.SLOTS_PER_EPOCH + (0 : Nat).toUInt64, (0 : Nat).toUInt64) ∈
      slots.flatMap (fun s =>
        ((List.range (getCommitteeCountPerSlot state epoch).toNat).map Nat.toUInt64).map
          (s, ·)) := by
    rw [slotsEq]
    simp only [List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq]
    exact ⟨_, ⟨0, lengthPos, rfl⟩, _, ⟨0, perPos, rfl⟩, rfl, rfl⟩
  obtain ⟨_, _, count, _, _, countEq, first⟩ := atPosition _ firstMem
  have countFits : (getCommitteeCountPerSlot state epoch).toNat * preset.SLOTS_PER_EPOCH.toNat <
      2 ^ 64 := countEq ▸ count.toNat_lt
  have sizeFits : (getActiveValidatorIndices state epoch).toArray.size < 2 ^ 64 := by
    have : 1 ≤ (getCommitteeCountPerSlot state epoch).toNat * preset.SLOTS_PER_EPOCH.toNat :=
      Nat.mul_pos perPos lengthPos
    simp only [List.size_toArray]
    exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ this) fits
  have small := le_of_computeCommittee sizeFits first
  have sliceFits : (getActiveValidatorIndices state epoch).toArray.size * count.toNat < 2 ^ 64 := by
    simpa [countEq] using fits
  -- Each committee is the slice of the shuffle at its place in the epoch.
  have sliceAt : ∀ x ∈ slots.flatMap (fun s =>
      ((List.range (getCommitteeCountPerSlot state epoch).toNat).map Nat.toUInt64).map (s, ·)),
      (do
        let validators ← beaconCommitteeOf preset x.1 x.2 (getCommitteeCountPerSlot state epoch)
          (getActiveValidatorIndices state epoch).toArray shuffled
        pure { index := x.2, slot := x.1, validators := validators } :
          Except AccessorError Committee) =
        .ok { index := x.2, slot := x.1, validators := (Shuffle.committeeSlice preset
          (getActiveValidatorIndices state epoch).toArray seed count.toNat
          ((x.1 % preset.SLOTS_PER_EPOCH).toNat * (getCommitteeCountPerSlot state epoch).toNat +
            x.2.toNat)).toArray } := by
    intro x member
    obtain ⟨validators, position, count', validatorsOk, positionEq, countEq', committeeOk⟩ :=
      atPosition x member
    have sameCount : count' = count := UInt64.toNat_inj.mp (countEq'.trans countEq.symm)
    subst sameCount
    simp only [List.mem_flatMap, List.mem_map, List.mem_range] at member
    obtain ⟨s, _, _, ⟨n, nLt, rfl⟩, rfl⟩ := member
    have nNat : n.toUInt64.toNat = n := by
      have := (getCommitteeCountPerSlot state epoch).toNat_lt
      simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by omega)
    have modLt : (s % preset.SLOTS_PER_EPOCH).toNat < preset.SLOTS_PER_EPOCH.toNat := by
      rw [UInt64.toNat_mod]
      exact Nat.mod_lt _ lengthPos
    have positionLt : position.toNat < count'.toNat := by
      rw [positionEq, countEq', nNat]
      calc (s % preset.SLOTS_PER_EPOCH).toNat * (getCommitteeCountPerSlot state epoch).toNat + n
          < ((s % preset.SLOTS_PER_EPOCH).toNat + 1) *
              (getCommitteeCountPerSlot state epoch).toNat := by rw [Nat.succ_mul]; omega
        _ ≤ preset.SLOTS_PER_EPOCH.toNat * (getCommitteeCountPerSlot state epoch).toNat :=
          Nat.mul_le_mul_right _ modLt
        _ = _ := Nat.mul_comm _ _
    have sliceOk := computeCommittee_of_mem (preset := preset) (seed := seed) small sliceFits _
      (List.mem_range.mpr positionLt)
    rw [UInt64.ofNat_toNat, committeeOk, Except.ok.injEq] at sliceOk
    rw [validatorsOk, ← positionEq, sliceOk]
    rfl
  have committeesEq := (mapM_eq_ok_map sliceAt).symm.trans mapped
  rw [Except.ok.injEq] at committeesEq
  subst committeesEq
  rw [List.flatMap_map]
  -- The places of the committees, in order, are all the places of the epoch.
  have placesEq : (slots.flatMap (fun s =>
      ((List.range (getCommitteeCountPerSlot state epoch).toNat).map Nat.toUInt64).map
        (s, ·))).map (fun x : Slot × CommitteeIndex =>
          (x.1 % preset.SLOTS_PER_EPOCH).toNat * (getCommitteeCountPerSlot state epoch).toNat +
            x.2.toNat) = List.range count.toNat := by
    rw [slotsEq, List.map_flatMap, List.flatMap_map, countEq, Nat.mul_comm,
      ← flatMap_range_rows, List.flatMap_def, List.flatMap_def]
    congr 1
    apply List.map_congr_left
    intro offset offsetMem
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro n nMem
    have offsetLt := List.mem_range.mp offsetMem
    have nLt := List.mem_range.mp nMem
    have perSmall := (getCommitteeCountPerSlot state epoch).toNat_lt
    simp only [Function.comp_apply, UInt64.toNat_mod, toNat_epochSlot slotsFit offsetLt,
      Nat.mul_comm epoch.toNat, Nat.mul_add_mod, Nat.mod_eq_of_lt offsetLt, Nat.toUInt64_eq,
      UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans nLt perSmall)]
  have partition := computeCommittee_partition (preset := preset) (seed := seed) sliceFits
    (UInt64.lt_iff_toNat_lt.mpr (by rw [countEq]; exact Nat.mul_pos perPos lengthPos))
    (computeCommittee_mapM small sliceFits)
  rw [List.flatMap_map, ← placesEq, List.flatMap_map] at partition
  simpa using partition

/-- An epoch after the next one gives the error with code 400. -/
theorem committeesResponse_epoch_bound {state : BeaconState preset fork} {epoch : Epoch}
    (late : (getCurrentEpoch state).toNat + 1 < epoch.toNat)
    (index : Option CommitteeIndex) (slot : Option Slot) :
    ∃ message, committeesResponse state (some epoch) index slot =
      .error { code := 400, message } := by
  simp only [committeesResponse, Option.getD_some, Nat.not_le.mpr late]
  exact ⟨_, rfl⟩

/-- An epoch whose RANDAO mix the state no longer holds gives the error with code 400.

Its mix is read from the buffer of the state.

The epoch plus the length of that buffer is at most the next epoch plus the lookahead of seeds. -/
theorem committeesResponse_epoch_old {state : BeaconState preset fork} {epoch : Epoch}
    (old : epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat ≤
      (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1)
    (index : Option CommitteeIndex) (slot : Option Slot) :
    ∃ message, committeesResponse state (some epoch) index slot =
      .error { code := 400, message } := by
  by_cases late : (getCurrentEpoch state).toNat + 1 < epoch.toNat
  · exact committeesResponse_epoch_bound late index slot
  · simp only [committeesResponse, Option.getD_some, Nat.not_lt.mp late, Nat.not_lt.mpr old]
    exact ⟨_, rfl⟩

/-! ## Sync committees -/

/-- Each seat of the answer holds the first validator whose key is the key of the seat.

The keys are those of the sync committee of the period of the epoch. -/
theorem epochSyncCommittees_validators {state : BeaconState preset fork}
    {altair : .altair ≤ fork} {epoch : Epoch} {answer : SyncCommitteeIndices}
    {committee : SyncCommittee preset}
    (committeeOk : syncCommitteeOf state altair epoch = .ok committee)
    (computed : epochSyncCommittees state altair epoch = .ok answer) :
    answer.validators.length = preset.SYNC_COMMITTEE_SIZE.toNat ∧
      ∀ seat (seatLt : seat < preset.SYNC_COMMITTEE_SIZE.toNat),
        answer.validators[seat]? = resolveValidatorId state (.pubkey committee.pubkeys[seat]) := by
  simp only [epochSyncCommittees, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨found, foundOk, validators, validatorsOk, rfl⟩ := computed
  rw [committeeOk, Except.ok.injEq] at foundOk
  subst foundOk
  have length := mapM_ok_length validatorsOk
  simp only [Vector.length_toList] at length
  refine ⟨length, fun seat seatLt => ?_⟩
  have step := mapM_ok_getElem validatorsOk seat (by simpa using seatLt)
  simp only [Vector.getElem_toList] at step
  split at step <;> simp_all

/-- The slices of a committee are the key lists of its subcommittees, in order. -/
theorem syncAggregates_pubkeys (committee : SyncCommittee preset) :
    syncAggregates preset committee.pubkeys.toList =
      (List.range Networking.Enr.SYNC_COMMITTEE_SUBNET_COUNT).map
        (syncSubcommitteePubkeys committee) := rfl

/-- The slices of the answer, put end to end, give back the indices of the seats.

The count of subnets must divide the size of a sync committee. -/
theorem epochSyncCommittees_aggregates {state : BeaconState preset fork}
    {altair : .altair ≤ fork} {epoch : Epoch} {answer : SyncCommitteeIndices}
    (computed : epochSyncCommittees state altair epoch = .ok answer)
    (divides : Networking.Enr.SYNC_COMMITTEE_SUBNET_COUNT ∣ preset.SYNC_COMMITTEE_SIZE.toNat) :
    answer.validatorAggregates.flatten = answer.validators := by
  simp only [epochSyncCommittees, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨committee, _, validators, validatorsOk, rfl⟩ := computed
  have length := mapM_ok_length validatorsOk
  simp only [Vector.length_toList] at length
  -- The slices are those of the bounds at the multiples of the size of a slice.
  have slices := Shuffle.flatMap_slices validators (· * syncSubcommitteeSize preset)
    (Nat.zero_mul _) (fun part => Nat.mul_le_mul_right _ (Nat.le_succ part))
    Networking.Enr.SYNC_COMMITTEE_SUBNET_COUNT
  simp only [Nat.succ_mul, Nat.add_sub_cancel_left] at slices
  have whole : Networking.Enr.SYNC_COMMITTEE_SUBNET_COUNT * syncSubcommitteeSize preset =
      validators.length := by
    rw [length, syncSubcommitteeSize, Nat.mul_div_cancel' divides]
  rw [whole, List.take_length] at slices
  simp only [syncAggregates, ← List.flatMap_def]
  exact slices

/-! ## Payload timeliness committees -/

/-- The window has no position for a slot before the fork, too old, or past the lookahead. -/
private theorem ptcWindowPosition_error_of {config : Config} {state : BeaconState preset fork}
    {slot : Slot}
    (fits : (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat < 2 ^ 64)
    (outside : computeEpochAtSlot preset slot < config.GLOAS_FORK_EPOCH ∨
      (computeEpochAtSlot preset slot).toNat + 1 < (getCurrentEpoch state).toNat ∨
      (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat <
        (computeEpochAtSlot preset slot).toNat) :
    ∃ error, ptcWindowPosition config state slot = .error error := by
  by_cases forkLe : config.GLOAS_FORK_EPOCH ≤ computeEpochAtSlot preset slot
  case neg =>
    simp only [ptcWindowPosition, forkLe]
    exact ⟨_, rfl⟩
  rcases outside with before | old | late
  · exact absurd forkLe (UInt64.not_le.mpr before)
  · -- An epoch two or more before that of the state.
    have lt : computeEpochAtSlot preset slot < getCurrentEpoch state :=
      UInt64.lt_iff_toNat_lt.mpr (by omega)
    have ne : computeEpochAtSlot preset slot + 1 ≠ getCurrentEpoch state := by
      intro same
      have sameNat := congrArg UInt64.toNat same
      rw [Uint64.toNat_add_of_lt (by simp; omega)] at sameNat
      simp at sameNat
      omega
    simp only [ptcWindowPosition, forkLe, lt, ne]
    exact ⟨_, rfl⟩
  · -- An epoch past the lookahead.
    have notLt : ¬computeEpochAtSlot preset slot < getCurrentEpoch state :=
      fun lt => by have := UInt64.lt_iff_toNat_lt.mp lt; omega
    have notLe :
        ¬computeEpochAtSlot preset slot ≤ getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD :=
      fun le => by
        have := UInt64.le_iff_toNat_le.mp le
        rw [Uint64.toNat_add_of_lt fits] at this
        omega
    simp only [ptcWindowPosition, forkLe, notLt, liftArith, Uint64.addChecked_of_lt fits,
      Except.mapError, bind, Except.bind, notLe, ite_true, ite_false]
    exact ⟨_, rfl⟩

/-- From Gloas, an answer is the committee that the window of the state holds for the slot. -/
theorem statePtc_ok_iff {config : Config} {state : BeaconState preset fork}
    (gloas : .glamsterdam ≤ fork) {slot : Option Slot} {answer : PtcResponse preset} :
    statePtc config state slot = .ok answer ↔
      answer.slot = slot.getD state.slot ∧
      getPtc config state gloas answer.slot = .ok answer.validators := by
  simp only [statePtc, gloas, dite_true]
  constructor
  · intro answered
    split at answered
    · rename_i validators committeeOk
      cases answered
      exact ⟨rfl, committeeOk⟩
    · cases answered
  · rintro ⟨slotEq, committeeOk⟩
    rw [← slotEq, committeeOk]
    rfl

/-- The PTC answer is an error exactly when one of four conditions holds. -/
theorem statePtc_error_iff {config : Config} {state : BeaconState preset fork} {slot : Option Slot}
    -- An epoch must have at least one slot.
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    -- The last epoch of the lookahead must fit in 64 bits.
    (fits : (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat < 2 ^ 64)
    -- The length of the window must fit in 64 bits.
    (windowFits :
      (preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64) :
    (∃ error, statePtc config state slot = .error error) ↔
      -- The state is before Gloas, or the epoch of the slot is before the Gloas fork epoch.
      ¬.glamsterdam ≤ fork ∨
      computeEpochAtSlot preset (slot.getD state.slot) < config.GLOAS_FORK_EPOCH ∨
      -- Or the epoch of the slot is before the current epoch minus one, or past the lookahead.
      (computeEpochAtSlot preset (slot.getD state.slot)).toNat + 1 <
        (getCurrentEpoch state).toNat ∨
      (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat <
        (computeEpochAtSlot preset (slot.getD state.slot)).toNat := by
  by_cases gloas : .glamsterdam ≤ fork
  case neg =>
    simp only [statePtc, gloas, dite_false, not_false_eq_true, true_or, iff_true]
    exact ⟨_, rfl⟩
  simp only [statePtc, gloas, dite_true, not_true_eq_false, false_or]
  generalize slot.getD state.slot = slot
  constructor
  · rintro ⟨error, failed⟩
    split at failed
    · cases failed
    rename_i fault committeeFailed
    -- Inside the window, the position has an entry, so the committee has a value.
    refine Classical.byContradiction fun inside => ?_
    simp only [not_or, UInt64.not_lt, Nat.not_lt] at inside
    obtain ⟨forkLe, recent, lookahead⟩ := inside
    obtain ⟨_, committeeOk⟩ := getPtc_exists gloas positive fits windowFits forkLe recent lookahead
    rw [committeeOk] at committeeFailed
    cases committeeFailed
  · intro outside
    obtain ⟨fault, positionFailed⟩ := ptcWindowPosition_error_of fits outside
    have committeeFailed : getPtc config state gloas slot = .error fault := by
      simp only [getPtc, positionFailed, bind, Except.bind]
    rw [committeeFailed]
    exact ⟨_, rfl⟩

/-- Every error of the PTC answer has code 400. -/
theorem statePtc_error_code {config : Config} {state : BeaconState preset fork}
    {slot : Option Slot} {error : ErrorMessage}
    (failed : statePtc config state slot = .error error) : error.code = 400 := by
  unfold statePtc at failed
  split at failed
  · simp only at failed
    split at failed
    · cases failed
    · cases failed
      rfl
  · cases failed
    rfl

/-! ## The PTC response -/

-- The two field names differ, and the vector of members is lawful once the PTC is not empty.
instance [NeZero preset.PTC_SIZE.toNat] : Serialization.Ssz.LawfulSszType (PtcResponse preset) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

/-- The PTC response in JSON refuses exactly when the answer does, with the same error.

It needs a preset whose PTC is not empty. -/
theorem ptcResponse_eq_error_iff [NeZero preset.PTC_SIZE.toNat] {config : Config}
    {state : BeaconState preset fork} {slot : Option Slot} {error : ErrorMessage} :
    ptcResponse config state slot = .error error ↔ statePtc config state slot = .error error := by
  unfold ptcResponse
  exact apiJsonOr500_bind_eq_error_iff fun answer _ => toApiJson_total answer

/-- Every error of the PTC response in JSON has code 400.

It needs a preset whose PTC is not empty. -/
theorem ptcResponse_error_code [NeZero preset.PTC_SIZE.toNat] {config : Config}
    {state : BeaconState preset fork} {slot : Option Slot} {error : ErrorMessage}
    (failed : ptcResponse config state slot = .error error) : error.code = 400 :=
  statePtc_error_code (ptcResponse_eq_error_iff.mp failed)

/-- The PTC answer in SSZ refuses exactly when the answer does, with the same error.

It needs a preset whose PTC is not empty, and whose answer stays below `2^32` bytes. -/
theorem ptcSsz_eq_error_iff [NeZero preset.PTC_SIZE.toNat]
    -- The answer has 8 bytes for the slot and 8 bytes for each member.
    (small : 8 + preset.PTC_SIZE.toNat * 8 < 2 ^ 32) {config : Config}
    {state : BeaconState preset fork} {slot : Option Slot} {error : ErrorMessage} :
    ptcSsz config state slot = .error error ↔ statePtc config state slot = .error error := by
  unfold ptcSsz
  -- Every part of the answer has a fixed size, so its largest encoding is its only one.
  exact apiSszOr500_bind_eq_error_iff fun answer _ =>
    Serialization.Ssz.SszType.serialize_exists_ok_of_maxSize answer rfl small

/-- Every error of the PTC answer in SSZ has code 400.

It needs a preset whose PTC is not empty, and whose answer stays below `2^32` bytes. -/
theorem ptcSsz_error_code [NeZero preset.PTC_SIZE.toNat]
    (small : 8 + preset.PTC_SIZE.toNat * 8 < 2 ^ 32) {config : Config}
    {state : BeaconState preset fork} {slot : Option Slot} {error : ErrorMessage}
    (failed : ptcSsz config state slot = .error error) : error.code = 400 :=
  statePtc_error_code ((ptcSsz_eq_error_iff small).mp failed)

end EthLib.Consensus.BeaconApi
