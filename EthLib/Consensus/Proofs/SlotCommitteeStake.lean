module

public import EthLib.Consensus.Proofs.StakeMovement
import EthLib.Base.Proofs.Forall2
import EthLib.Consensus.Proofs.Accessors
import EthLib.Consensus.Proofs.ShufflePermutation
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.Totality.PtcWindow
import Mathlib.Data.Nat.ModEq

/-!
# Proofs: honest votes keep two thirds without the committees of one slot

A block includes an attestation one slot after the slot of the attestation at the earliest.

So the test of an epoch at its end never counts the committees of its last slot.

The committees of one slot cut a contiguous share of the shuffled active validators.

That share holds at most the active count over the slots of an epoch, plus one validator.

Those validators are active in the epoch of the slot, which a run fixes several epochs ahead.

So the margin at the first state of the run asks two thirds without any such small set of them.

Then the honest validators outside the committees of one slot keep two thirds at a later state.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models DirectSafety DirectSafety.Apriori

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- A beacon committee holds the gap between the bounds of its place among those of the epoch.

Its place counts the committees of the earlier slots of the epoch, then its index. -/
private theorem size_of_getBeaconCommittee {fork : Base.Fork} {state : BeaconState preset fork}
    {slot : Slot} {index : CommitteeIndex} {committee : Array ValidatorIndex}
    (computed : getBeaconCommittee state slot index = .ok committee) :
    committee.size =
      (getActiveValidatorIndices state (computeEpochAtSlot preset slot)).length *
          ((slot % preset.SLOTS_PER_EPOCH).toNat *
            (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat +
              index.toNat + 1) /
        ((getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat *
          preset.SLOTS_PER_EPOCH.toNat) -
      (getActiveValidatorIndices state (computeEpochAtSlot preset slot)).length *
          ((slot % preset.SLOTS_PER_EPOCH).toNat *
            (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat +
              index.toNat) /
        ((getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat *
          preset.SLOTS_PER_EPOCH.toNat) := by
  obtain ⟨seed, position, count, -, positionEq, countEq, committeeOk⟩ :=
    getBeaconCommittee_ok computed
  rw [computeCommittee, bind_ok_iff] at committeeOk
  obtain ⟨shuffled, -, cut⟩ := committeeOk
  rw [(size_of_shuffledCommittee cut).2, positionEq, countEq, List.size_toArray]

/-- The committees of a slot hold at most the active count over the slots of an epoch, plus one.

The count is that of the active validators in the epoch of the slot.

The committees are read in turn, one for each index below the count of the slot. -/
theorem sum_size_le_of_mapM_getBeaconCommittee {fork : Base.Fork}
    {state : BeaconState preset fork} {slot : Slot} {committees : List (Array ValidatorIndex)}
    (committeesOk : (List.range
        (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat).mapM
      (fun position => getBeaconCommittee state slot position.toUInt64) = .ok committees) :
    (committees.map Array.size).sum ≤
      (getActiveValidatorIndices state (computeEpochAtSlot preset slot)).length /
        preset.SLOTS_PER_EPOCH.toNat + 1 := by
  set active := (getActiveValidatorIndices state (computeEpochAtSlot preset slot)).length
  set perSlot := (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat
  set before := (slot % preset.SLOTS_PER_EPOCH).toNat
  set slots := preset.SLOTS_PER_EPOCH.toNat
  -- The bound of a place among the committees of the epoch, in the shuffled active validators.
  set bound := fun place => active * (before * perSlot + place) / (perSlot * slots) with boundEq
  have mono : Monotone bound := fun _ _ le =>
    Nat.div_le_div_right (Nat.mul_le_mul_left _ (Nat.add_le_add_left le _))
  -- Each committee holds the gap between its bound and the next one.
  have lengthEq := mapM_ok_length committeesOk
  have sizes : committees.map Array.size =
      (List.range perSlot).map fun place => bound (place + 1) - bound place := by
    apply List.ext_getElem (by simp [lengthEq])
    intro place lt _
    have read := mapM_ok_getElem committeesOk place (by simpa [lengthEq] using lt)
    simp only [List.getElem_range] at read
    have small : place < 2 ^ 64 := by
      have := (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat_lt
      simp [lengthEq] at lt
      omega
    have placeEq : place.toUInt64.toNat = place := by
      simpa using small
    simp only [List.getElem_map, List.getElem_range, size_of_getBeaconCommittee read, boundEq,
      placeEq]
    rfl
  -- The steps telescope, from the first committee of the slot to the first of the next slot.
  have telescoped : ((List.range perSlot).map fun place => bound (place + 1) - bound place).sum =
      bound perSlot - bound 0 := by
    rw [← Finset.sum_range_tsub mono]
    rfl
  rw [sizes, telescoped]
  rcases Nat.eq_zero_or_pos perSlot with zero | positive
  · simp [boundEq, zero]
  -- The committee count of a slot cancels from the bounds.
  have top : bound perSlot = active * (before + 1) / slots := by
    change active * (before * perSlot + perSlot) / (perSlot * slots) = _
    rw [← Nat.succ_mul, ← Nat.mul_assoc, Nat.mul_comm perSlot slots,
      Nat.mul_div_mul_right _ _ positive]
  have bottom : bound 0 = active * before / slots := by
    change active * (before * perSlot + 0) / (perSlot * slots) = _
    rw [Nat.add_zero, ← Nat.mul_assoc, Nat.mul_comm perSlot slots,
      Nat.mul_div_mul_right _ _ positive]
  -- The share of one more slot exceeds the share of one slot by at most one rounding.
  rw [top, bottom, Nat.mul_succ, Nat.sub_le_iff_le_add', ← Nat.add_assoc]
  exact Nat.add_div_le_div_add_div_add_one (active * before) active slots

/-- Honest validators outside the committees of one slot keep two thirds at a later state.

A run from a genesis state `g` reaches `x`, and a branch continues it to `w`, before Gloas.

The preset meets the parameters of the a priori drift, and its guard holds at `x` and `high`.

The epoch of `w` is at most `high + 1`.

Each honest validator is active at `x`, and active and unslashed at `w`.

Every validator active and slashed at `w` was slashed at `x`.

The epoch of the slot is at most the largest seed lookahead after the current epoch of `x`.

So the run keeps its active validators.

The committees of the slot are read at `w`.

Take any set of validators active at `x` in the epoch of the slot.

The set may hold at most their count over the slots of an epoch, plus one.

At `x`, three times the honest stake outside it covers twice the active stake and the margin.

Then at `w`, without the members of those committees, three times the honest stake is enough. -/
theorem quorum_without_slot_of_stakeMargin {g x w : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x w)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : DirectSafety.Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (early : w.fork < .glamsterdam) {high : ℕ}
    (window : (getCurrentEpoch w.state).toNat ≤ high + 1)
    (guard : aprioriGuardAt config x high) {honest : Finset ValidatorIndex}
    (active : ∀ i ∈ honest, i ∈ getActiveValidatorIndices w.state (getCurrentEpoch w.state))
    (unslashed : ∀ i ∈ honest, (w.state.validators.data[i.toNat]?).map (·.slashed) = some false)
    (activeBefore : ∀ i ∈ honest, i ∈ getActiveValidatorIndices x.state (getCurrentEpoch x.state))
    (noSlashing : ∀ i ∈ getActiveValidatorIndices w.state (getCurrentEpoch w.state),
      (w.state.validators.data[i.toNat]?).map (·.slashed) = some true →
        (x.state.validators.data[i.toNat]?).map (·.slashed) = some true)
    {slot : Slot} (fixed : computeEpochAtSlot preset slot ≤ activityFixedEpoch x.state)
    {committees : List (Array ValidatorIndex)}
    (committeesOk : (List.range
        (getCommitteeCountPerSlot w.state (computeEpochAtSlot preset slot)).toNat).mapM
      (fun position => getBeaconCommittee w.state slot position.toUInt64) = .ok committees)
    (margin : ∀ excluded ⊆
        (getActiveValidatorIndices x.state (computeEpochAtSlot preset slot)).toFinset,
      excluded.card ≤ (getActiveValidatorIndices x.state (computeEpochAtSlot preset slot)).length /
        preset.SLOTS_PER_EPOCH.toNat + 1 →
      2 * stake (fun i => balanceAt x.state i.toNat)
          (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset +
        stakeMargin config x high ≤
      3 * stake (fun i => balanceAt x.state i.toNat) (honest \ excluded)) :
    2 * stake (fun i => balanceAt w.state i.toNat)
        (getActiveValidatorIndices w.state (getCurrentEpoch w.state)).toFinset ≤
      3 * stake (fun i => balanceAt w.state i.toNat)
        (honest \ (committees.flatMap Array.toList).toFinset) := by
  -- The run fixes the activity of the epoch of the slot, so its active validators are those of `x`.
  have same := (activeKept_of_chainSteps tail.chainSteps).getActiveValidatorIndices_eq fixed
  -- Each member of the committees is active in the epoch of the slot.
  have inside : (committees.flatMap Array.toList).toFinset ⊆
      (getActiveValidatorIndices x.state (computeEpochAtSlot preset slot)).toFinset := by
    intro member listed
    obtain ⟨committee, found, mem⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp listed)
    obtain ⟨position, -, -, read⟩ :=
      exists_mem_of_forall₂ (forall₂_mem_of_mapM_ok committeesOk).flip found
    rw [List.mem_toFinset, ← same]
    exact mem_getActiveValidatorIndices_of_getBeaconCommittee read (Array.mem_toList_iff.mp mem)
  -- They are at most the share of one slot.
  have counted : (committees.flatMap Array.toList).toFinset.card ≤
      (getActiveValidatorIndices x.state (computeEpochAtSlot preset slot)).length /
        preset.SLOTS_PER_EPOCH.toNat + 1 := by
    rw [← same]
    refine (List.toFinset_card_le _).trans ?_
    rw [List.length_flatMap]
    simpa using sum_size_le_of_mapM_getBeaconCommittee committeesOk
  exact quorum_of_stakeMargin shared tail genesis parameters caps aligned twoSlots early window
    guard (fun i member => active i (Finset.mem_sdiff.mp member).1)
    (fun i member => unslashed i (Finset.mem_sdiff.mp member).1)
    (fun i member => activeBefore i (Finset.mem_sdiff.mp member).1) noSlashing
    (margin _ inside counted)

end EthLib.Consensus
