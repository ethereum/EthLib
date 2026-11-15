module

import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Basic
import EthLib.Consensus.Proofs.Transition.FfgStake

/-!
# Checked reads for historical-anchor transport

A receiver can read the weight of an older committee window in its own balance state.

The caller's successful read supplies the arithmetic at the first slot.

The receiver's longer committee window supplies the shorter window and its final-slot arithmetic.

Successful registry lookups and an active total then supply the checked balance read.
-/

namespace EthLib.Consensus

open Base Uint64 Models

variable {preset : Preset} {fork : Fork}

/-- A successful total also bounds a subset, without bounding inactive balances. -/
private theorem totalBalance_exists_of_subset {state : BeaconState preset fork}
    {indices all : List ValidatorIndex} {total : Gwei}
    (read : getTotalBalance state all = .ok total)
    (subset : ∀ v ∈ indices, v ∈ all) :
    ∃ result, getTotalBalance state indices = .ok result := by
  obtain ⟨inside, bounded, -⟩ := getTotalBalance_ok_iff_stake.mp read
  have small : stake (fun v => balanceAt state v.toNat) indices.toFinset < 2 ^ 64 :=
    lt_of_le_of_lt (stake_mono fun v member =>
      List.mem_toFinset.mpr (subset v (List.mem_toFinset.mp member))) bounded
  let value := max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    (stake (fun v => balanceAt state v.toNat) indices.toFinset)
  have fits : value < 2 ^ 64 := max_lt preset.EFFECTIVE_BALANCE_INCREMENT.toNat_lt small
  refine ⟨value.toUInt64, getTotalBalance_ok_iff_stake.mpr
    ⟨fun v member => inside v (subset v member), small, ?_⟩⟩
  exact UInt64.toNat_ofNat_of_lt' fits

/-- Registry lookups and a checked active total supply a checked filtered total. -/
private theorem filteredTotal_exists {state : BeaconState preset fork}
    {participants : Std.TreeSet ValidatorIndex} {total : Gwei}
    (read : getTotalActiveBalance state = .ok total)
    (inside : ∀ v ∈ participants, ∃ validator, validatorAt state v = .ok validator) :
    ∃ active result,
      participants.toList.filterM (fun index => do
        return isActiveValidator (← validatorAt state index) (getCurrentEpoch state)) =
        .ok active ∧ getTotalBalance state active = .ok result := by
  obtain ⟨active, filtered⟩ := filterM_exists_ok (test := fun index => do
    return isActiveValidator (← validatorAt state index) (getCurrentEpoch state))
    (list := participants.toList) (fun v member => by
      obtain ⟨validator, found⟩ := inside v (Std.TreeSet.mem_toList.mp member)
      exact ⟨isActiveValidator validator (getCurrentEpoch state), by simp [found]⟩)
  obtain ⟨result, resultOk⟩ := totalBalance_exists_of_subset
    (indices := active) (getTotalActiveBalance_ok read) (fun v member => by
      have passed := passes_of_mem_filterM_ok filtered member
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at passed
      obtain ⟨validator, found, isActive⟩ := passed
      exact mem_getActiveValidatorIndices_of_isActiveAt
        (isActiveAt_eq_true_iff.mpr ⟨validator, validatorAt_ok_iff.mp found, isActive⟩))
  exact ⟨active, result, filtered, resultOk⟩

/-- The maximum succeeds when its arithmetic, committee, registry and total reads succeed. -/
private theorem maximum_exists_of_total {store : Store preset fork} {head : Root}
    {state : BeaconState preset fork} {first last : Slot}
    {participants : Std.TreeSet ValidatorIndex} {total : Gwei} {covered : Bool}
    (coverage : isFullValidatorSetCovered preset first last = .ok covered)
    (windowOk : store.getCommitteesBetweenSlots head first last = .ok participants)
    (totalOk : getTotalActiveBalance state = .ok total)
    (inside : ∀ v ∈ participants, ∃ validator, validatorAt state v = .ok validator) :
    ∃ maximum, store.computeCommitteeWeightBetweenSlots head state first last = .ok maximum := by
  by_cases empty : last < first
  · exact ⟨0, Store.computeCommitteeWeightBetweenSlots_of_gt empty⟩
  cases covered
  · obtain ⟨active, result, filtered, resultOk⟩ := filteredTotal_exists totalOk inside
    simp only [bind, Except.bind, pure, Except.pure] at filtered
    exact ⟨result, by
      simp only [Store.computeCommitteeWeightBetweenSlots, Store.computeCommitteeWeightAndMembers,
        empty, ↓reduceIte, coverage, bind, Except.bind, Bool.false_eq_true, windowOk,
        filtered, resultOk, Except.mapError, pure, Except.pure]⟩
  · exact ⟨total, by
      rw [Store.computeCommitteeWeightBetweenSlots_of_covered coverage]
      rw [totalOk]; rfl⟩

/-- A successful committee window supplies every shorter window with the same first slot. -/
private theorem committeeWindow_prefix {store : Store preset fork} {head : Root}
    {first last shortLast : Slot} {members : Std.TreeSet ValidatorIndex}
    (read : store.getCommitteesBetweenSlots head first last = .ok members)
    (before : shortLast ≤ last) :
    ∃ short, store.getCommitteesBetweenSlots head first shortLast = .ok short ∧
      ∀ v ∈ short, v ∈ members := by
  have original := read
  unfold Store.getCommitteesBetweenSlots at read
  obtain ⟨afterLast, afterOk, folded⟩ := bind_ok_iff.mp read
  have afterNat := addChecked_ok_iff.mp (mapError_ok_iff.mp afterOk)
  have shorter : shortLast.toNat + (1 : UInt64).toNat < 2 ^ 64 := by
    have le := UInt64.le_iff_toNat_le.mp before
    omega
  have shortOk := addChecked_of_lt shorter
  have shortNat := (addChecked_ok_iff.mp shortOk).2
  have counts : (shortLast + 1).toNat - first.toNat ≤ afterLast.toNat - first.toNat := by
    have le := UInt64.le_iff_toNat_le.mp before
    omega
  have split : List.range (afterLast.toNat - first.toNat) =
      List.range ((shortLast + 1).toNat - first.toNat) ++
        (List.range (afterLast.toNat - first.toNat)).drop
          ((shortLast + 1).toNat - first.toNat) := by
    simpa only [List.take_range, Nat.min_eq_left counts] using
      (List.take_append_drop ((shortLast + 1).toNat - first.toNat)
        (List.range (afterLast.toNat - first.toNat))).symm
  rw [split, List.foldlM_append] at folded
  obtain ⟨short, prefixOk, _⟩ := bind_ok_iff.mp folded
  have shortRead : store.getCommitteesBetweenSlots head first shortLast = .ok short := by
    simpa only [Store.getCommitteesBetweenSlots, shortOk, Except.mapError,
      bind, Except.bind] using prefixOk
  exact ⟨short, shortRead, fun _ member =>
    Store.mem_getCommitteesBetweenSlots_of_le shortRead original before member⟩

/-- A nonempty maximum supplies first-slot arithmetic for another range with the same start. -/
private theorem coverage_exists_of_maximum {store : Store preset fork} {head : Root}
    {state : BeaconState preset fork} {first last otherLast afterOther : Slot} {maximum : Gwei}
    (nonempty : first ≤ last)
    (read : store.computeCommitteeWeightBetweenSlots head state first last = .ok maximum)
    (afterOk : addChecked otherLast 1 = .ok afterOther) :
    ∃ covered, isFullValidatorSetCovered preset first otherLast = .ok covered := by
  have notEmpty : ¬last < first := UInt64.not_lt.mpr nonempty
  simp only [Store.computeCommitteeWeightBetweenSlots, bind_ok_iff] at read
  obtain ⟨result, read, -⟩ := read
  simp only [Store.computeCommitteeWeightAndMembers, notEmpty, ↓reduceIte,
    bind_ok_iff] at read
  obtain ⟨covered, coverage, -⟩ := read
  simp only [isFullValidatorSetCovered, bind_ok_iff, mapError_ok_iff] at coverage
  obtain ⟨afterFirst, firstOk, lastFirst, lastFirstOk, _, _, -⟩ := coverage
  refine ⟨decide (computeEpochAtSlot preset lastFirst < computeEpochAtSlot preset afterOther), ?_⟩
  simp only [isFullValidatorSetCovered, firstOk, lastFirstOk, afterOk, Except.mapError,
    bind, Except.bind, pure, Except.pure]

/-- The receiver reads the old maximum from its own balance state.

The caller supplies range arithmetic, not balances or registry containment. -/
private theorem receiver_oldMaximum {caller receiver : Store preset fork}
    {head receiverHead : Root} {source state : BeaconState preset fork}
    {first oldLast last : Slot} {maximum total : Gwei}
    {window : Std.TreeSet ValidatorIndex}
    (read : caller.computeCommitteeWeightBetweenSlots head source first oldLast = .ok maximum)
    (windowOk : receiver.getCommitteesBetweenSlots receiverHead first last = .ok window)
    (before : oldLast ≤ last) (totalOk : getTotalActiveBalance state = .ok total)
    (inside : ∀ v ∈ window, ∃ validator, validatorAt state v = .ok validator) :
    ∃ result, receiver.computeCommitteeWeightBetweenSlots receiverHead state first oldLast =
      .ok result := by
  by_cases empty : oldLast < first
  · exact ⟨0, Store.computeCommitteeWeightBetweenSlots_of_gt empty⟩
  obtain ⟨members, membersOk, subset⟩ := committeeWindow_prefix windowOk before
  have afterRead := membersOk
  unfold Store.getCommitteesBetweenSlots at afterRead
  obtain ⟨afterOld, afterOk, _⟩ := bind_ok_iff.mp afterRead
  obtain ⟨covered, coverage⟩ := coverage_exists_of_maximum (UInt64.not_lt.mp empty) read
    (mapError_ok_iff.mp afterOk)
  exact maximum_exists_of_total coverage membersOk totalOk
    (fun v member => inside v (subset v member))

end EthLib.Consensus
