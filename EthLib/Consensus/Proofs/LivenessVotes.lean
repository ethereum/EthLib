module

public import EthLib.Consensus.Proofs.DirectSafety.Attestations
public import EthLib.Consensus.Proofs.LivenessContinuation
public import EthLib.Consensus.Proofs.Transition.EpochJustification
public import EthLib.Consensus.Proofs.Transition.FfgFreshVotes
import EthLib.Consensus.Proofs.ForkChoice.RealizedJustification
import EthLib.Consensus.Proofs.Transition.SlashedFlags

/-!
# Proofs: the votes of an honest continuation count for the target and add no slashable pair

The committees of an epoch hold each of its active validators once.

So an active honest validator sits in a committee of some slot of the epoch.

If that slot is not the last one, an honest continuation through the epoch gave it the flag.

So the justification test of the epoch counts every honest validator outside the last slot.

An honest validator also votes once in each epoch, in its one committee.

Its vote reads the target, the source and the head that the epoch fixes.

So two of its votes for one target epoch in an honest run are the same data.

Its source never goes back from one epoch to the next.

So with a fresh source, its new votes add no slashable pair to its old ones.

An honest block, as modelled, carries no slashing, so an honest run slashes no one.

These are steps toward Theorem 2 of Casper FFG.

The paper is [arXiv 1710.09437v4](https://arxiv.org/abs/1710.09437v4).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-! ## The order of the steps of a run -/

/-- One step of a chain keeps the invariant and does not lower the current justified epoch. -/
private theorem ChainStep.justified_le {a b : ForkedBeaconState preset}
    (holds : Invariant a.state) (step : ChainStep config checks a b) :
    Invariant b.state ∧
      a.state.currentJustifiedCheckpoint.epoch ≤ b.state.currentJustifiedCheckpoint.epoch := by
  cases step with
  | slot computed =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
    refine ⟨(advanceSlotAcross_invariant holds computed).1, ?_⟩
    have first := advanceSlots_currentJustified_mono (count := 1) holds
      (by simp only [advanceSlots, bind_ok_iff]; exact ⟨advanced, advancedOk, rfl⟩)
    -- The upgrades keep the current justified checkpoint.
    have kept := processUpgrades_induction (property := fun z =>
        z.state.currentJustifiedCheckpoint = advanced.currentJustifiedCheckpoint)
      (fun held ok => (upgradeFrame_upgradeNext ok).currentJustified.trans held) rfl upgraded
    rw [kept]
    exact first
  | block engine signed _ applied =>
    have frame := frame_processBlock (applySignedBlock_ok applied).2.1
    exact ⟨frame.invariant holds, frame.currentJustified ▸ UInt64.le_refl _⟩

/-- Steps of a chain keep the invariant and do not lower the current justified epoch. -/
private theorem justified_le_of_chainSteps {a b : ForkedBeaconState preset}
    (holds : Invariant a.state) (steps : Relation.ReflTransGen (ChainStep config checks) a b) :
    Invariant b.state ∧
      a.state.currentJustifiedCheckpoint.epoch ≤ b.state.currentJustifiedCheckpoint.epoch := by
  induction steps with
  | refl => exact ⟨holds, UInt64.le_refl _⟩
  | tail _ step ih =>
    obtain ⟨middle, low⟩ := ih
    obtain ⟨last, high⟩ := step.justified_le middle
    exact ⟨last, UInt64.le_trans low high⟩

/-- The first state of a step of a run follows the first state of the run by steps of a chain. -/
private theorem Run.reach_of_contains {x y u v : ForkedBeaconState preset}
    {run : Run config checks x y} {step : Step config checks u v} (member : run.Contains step) :
    Relation.ReflTransGen (ChainStep config checks) x u := by
  obtain ⟨pre, -, -⟩ := run.contains_split step member
  exact pre.chainSteps

/-- Two steps of a run come in order.

Either the first state of the one leads to the first state of the other by steps of a chain.

Or the last state of the other leads to the first state of the one. -/
private theorem Run.steps_ordered {x y u₁ v₁ u₂ v₂ : ForkedBeaconState preset}
    {run : Run config checks x y} {one : Step config checks u₁ v₁}
    {two : Step config checks u₂ v₂} (first : run.Contains one) (second : run.Contains two) :
    Relation.ReflTransGen (ChainStep config checks) u₁ u₂ ∨
      Relation.ReflTransGen (ChainStep config checks) v₂ u₁ := by
  obtain ⟨pre, post, rfl⟩ := run.contains_split two second
  rcases (Run.contains_append _ post one).mp first with inPre | inPost
  · cases inPre with
    | last => exact .inl .refl
    | earlier inner =>
      obtain ⟨pre', middle, rfl⟩ := pre.contains_split one inner
      exact .inl ((Run.nil.snoc one).append middle).chainSteps
  · obtain ⟨pre', -, -⟩ := post.contains_split one inPost
    exact .inr pre'.chainSteps

/-- A vote of an honest run is an honest vote on the state before the block that carries it. -/
private theorem Run.Honest.honestVote {x y : ForkedBeaconState preset}
    {honest : Finset ValidatorIndex} {key : ValidatorIndex → Signatures.SecretKey}
    {run : Run config checks x y} (honestRun : run.Honest config honest key)
    {vote : ValidatorIndex × AttestationData} (member : vote ∈ run.votes) :
    ∃ (fork : Fork) (before : BeaconState preset fork) (after : ForkedBeaconState preset)
      (step : Step config checks ⟨fork, before⟩ after), run.Contains step ∧
        HonestVote honest before vote := by
  obtain ⟨before, after, step, contained, voted⟩ := member
  have honestStep := honestRun step contained
  cases step with
  | slot _ => exact absurd voted (Set.notMem_empty _)
  | block engine signed due ok =>
    exact ⟨_, _, _, _, contained, honestStep.2.2 vote voted⟩

/-! ## The target test of an epoch -/

/-- Two slots of one epoch that are both the last of it are equal. -/
private theorem eq_of_last_of_same_epoch {s v p : Nat} (same : s / p = v / p)
    (sLast : (s + 1) % p = 0) (vLast : (v + 1) % p = 0) : s = v := by
  have sSplit := Nat.div_add_mod (s + 1) p
  have vSplit := Nat.div_add_mod (v + 1) p
  rw [sLast, Nat.succ_div_of_dvd (Nat.dvd_of_mod_eq_zero sLast)] at sSplit
  rw [vLast, Nat.succ_div_of_dvd (Nat.dvd_of_mod_eq_zero vLast), ← same] at vSplit
  omega

/-- From Altair, an active validator with the timely target flag of the current epoch is counted.

The validator is not slashed, and the read of the participants of the epoch succeeds. -/
private theorem mem_currentTarget {fork : Fork} {state : BeaconState preset fork}
    (altair : .altair ≤ fork) {indices : List ValidatorIndex}
    (computed : getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
      (getCurrentEpoch state) = .ok indices)
    {index : ValidatorIndex}
    (active : index ∈ getActiveValidatorIndices state (getCurrentEpoch state))
    (unslashed : (state.validators.data[index.toNat]?).map (·.slashed) = some false)
    (flagged : TargetFlagAt (state.currentEpochParticipation altair) index.toNat) :
    index ∈ indices := by
  obtain ⟨validator, found, clean⟩ := Option.map_eq_some_iff.mp unslashed
  obtain ⟨flags, read, set⟩ := flagged
  unfold getUnslashedParticipatingIndices at computed
  dsimp only at computed
  rw [ite_eq_left (Or.inr rfl)] at computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨activeIndices, checked, entries, entriesOk, rfl⟩ := computed
  have member : index ∈ activeIndices :=
    (getActiveValidatorIndicesChecked_ok checked).symm ▸ active
  obtain ⟨entry, listed, step⟩ := exists_mem_of_mapM_ok entriesOk member
  simp only [ite_true, read, getValidator_eq_ok_iff.mpr found, bind, Except.bind,
    Except.ok.injEq] at step
  subst step
  simp only [List.mem_map, List.mem_filter]
  exact ⟨_, ⟨listed, by simp [set, clean]⟩, rfl⟩

/-- From Altair, the target test of an epoch counts every honest validator outside its last slot.

The state is at the last slot of its epoch, and the votes of its other slots are gathered.

Each honest validator is active in the epoch and not slashed.

The active validators times the committees fit in 64 bits.

The committees of the last slot are read at the state. -/
theorem targetIndices_of_votesGathered {fork : Fork} {state : BeaconState preset fork}
    (altair : .altair ≤ fork)
    (last : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0)
    (shuffleRoom : (getActiveValidatorIndices state (getCurrentEpoch state)).length *
      ((getCommitteeCountPerSlot state (getCurrentEpoch state)).toNat *
        preset.SLOTS_PER_EPOCH.toNat) < 2 ^ 64)
    {honest : Finset ValidatorIndex} (gathered : VotesGathered honest state)
    (active : ∀ i ∈ honest, i ∈ getActiveValidatorIndices state (getCurrentEpoch state))
    (unslashed : ∀ i ∈ honest,
      (state.validators.data[i.toNat]?).map (·.slashed) = some false)
    {committees : List (Array ValidatorIndex)}
    (committeesOk : (List.range
        (getCommitteeCountPerSlot state (getCurrentEpoch state)).toNat).mapM
      (fun position => getBeaconCommittee state state.slot position.toUInt64) = .ok committees) :
    ∀ indices, targetIndices state (getCurrentEpoch state) = .ok indices →
      honest \ (committees.flatMap Array.toList).toFinset ⊆ indices.toFinset := by
  -- The last slot ends an epoch, so an epoch has a slot.
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by
    rcases Nat.eq_zero_or_pos preset.SLOTS_PER_EPOCH.toNat with zero | positive
    · rw [zero, Nat.mod_zero] at last
      omega
    · exact positive
  intro indices computed index member
  obtain ⟨isHonest, outside⟩ := Finset.mem_sdiff.mp member
  have participating : getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
      (getCurrentEpoch state) = .ok indices := by
    unfold targetIndices at computed
    rw [dite_eq_left altair] at computed
    exact liftAccessor_ok.mp computed
  have epochActive := active index isHonest
  -- The checked read of the active indices succeeds, since the read of the flags does.
  have indicesFit : getActiveValidatorIndicesChecked state (getCurrentEpoch state) =
      .ok (getActiveValidatorIndices state (getCurrentEpoch state)) := by
    have read := participating
    unfold getUnslashedParticipatingIndices at read
    dsimp only at read
    rw [ite_eq_left (Or.inr rfl)] at read
    simp only [bind_ok_iff] at read
    obtain ⟨activeIndices, checked, -⟩ := read
    rw [← getActiveValidatorIndicesChecked_ok checked]
    exact checked
  -- The first committee of the last slot has a value, so the seed and the shuffle have one.
  obtain ⟨length, each⟩ := mapM_eq_ok_iff.mp committeesOk
  have countPos : 0 < (getCommitteeCountPerSlot state (getCurrentEpoch state)).toNat :=
    UInt64.le_iff_toNat_le.mp (one_le_getCommitteeCountPerSlot state _)
  have firstOk := each 0 (by simpa using countPos)
  simp only [List.getElem_range] at firstOk
  obtain ⟨seed, _, _, seedOk, _, _, firstCommittee⟩ := getBeaconCommittee_ok firstOk
  have sizeFits :
      (getActiveValidatorIndices state (getCurrentEpoch state)).toArray.size < 2 ^ 64 := by
    rw [List.size_toArray]
    exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.mul_pos countPos positive))
      shuffleRoom
  have small := le_of_computeCommittee sizeFits firstCommittee
  rw [List.size_toArray] at small
  -- The epoch ends at the slot of the state, so its slots fit in 64 bits.
  have slotsFit : ((getCurrentEpoch state).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat ≤ 2 ^ 64 := by
    have split := Nat.div_add_mod (state.slot.toNat + 1) preset.SLOTS_PER_EPOCH.toNat
    rw [last, Nat.succ_div_of_dvd (Nat.dvd_of_mod_eq_zero last)] at split
    have bound := state.slot.toNat_lt
    rw [getCurrentEpoch_toNat, Nat.mul_comm]
    omega
  obtain ⟨slot, position, committee, slotEpoch, positionLt, committeeOk, inCommittee⟩ :=
    exists_mem_getBeaconCommittee indicesFit seedOk
      (fun zero => by rw [zero] at positive; exact absurd positive (by decide)) slotsFit small
      shuffleRoom epochActive
  refine List.mem_toFinset.mpr (mem_currentTarget altair participating epochActive
    (unslashed index isHonest) ?_)
  by_cases lastSlot : (slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0
  · -- A committee of the last slot is one of the committees read at the state.
    have sameNat := congrArg UInt64.toNat slotEpoch
    rw [getCurrentEpoch_toNat] at sameNat
    simp only [computeEpochAtSlot, UInt64.toNat_div] at sameNat
    have atSlot : slot = state.slot :=
      UInt64.toNat_inj.mp (eq_of_last_of_same_epoch sameNat lastSlot last)
    subst atSlot
    have positionNat := UInt64.lt_iff_toNat_lt.mp positionLt
    have read := each position.toNat (by simpa using positionNat)
    have back : position.toNat.toUInt64 = position := by simp
    simp only [List.getElem_range] at read
    rw [back, committeeOk, Except.ok.injEq] at read
    subst read
    exact absurd (List.mem_toFinset.mpr (List.mem_flatMap.mpr
      ⟨_, List.getElem_mem _, Array.mem_toList_iff.mpr inCommittee⟩)) outside
  · exact gathered altair slot slotEpoch lastSlot position committee positionLt committeeOk
      index inCommittee isHonest

/-! ## One vote for each validator and epoch -/

/-- No validator is in two committees of one epoch, when a committee of the epoch has a value.

The two committees have slots of one epoch and indices below the committees of a slot.

The active validators times the committees of the epoch fit in 64 bits.

A committee with a value comes from the checked read of the active indices.

So each active position fits in 64 bits, and no index is active twice. -/
private theorem eq_of_mem_committees {fork : Fork} {state : BeaconState preset fork}
    {firstSlot secondSlot : Slot} {firstIndex secondIndex : CommitteeIndex}
    (sameEpoch : computeEpochAtSlot preset firstSlot = computeEpochAtSlot preset secondSlot)
    (firstLt : firstIndex < getCommitteeCountPerSlot state (computeEpochAtSlot preset firstSlot))
    (secondLt :
      secondIndex < getCommitteeCountPerSlot state (computeEpochAtSlot preset secondSlot))
    (fits : (getActiveValidatorIndices state (computeEpochAtSlot preset firstSlot)).length *
      ((getCommitteeCountPerSlot state (computeEpochAtSlot preset firstSlot)).toNat *
        preset.SLOTS_PER_EPOCH.toNat) < 2 ^ 64)
    {firstCommittee secondCommittee : Array ValidatorIndex}
    (first : getBeaconCommittee state firstSlot firstIndex = .ok firstCommittee)
    (second : getBeaconCommittee state secondSlot secondIndex = .ok secondCommittee)
    {member : ValidatorIndex} (firstMem : member ∈ firstCommittee)
    (secondMem : member ∈ secondCommittee) :
    firstSlot = secondSlot ∧ firstIndex = secondIndex := by
  -- The shuffle of the epoch read the active indices with the check.
  have nodup : (getActiveValidatorIndices state
      (computeEpochAtSlot preset firstSlot)).toArray.toList.Nodup := by
    obtain ⟨active, shuffled, shuffleOk⟩ := attesterShuffle_ok_of_getBeaconCommittee first
    simp only [attesterShuffle, bind_ok_iff] at shuffleOk
    obtain ⟨_, -, indices, checked, -⟩ := shuffleOk
    have sorted := sorted_of_getActiveValidatorIndicesChecked_ok checked
    rw [getActiveValidatorIndicesChecked_ok checked] at sorted
    simpa [List.Nodup] using sorted.imp UInt64.ne_of_lt
  obtain ⟨firstSeed, firstPosition, firstCount, firstSeedOk, firstPositionEq, firstCountEq,
    firstOk⟩ := getBeaconCommittee_ok first
  obtain ⟨secondSeed, secondPosition, secondCount, secondSeedOk, secondPositionEq,
    secondCountEq, secondOk⟩ := getBeaconCommittee_ok second
  rw [← sameEpoch] at secondSeedOk secondPositionEq secondCountEq secondOk secondLt
  rw [firstSeedOk, Except.ok.injEq] at secondSeedOk
  subst secondSeedOk
  have sameCount : firstCount = secondCount :=
    UInt64.toNat_inj.mp (firstCountEq.trans secondCountEq.symm)
  subst sameCount
  -- The names of the epoch's numbers, on natural numbers.
  generalize perSlotEq : (getCommitteeCountPerSlot state
    (computeEpochAtSlot preset firstSlot)).toNat = perSlot at *
  generalize epochLength : preset.SLOTS_PER_EPOCH.toNat = length at *
  have firstIndexLt : firstIndex.toNat < perSlot := perSlotEq ▸ UInt64.lt_iff_toNat_lt.mp firstLt
  have secondIndexLt : secondIndex.toNat < perSlot :=
    perSlotEq ▸ UInt64.lt_iff_toNat_lt.mp secondLt
  have lengthPos : 0 < length := by
    have nonzero := count_ne_zero_of_computeCommittee firstOk
    refine Nat.pos_of_ne_zero fun zero => nonzero (UInt64.toNat_inj.mp ?_)
    rw [firstCountEq, zero, Nat.mul_zero]
    rfl
  have firstModLt : (firstSlot % preset.SLOTS_PER_EPOCH).toNat < length := by
    rw [UInt64.toNat_mod, epochLength]
    exact Nat.mod_lt _ lengthPos
  have secondModLt : (secondSlot % preset.SLOTS_PER_EPOCH).toNat < length := by
    rw [UInt64.toNat_mod, epochLength]
    exact Nat.mod_lt _ lengthPos
  -- A position below the count: the earlier slots, then the index, stay below the epoch.
  have positionLt : ∀ slotPart indexPart, slotPart < length → indexPart < perSlot →
      slotPart * perSlot + indexPart < perSlot * length := by
    intro slotPart indexPart slotLt indexLt
    calc slotPart * perSlot + indexPart < slotPart * perSlot + perSlot := by omega
      _ = (slotPart + 1) * perSlot := (Nat.succ_mul _ _).symm
      _ ≤ length * perSlot := Nat.mul_le_mul_right _ slotLt
      _ = perSlot * length := Nat.mul_comm _ _
  have samePosition := eq_of_mem_computeCommittee (count := firstCount) nodup
    (by simpa [firstCountEq] using fits)
    (first := firstPosition.toNat) (second := secondPosition.toNat)
    (by rw [firstPositionEq, firstCountEq]; exact positionLt _ _ firstModLt firstIndexLt)
    (by rw [secondPositionEq, firstCountEq]; exact positionLt _ _ secondModLt secondIndexLt)
    (by simpa using firstOk) (by simpa using secondOk) firstMem secondMem
  rw [firstPositionEq, secondPositionEq] at samePosition
  -- The slot part and the index part of one position are equal.
  have perSlotPos : 0 < perSlot := Nat.zero_lt_of_lt firstIndexLt
  have split : ∀ a b c d, b < perSlot → d < perSlot → a * perSlot + b = c * perSlot + d →
      a = c ∧ b = d := by
    intro a b c d bLt dLt equal
    have divided := congrArg (· / perSlot) equal
    have reduced := congrArg (· % perSlot) equal
    simp only [Nat.mul_comm _ perSlot, Nat.mul_add_div perSlotPos, Nat.div_eq_of_lt bLt,
      Nat.div_eq_of_lt dLt, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt bLt,
      Nat.mod_eq_of_lt dLt] at divided reduced
    exact ⟨divided, reduced⟩
  obtain ⟨sameMod, sameIndex⟩ := split _ _ _ _ firstIndexLt secondIndexLt samePosition
  refine ⟨?_, UInt64.toNat_inj.mp sameIndex⟩
  -- A slot is its epoch times the length of an epoch, plus its place in the epoch.
  have epochNat := congrArg UInt64.toNat sameEpoch
  simp only [computeEpochAtSlot, UInt64.toNat_div, epochLength] at epochNat
  rw [UInt64.toNat_mod, UInt64.toNat_mod, epochLength] at sameMod
  apply UInt64.toNat_inj.mp
  rw [← Nat.div_add_mod firstSlot.toNat length, ← Nat.div_add_mod secondSlot.toNat length,
    epochNat, sameMod]

/-- What a walk inside one epoch keeps, from a first state to a later one.

The fork, the current justified checkpoint, the committees of the epoch and their count stay.

The slot does not go back, and the root of each slot before the first state reads the same. -/
private def InsideKept (a b : ForkedBeaconState preset) : Prop :=
  b.fork = a.fork ∧ b.state.currentJustifiedCheckpoint = a.state.currentJustifiedCheckpoint ∧
    a.state.slot ≤ b.state.slot ∧ CommitteesKept (getCurrentEpoch a.state) a.state b.state ∧
    getCommitteeCountPerSlot b.state (getCurrentEpoch a.state) =
      getCommitteeCountPerSlot a.state (getCurrentEpoch a.state) ∧
    ∀ slot root, slot < a.state.slot → getBlockRootAtSlot b.state slot = .ok root →
      getBlockRootAtSlot a.state slot = .ok root

/-- Two walks inside one epoch make one. -/
private theorem InsideKept.trans {a m b : ForkedBeaconState preset}
    (same : getCurrentEpoch m.state = getCurrentEpoch a.state) (one : InsideKept a m)
    (two : InsideKept m b) : InsideKept a b := by
  obtain ⟨fork₁, justified₁, slot₁, kept₁, count₁, roots₁⟩ := one
  obtain ⟨fork₂, justified₂, slot₂, kept₂, count₂, roots₂⟩ := two
  rw [same] at kept₂ count₂
  exact ⟨fork₂.trans fork₁, justified₂.trans justified₁, UInt64.le_trans slot₁ slot₂,
    kept₁.trans kept₂, count₂.trans count₁, fun slot root below read =>
      roots₁ slot root below (roots₂ slot root (UInt64.lt_of_lt_of_le below slot₁) read)⟩

/-- One step of a chain inside the epoch of its first state keeps what a walk inside it keeps.

A slot step there runs no epoch step and no upgrade. -/
private theorem ChainStep.insideKept
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {m b : ForkedBeaconState preset} (step : ChainStep config checks m b)
    (same : getCurrentEpoch b.state = getCurrentEpoch m.state) : InsideKept m b := by
  cases step with
  | slot computed =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
    obtain ⟨succ, -, reads, -⟩ := advanceSlotAcross_cases computed
    obtain ⟨nextSlot, cached, epoched, sum, cachedOk, epochedOk, advancedEq⟩ :=
      advanceSlot_ok advancedOk
    -- The slot reached stays in the epoch, so it is not the first of an epoch.
    have inside : (m.state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat ≠ 0 := by
      intro boundary
      have epochs := congrArg UInt64.toNat same
      rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, succ,
        Nat.succ_div_of_dvd (Nat.dvd_of_mod_eq_zero boundary)] at epochs
      omega
    have notFirst : ¬ nextSlot % preset.SLOTS_PER_EPOCH = 0 := by
      intro zero
      apply inside
      rw [← sum]
      simpa only [UInt64.toNat_mod, UInt64.toNat_zero] using congrArg UInt64.toNat zero
    rcases epochIfLast_cases epochedOk with ⟨first, -⟩ | ⟨-, kept⟩
    · exact absurd first notFirst
    have due : upgradeDue config ⟨m.fork, advanced⟩ = false := by
      apply upgradeDue_of_not_first
      rw [advancedEq]
      exact notFirst
    have reached := Except.ok.inj ((processUpgrades_of_not_due due).symm.trans upgraded)
    subst reached kept
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    obtain ⟨committees, count⟩ := committees_of_runKept apart (runKept_advanceSlot advancedOk) same
    refine ⟨rfl, by rw [advancedEq], UInt64.le_iff_toNat_le.mpr (by omega), committees, count,
      fun slot root below read => ?_⟩
    rcases reads read with ⟨-, old⟩ | ⟨atSlot, -⟩
    · exact old
    · exact absurd (atSlot ▸ below) (UInt64.lt_irrefl _)
  | block engine signed validateResult applied =>
    have processed := (applySignedBlock_ok applied).2.1
    have frame := frame_processBlock processed
    obtain ⟨committees, count⟩ := committees_of_runKept apart (runKept_processBlock processed) same
    refine ⟨rfl, frame.currentJustified, frame.slot ▸ UInt64.le_refl _, committees, count,
      fun slot root _ read => ?_⟩
    rwa [getBlockRootAtSlot_congr (processBlock_slot processed)
      (processBlock_blockRoots processed)] at read

/-- Steps of a chain that end in the epoch where they start keep what a walk inside it keeps. -/
private theorem insideKept_of_chainSteps
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {a b : ForkedBeaconState preset} (steps : Relation.ReflTransGen (ChainStep config checks) a b)
    (same : getCurrentEpoch b.state = getCurrentEpoch a.state) : InsideKept a b := by
  induction steps with
  | refl =>
    exact ⟨rfl, rfl, UInt64.le_refl _, CommitteesKept.refl _ _, rfl, fun _ _ _ read => read⟩
  | tail before step ih =>
    -- The state before the last step sits between the two, so it is in the epoch too.
    have middle := UInt64.le_antisymm (UInt64.le_trans step.currentEpoch_le (UInt64.le_of_eq same))
      (currentEpoch_le_of_chainSteps before)
    exact (ih middle).trans middle (step.insideKept apart (same.trans middle.symm))

/-- Two honest votes of one validator for one target epoch are the same data.

The second state follows the first by steps of a chain.

At the first state the active validators times the committees of the epoch fit in 64 bits. -/
private theorem vote_eq_of_chainSteps {honest : Finset ValidatorIndex}
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {fork₁ fork₂ : Fork} {s₁ : BeaconState preset fork₁} {s₂ : BeaconState preset fork₂}
    (steps : Relation.ReflTransGen (ChainStep config checks) ⟨fork₁, s₁⟩ ⟨fork₂, s₂⟩)
    (room : (getActiveValidatorIndices s₁ (getCurrentEpoch s₁)).length *
      ((getCommitteeCountPerSlot s₁ (getCurrentEpoch s₁)).toNat *
        preset.SLOTS_PER_EPOCH.toNat) < 2 ^ 64)
    {validator : ValidatorIndex} {data₁ data₂ : AttestationData}
    (vote₁ : HonestVote honest s₁ (validator, data₁))
    (vote₂ : HonestVote honest s₂ (validator, data₂))
    (same : data₁.target.epoch = data₂.target.epoch) : data₁ = data₂ := by
  have epochs : getCurrentEpoch s₂ = getCurrentEpoch s₁ :=
    vote₂.target.symm.trans (same.symm.trans vote₁.target)
  obtain ⟨forks, justified, -, kept, count, roots⟩ := insideKept_of_chainSteps apart steps epochs
  simp only at forks justified kept count roots
  subst forks
  -- The validator sits in one committee of the epoch, so the two slots and indices agree.
  obtain ⟨index₁, members₁, below₁, committee₁, in₁, named₁⟩ := vote₁.committee
  obtain ⟨index₂, members₂, below₂, committee₂, in₂, named₂⟩ := vote₂.committee
  have slot₁ := vote₁.slot
  have slot₂ : computeEpochAtSlot preset data₂.slot = getCurrentEpoch s₁ :=
    vote₂.slot.trans epochs
  rw [kept data₂.slot index₂ slot₂] at committee₂
  rw [epochs, count] at below₂
  rw [← slot₁] at below₁ room
  rw [← slot₂] at below₂
  obtain ⟨sameSlot, sameIndex⟩ := eq_of_mem_committees (slot₁.trans slot₂.symm) below₁ below₂
    room committee₁ committee₂ in₁ in₂
  -- The head and the target root are roots of slots before the first state.
  have head₁ := vote₁.head
  have head₂ := vote₂.head
  rw [← sameSlot] at head₂
  have head := head₁.symm.trans (roots _ _ (getBlockRootAtSlot_read head₁).1 head₂)
  have target₁ := vote₁.targetRoot
  have target₂ := vote₂.targetRoot
  rw [epochs] at target₂
  simp only [getBlockRoot, bind_ok_iff] at target₁ target₂
  obtain ⟨start₁, startOk₁, read₁⟩ := target₁
  obtain ⟨start₂, startOk₂, read₂⟩ := target₂
  rw [startOk₁, Except.ok.injEq] at startOk₂
  subst startOk₂
  have targetRoot := read₁.symm.trans (roots _ _ (getBlockRootAtSlot_read read₁).1 read₂)
  have source := vote₁.source.trans (justified.symm.trans vote₂.source.symm)
  have index : data₁.index = data₂.index := by rw [named₁, named₂, sameIndex]
  obtain ⟨_, _, _, _, ⟨_, _⟩⟩ := data₁
  obtain ⟨_, _, _, _, ⟨_, _⟩⟩ := data₂
  simp only [Except.ok.injEq] at head targetRoot
  simp_all

/-- Two votes of one validator for one target epoch in an honest run are the same data.

The ring of RANDAO mixes spans more than the seed lookahead plus two epochs.

Before each step of the run, the active validators times the committees fit in 64 bits. -/
theorem Run.Honest.vote_eq {x y : ForkedBeaconState preset} {honest : Finset ValidatorIndex}
    {key : ValidatorIndex → Signatures.SecretKey} {run : Run config checks x y}
    (honestRun : run.Honest config honest key)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (shuffleRoom : ∀ (before after : ForkedBeaconState preset)
      (step : Step config checks before after), run.Contains step →
      (getActiveValidatorIndices before.state (getCurrentEpoch before.state)).length *
        ((getCommitteeCountPerSlot before.state (getCurrentEpoch before.state)).toNat *
          preset.SLOTS_PER_EPOCH.toNat) < 2 ^ 64)
    {validator : ValidatorIndex} {data1 data2 : AttestationData}
    (member1 : (validator, data1) ∈ run.votes) (member2 : (validator, data2) ∈ run.votes)
    (same : data1.target.epoch = data2.target.epoch) : data1 = data2 := by
  obtain ⟨fork₁, s₁, _, one, first, vote₁⟩ := honestRun.honestVote member1
  obtain ⟨fork₂, s₂, _, two, second, vote₂⟩ := honestRun.honestVote member2
  have room₁ := shuffleRoom _ _ one first
  have room₂ := shuffleRoom _ _ two second
  rcases Run.steps_ordered first second with forward | backward
  · exact vote_eq_of_chainSteps (s₁ := s₁) (s₂ := s₂) apart forward room₁ vote₁ vote₂ same
  · -- The second vote comes first: its step leads on to the state of the first vote.
    have reach : Relation.ReflTransGen (ChainStep config checks) ⟨fork₂, s₂⟩ ⟨fork₁, s₁⟩ :=
      .head two.chainStep backward
    exact (vote_eq_of_chainSteps (s₁ := s₂) (s₂ := s₁) apart reach room₂ vote₂ vote₁
      same.symm).symm

/-- Along an honest run, a vote for a later target epoch never has an earlier source.

The run starts from a state that keeps the invariant of the state transition. -/
theorem Run.Honest.source_le {x y : ForkedBeaconState preset} {honest : Finset ValidatorIndex}
    {key : ValidatorIndex → Signatures.SecretKey} {run : Run config checks x y}
    (honestRun : run.Honest config honest key) (invariant : Invariant x.state)
    {validator1 validator2 : ValidatorIndex} {data1 data2 : AttestationData}
    (member1 : (validator1, data1) ∈ run.votes) (member2 : (validator2, data2) ∈ run.votes)
    (later : data1.target.epoch < data2.target.epoch) :
    data1.source.epoch ≤ data2.source.epoch := by
  obtain ⟨_, s₁, _, one, first, vote₁⟩ := honestRun.honestVote member1
  obtain ⟨_, s₂, _, two, second, vote₂⟩ := honestRun.honestVote member2
  rw [vote₁.source, vote₂.source]
  rw [vote₁.target, vote₂.target] at later
  rcases Run.steps_ordered first second with forward | backward
  · have holds := (justified_le_of_chainSteps invariant (Run.reach_of_contains first)).1
    exact (justified_le_of_chainSteps holds forward).2
  · -- The other step comes first, so its epoch is not later.
    have moved := UInt64.le_trans two.chainStep.currentEpoch_le
      (currentEpoch_le_of_chainSteps backward)
    exact absurd later (UInt64.not_lt.mpr moved)

/-- Each vote of an honest run has a source at least the current justified one at its start.

Its validator is honest, and its target epoch is at least the current epoch there.

The run starts from a state that keeps the invariant of the state transition. -/
theorem Run.Honest.vote_fresh {x y : ForkedBeaconState preset} {honest : Finset ValidatorIndex}
    {key : ValidatorIndex → Signatures.SecretKey} {run : Run config checks x y}
    (honestRun : run.Honest config honest key) (invariant : Invariant x.state)
    {vote : ValidatorIndex × AttestationData}
    (member : vote ∈ run.votes) :
    vote.1 ∈ honest ∧
      x.state.currentJustifiedCheckpoint.epoch ≤ vote.2.source.epoch ∧
      getCurrentEpoch x.state ≤ vote.2.target.epoch := by
  obtain ⟨_, before, _, step, contained, voted⟩ := honestRun.honestVote member
  have reach := Run.reach_of_contains contained
  refine ⟨voted.honest, ?_, ?_⟩
  · rw [voted.source]
    exact (justified_le_of_chainSteps invariant reach).2
  · rw [voted.target]
    exact currentEpoch_le_of_chainSteps reach

/-! ## Slashed flags along an honest run -/

/-- Each slashed flag of the second state was already set at its position in the first. -/
private def FlagsBack {f g : Fork} (s : BeaconState preset f) (t : BeaconState preset g) : Prop :=
  ∀ position, slashedFlagAt t position = some true → slashedFlagAt s position = some true

namespace FlagsBack

/-- A state sets no slashed flag over itself. -/
private theorem refl {f : Fork} (s : BeaconState preset f) : FlagsBack s s :=
  fun _ => id

/-- Two steps that set no slashed flag make one. -/
private theorem trans {f g h : Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    {u : BeaconState preset h} (one : FlagsBack s t) (two : FlagsBack t u) : FlagsBack s u :=
  fun position marked => one position (two position marked)

/-- A step that keeps every slashed flag sets none. -/
private theorem of_flags {f g : Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    (flags : ∀ position, slashedFlagAt t position = slashedFlagAt s position) :
    FlagsBack s t :=
  fun position marked => flags position ▸ marked

/-- A step that keeps the registry sets no slashed flag. -/
private theorem of_validators {f g : Fork} {s : BeaconState preset f} {t : BeaconState preset g}
    (same : t.validators.data = s.validators.data := by rfl) : FlagsBack s t :=
  of_flags fun position => by simp only [slashedFlagAt, same]

/-- A step that appends a validator that is not slashed sets no slashed flag. -/
private theorem of_push {fork : Fork} {s t : BeaconState preset fork} {v : Validator}
    (added : t.validators.data = s.validators.data.push v) (flag : v.slashed = false) :
    FlagsBack s t := by
  intro position marked
  simp only [slashedFlagAt, added, Array.getElem?_push] at marked ⊢
  split at marked
  · simp [flag] at marked
  · exact marked

/-- A slot sets no slashed flag. -/
private theorem of_advanceSlot {fork : Fork} {s t : BeaconState preset fork}
    (ok : advanceSlot config checks s = .ok t) : FlagsBack s t := by
  intro position marked
  have same := slashedFlagAt_advanceSlot ok position
  rw [marked] at same
  revert same
  cases slashedFlagAt s position with
  | none => simp
  | some flag => simp_all

/-- Each step of an epoch, a deposit and the other writes of a block set no slashed flag. -/
private theorem laws {fork : Fork} :
    EpochFrameLaws (preset := preset) (fork := fork) fun s t => FlagsBack s t where
  refl := refl
  trans := trans
  setValidatorAt set found _ flag _ _ := of_flags (slashedFlagAt_setValidatorAt found set flag)
  increaseBalance ok := of_validators (congrArg (·.data) (increaseBalance_validators ok))
  decreaseBalance ok := of_validators (congrArg (·.data) (decreaseBalance_validators ok))
  initiateValidatorExit ok := of_flags (slashedFlagAt_initiateValidatorExit ok)
  addValidatorToRegistry added _ := of_push (addValidatorToRegistry_validators_eq_push added) rfl
  eth1DataVotes _ _ := of_validators
  inactivityScores _ _ := of_validators
  slashings _ _ := of_validators
  randaoMixes _ _ := of_validators
  historicalRoots _ _ := of_validators
  historicalSummaries _ _ := of_validators
  participationRecords _ := of_validators
  pendingDeposits _ _ _ := of_validators
  pendingConsolidations _ _ := of_validators
  syncCommittees _ _ _ := of_validators
  proposerLookahead _ _ := of_validators
  ptcWindow _ _ := of_validators

/-- A block with no proposer slashing and no attester slashing sets no slashed flag. -/
private theorem of_processBlock {fork : Fork} {state after : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    (ok : processBlock config checks engine state block = .ok after)
    (noProposer : block.body.proposerSlashings.data = #[])
    (noAttester : block.body.attesterSlashings.data = #[]) : FlagsBack state after := by
  have keep {s t : BeaconState preset fork} (_ : BlockFrame s t)
      (same : t.validators = s.validators) : FlagsBack s t :=
    of_validators (congrArg (·.data) same)
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput ok
  -- The steps before the operations set no slashed flag.
  have first : FlagsBack state input := by
    refine started.step_of (fun s t => FlagsBack s t) refl (fun one two => one.trans two)
      (fun _ ok => processParentExecutionPayload_step_of _ refl (fun one two => one.trans two)
        keep (laws.processWithdrawalRequest keep) (laws.processConsolidationRequest keep) ok)
      (fun ok => ?_)
      (fun _ ok => processBlockExecution_step_of _ refl (fun one two => one.trans two) keep
        (fun ok => laws.processWithdrawals keep ok) ok)
      (fun ok => ?_) (fun _ ok => ?_)
    · obtain ⟨_, _, rfl⟩ := processBlockHeader_eq ok
      exact of_validators
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq ok
      exact of_validators
    · obtain ⟨_, _, rest⟩ := processEth1Data_eq ok
      exact of_validators (by rw [← rest])
  -- The block carries no slashing, and the other operations set no slashed flag.
  obtain ⟨proposed, slashed, attested, proposersOk, attestersOk, attestations, tail⟩ :=
    processOperations_folds_of (fun s t => FlagsBack s t) refl (fun one two => one.trans two)
      (laws.processDeposit keep) laws.processVoluntaryExit laws.processBlsToExecutionChange
      (laws.processExecutionRequests keep)
      (fun ok => by rw [processPayloadAttestation_eq ok]; exact of_validators) operated
  rw [noProposer] at proposersOk
  rw [noAttester] at attestersOk
  cases proposersOk
  cases attestersOk
  have attestedBack : FlagsBack input attested := laws.foldlM
    (fun _ _ _ ok => of_validators (by rw [(processAttestation_registry ok).1])) attestations
  have operatedBack := first.trans (attestedBack.trans tail)
  -- From Altair the sync aggregate follows, and it sets no slashed flag.
  split at synced
  · exact operatedBack.trans (laws.processSyncAggregate synced)
  · cases synced
    exact operatedBack

/-- A step of an honest run sets no slashed flag. -/
private theorem of_step {honest : Finset ValidatorIndex}
    {key : ValidatorIndex → Signatures.SecretKey} {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (honestStep : step.Honest config honest key) :
    FlagsBack x.state y.state := by
  cases step with
  | slot ok =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
    exact (of_advanceSlot advancedOk).trans <|
      processUpgrades_induction (property := fun z => FlagsBack advanced z.state)
        (fun held ok => held.trans (of_flags (upgradeFrame_upgradeNext ok).slashed))
        (refl _) upgraded
  | block engine signed due ok =>
    obtain ⟨-, built, -⟩ := honestStep
    exact of_processBlock (applySignedBlock_ok ok).2.1 built.proposerSlashings
      built.attesterSlashings

end FlagsBack

/-- An honest run slashes no validator.

An honest block, as modelled, carries no slashing.

A validator slashed at its end was already slashed at its start. -/
theorem Run.Honest.slashed_of_slashed {x y : ForkedBeaconState preset}
    {honest : Finset ValidatorIndex} {key : ValidatorIndex → Signatures.SecretKey}
    {run : Run config checks x y} (honestRun : run.Honest config honest key) (position : Nat)
    (slashed : (y.state.validators.data[position]?).map (·.slashed) = some true) :
    (x.state.validators.data[position]?).map (·.slashed) = some true := by
  have back : FlagsBack x.state y.state := by
    clear slashed
    induction run with
    | nil => exact .refl _
    | snoc pre step ih =>
      exact (ih fun other member => honestRun other (.earlier member step)).trans
        (FlagsBack.of_step step (honestRun step (.last pre step)))
  exact back position slashed

end EthLib.Consensus
