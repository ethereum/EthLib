module

public import EthLib.Consensus.Proofs.Transition.EpochRewards

/-!
# Proofs: the amount of each reward and penalty

Each eligible validator appears once among the eligible indices, and the others not at all.

So a fold of the deltas over those indices touches the entry of each validator at most once.

That entry holds the amount that the step for its validator adds, and zero if no step adds one.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {state : BeaconState preset fork}

/-! ## The eligible validators -/

/-- For a registry within its limit, the eligible indices name each validator at most once.

Each one names a validator of the registry, and that validator is eligible.

The eligibility of every validator of the registry is decided without an error. -/
theorem getEligibleValidatorIndices_ok {eligible : List ValidatorIndex}
    (within : state.RegistryWithinLimit)
    (computed : getEligibleValidatorIndices state = .ok eligible) :
    (eligible.map UInt64.toNat).Nodup ∧
      ∀ j (inside : j < state.validators.data.size), ∃ decided,
        isEligibleValidator (getPreviousEpoch state) state.validators.data[j] = .ok decided ∧
          ((∃ index ∈ eligible, index.toNat = j) ↔ decided = true) := by
  -- The indices increase strictly, so no position repeats.
  refine ⟨List.pairwise_map.mpr ((getEligibleValidatorIndices_sorted within computed).imp
    fun lt => Nat.ne_of_lt (UInt64.lt_iff_toNat_lt.mp lt)), ?_⟩
  have succeeds := ok_of_filterMapM_ok computed
  have member {x : Validator × Nat} : x ∈ state.validators.data.toList.zipIdx ↔
      ∃ inside : x.2 < state.validators.data.size, state.validators.data[x.2] = x.1 := by
    rw [List.mem_zipIdx_iff_getElem?, Array.getElem?_toList, Array.getElem?_eq_some_iff]
  -- Each step succeeds, so it keeps the position exactly when it decides that it is eligible.
  let decide (x : Validator × Nat) : Bool :=
    match isEligibleValidator (getPreviousEpoch state) x.1 with
    | .ok decided => decided
    | .error _ => false
  obtain rfl := eq_filterMap_of_filterMapM_ok
    (g := fun x => if decide x then some x.2.toUInt64 else none)
    (fun ⟨validator, index⟩ _ image step => by
      simp only [bind_ok_iff] at step
      obtain ⟨decided, ok, step⟩ := step
      simp only [pure, Except.pure, Except.ok.injEq] at step
      subst step
      simp [decide, ok]) computed
  intro j inside
  obtain ⟨_, found⟩ := succeeds (state.validators.data[j], j) (member.mpr ⟨inside, rfl⟩)
  simp only [bind_ok_iff] at found
  obtain ⟨decided, ok, -⟩ := found
  refine ⟨decided, ok, ⟨fun ⟨index, chosen, named⟩ => ?_, fun yes => ?_⟩⟩
  · obtain ⟨⟨validator, k⟩, kInside, image⟩ := List.mem_filterMap.mp chosen
    obtain ⟨lt, same⟩ := member.mp kInside
    dsimp only at image lt same
    subst same
    split at image
    · rename_i chose
      simp only [Option.some.injEq] at image
      subst image
      obtain rfl : k = j := (toNat_toUInt64_of_lt within lt).symm.trans named
      simpa [decide, ok] using chose
    · cases image
  · refine ⟨j.toUInt64, List.mem_filterMap.mpr ⟨(state.validators.data[j], j),
      member.mpr ⟨inside, rfl⟩, by simp [decide, ok, yes]⟩, toNat_toUInt64_of_lt within inside⟩

/-! ## One entry of a fold over distinct indices -/

/-- A fold over indices that name each position at most once, read at one position.

Each step keeps the entry at the positions other than its own.

If no index names the position, its entry stays.

If one does, its entry is the one that the step of that index leaves from the starting entry. -/
theorem foldlM_entry {σ ε β : Type} {step : σ → ValidatorIndex → Except ε σ} {entry : σ → β}
    {j : Nat} (keeps : ∀ last index next, step last index = .ok next → index.toNat ≠ j →
      entry next = entry last) :
    ∀ {indices : List ValidatorIndex} {start result : σ}, (indices.map UInt64.toNat).Nodup →
      indices.foldlM step start = .ok result →
      ((∀ index ∈ indices, index.toNat ≠ j) → entry result = entry start) ∧
        ∀ index ∈ indices, index.toNat = j →
          ∃ last next, entry last = entry start ∧ step last index = .ok next ∧
            entry result = entry next
  | [], start, result, _, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨fun _ => rfl, fun _ absent => absurd absent List.not_mem_nil⟩
  | first :: rest, start, result, distinct, computed => by
    rw [List.map_cons, List.nodup_cons] at distinct
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, stepped, folded⟩ := computed
    have later := foldlM_entry keeps distinct.2 folded
    refine ⟨fun absent => ?_, fun index member named => ?_⟩
    · rw [later.1 fun index inside => absent index (List.mem_cons_of_mem _ inside)]
      exact keeps _ _ _ stepped (absent first List.mem_cons_self)
    rcases List.mem_cons.mp member with rfl | inside
    -- The first index names the position, so no later index does.
    · refine ⟨start, middle, rfl, stepped, later.1 fun other inside same => ?_⟩
      exact distinct.1 (named ▸ same ▸ List.mem_map_of_mem inside)
    · have other : first.toNat ≠ j := fun same =>
        distinct.1 (same ▸ named ▸ List.mem_map_of_mem inside)
      obtain ⟨last, next, start', step', result'⟩ := later.2 index inside named
      exact ⟨last, next, start'.trans (keeps _ _ _ stepped other), step', result'⟩

/-! ## The flag deltas from Altair -/

/-- One step of the flag deltas, read at the index of its own validator.

A validator that set the flag reads the leak.

In a leak it earns nothing; otherwise it earns the rounded share of the weighted base reward.

That share is the participating increments over the active increments.

A validator that did not set the flag pays the rounded weight of its base reward.

It pays nothing for the head flag.

Each amount is added to the entry, without overflow, and the other kind of delta stays. -/
theorem addFlagDelta_getD_self {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length}
    {participated : Array Bool} {total participatingIncrements activeIncrements : Gwei}
    {deltas next : Array Gwei × Array Gwei} {index : ValidatorIndex}
    (computed : addFlagDelta state flagIndex participated total participatingIncrements
      activeIncrements deltas index = .ok next) :
    ∃ base, getBaseReward state total index = .ok base ∧
      (participated.getD index.toNat false = true → ∃ leak, isInInactivityLeak state = .ok leak ∧
        (next.1.getD index.toNat 0).toNat = (deltas.1.getD index.toNat 0).toNat +
          (if leak then 0 else base.toNat * PARTICIPATION_FLAG_WEIGHTS[flagIndex].toNat *
            participatingIncrements.toNat / (activeIncrements.toNat * WEIGHT_DENOMINATOR.toNat)) ∧
        next.2.getD index.toNat 0 = deltas.2.getD index.toNat 0) ∧
      (participated.getD index.toNat false = false →
        next.1.getD index.toNat 0 = deltas.1.getD index.toNat 0 ∧
        (next.2.getD index.toNat 0).toNat = (deltas.2.getD index.toNat 0).toNat +
          (if flagIndex.val.toUInt64 = TIMELY_HEAD_FLAG_INDEX then 0
            else base.toNat * PARTICIPATION_FLAG_WEIGHTS[flagIndex].toNat /
              WEIGHT_DENOMINATOR.toNat)) := by
  obtain ⟨base, baseOk⟩ := addFlagDelta_base computed
  refine ⟨base, baseOk, fun set => ?_, fun unset => ?_⟩
  · -- The set branch is upstream's reward of a set flag, and keeps the penalty.
    obtain ⟨leak, leakOk⟩ := addFlagDelta_leak computed set
    exact ⟨leak, leakOk, addFlagDelta_reward_of_set computed set baseOk leakOk,
      addFlagDelta_penalty computed (.inl set)⟩
  refine ⟨addFlagDelta_reward computed (.inl unset), ?_⟩
  obtain ⟨rewards, penalties⟩ := deltas
  simp only [addFlagDelta, bind_ok_iff, liftAccessor_ok, baseOk, Except.ok.injEq,
    exists_eq_left', unset, Bool.false_eq_true, ↓reduceIte] at computed
  split at computed
  · rename_i head
    simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp [head]
  · rename_i notHead
    simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨scaled, scaledOk, added, addedOk, rfl⟩ := computed
    rw [mulChecked_ok_iff] at scaledOk
    rw [addDelta_getD_self addedOk, UInt64.toNat_div, scaledOk.2]
    simp only [notHead, ↓reduceIte]

/-- One step of the flag deltas keeps the entries of the other validators. -/
theorem addFlagDelta_getD_of_ne {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length}
    {participated : Array Bool} {total participatingIncrements activeIncrements : Gwei}
    {deltas next : Array Gwei × Array Gwei} {index : ValidatorIndex}
    (computed : addFlagDelta state flagIndex participated total participatingIncrements
      activeIncrements deltas index = .ok next) {j : Nat} (other : j ≠ index.toNat) :
    (next.1.getD j 0, next.2.getD j 0) = (deltas.1.getD j 0, deltas.2.getD j 0) := by
  obtain ⟨rewards, penalties⟩ := deltas
  simp only [addFlagDelta, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      rfl
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
      obtain ⟨_, _, _, _, _, _, _, ok, rfl⟩ := computed
      rw [addDelta_getD_of_ne ok other]
  · split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      rfl
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
      obtain ⟨_, _, _, ok, rfl⟩ := computed
      rw [addDelta_getD_of_ne ok other]

/-- A validator of a registry within its limit is marked exactly when its own index is listed. -/
theorem markIndices_getD_iff (within : state.RegistryWithinLimit) {j : Nat}
    (inside : j < state.validators.data.size) (indices : List ValidatorIndex) :
    (markIndices state.validators.data.size indices).getD j false = true ↔
      j.toUInt64 ∈ indices := by
  have small := toNat_toUInt64_of_lt within inside
  rw [Array.getD_eq_getD_getElem?, getElem?_markIndices]
  simp only [inside, ↓reduceIte, Option.getD_some, List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨index, member, named⟩
    rwa [show index = j.toUInt64 from UInt64.toNat_inj.mp (named.trans small.symm)] at member
  · exact fun member => ⟨_, member, small⟩

/-- For a registry within its limit, the flag deltas of each validator, from Altair.

A validator that is not eligible has no reward and no penalty.

An eligible validator that set the flag reads the leak, and pays no penalty.

In a leak it earns nothing.

Otherwise it earns its base reward times the weight of the flag times the participating increments.

That product is divided by the active increments times the weight denominator, rounding down.

An eligible validator that did not set the flag earns nothing.

It pays its base reward times the weight of the flag, over the weight denominator, rounding down.

For the head flag it pays nothing.

The increments are the balances divided by the effective balance increment, rounding down. -/
theorem getFlagIndexDeltas_getD {altair : .altair ≤ fork}
    {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length} {rewards penalties : Array Gwei}
    (within : state.RegistryWithinLimit)
    (computed : getFlagIndexDeltas state altair flagIndex = .ok (rewards, penalties)) :
    ∃ participating participatingBalance total,
      getUnslashedParticipatingIndices state altair flagIndex.val.toUInt64
        (getPreviousEpoch state) = .ok participating ∧
      getTotalBalance state participating = .ok participatingBalance ∧
      getTotalActiveBalance state = .ok total ∧
      ∀ j (inside : j < state.validators.data.size), ∃ eligible,
        isEligibleValidator (getPreviousEpoch state) state.validators.data[j] = .ok eligible ∧
        (eligible = false → rewards.getD j 0 = 0 ∧ penalties.getD j 0 = 0) ∧
        (eligible = true → ∃ base, getBaseReward state total j.toUInt64 = .ok base ∧
          (j.toUInt64 ∈ participating → ∃ leak, isInInactivityLeak state = .ok leak ∧
            (rewards.getD j 0).toNat = (if leak then 0 else
              base.toNat * PARTICIPATION_FLAG_WEIGHTS[flagIndex].toNat *
                (participatingBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) /
                (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
                  WEIGHT_DENOMINATOR.toNat)) ∧
            penalties.getD j 0 = 0) ∧
          (j.toUInt64 ∉ participating → rewards.getD j 0 = 0 ∧
            (penalties.getD j 0).toNat = (if flagIndex.val.toUInt64 = TIMELY_HEAD_FLAG_INDEX then 0
              else base.toNat * PARTICIPATION_FLAG_WEIGHTS[flagIndex].toNat /
                WEIGHT_DENOMINATOR.toNat))) := by
  simp only [getFlagIndexDeltas, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨participating, participatingOk, participatingBalance, balanceOk, total, totalOk,
    eligible, eligibleOk, folded⟩ := computed
  obtain ⟨distinct, decided⟩ := getEligibleValidatorIndices_ok within eligibleOk
  refine ⟨participating, participatingBalance, total, participatingOk, balanceOk, totalOk,
    fun j inside => ?_⟩
  obtain ⟨isEligible, eligibleJ, named⟩ := decided j inside
  have small := toNat_toUInt64_of_lt within inside
  -- Only the step of the validator itself changes its entries, and they start at zero.
  have entry := foldlM_entry (entry := fun deltas : Array Gwei × Array Gwei =>
      (deltas.1.getD j 0, deltas.2.getD j 0)) (j := j)
    (fun _ _ _ step other => addFlagDelta_getD_of_ne step (Ne.symm other)) distinct folded
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, inside, ↓reduceIte,
    Option.getD_some] at entry
  refine ⟨isEligible, eligibleJ, fun no => ?_, fun yes => ?_⟩
  · have absent : ∀ index ∈ eligible, index.toNat ≠ j := fun index member same =>
      Bool.false_ne_true (no ▸ named.mp ⟨index, member, same⟩)
    have := entry.1 absent
    simp only [Prod.mk.injEq] at this
    simp only [Array.getD_eq_getD_getElem?, this, and_self]
  · obtain ⟨index, member, same⟩ := named.mpr yes
    obtain ⟨last, next, start, step, result⟩ := entry.2 index member same
    obtain rfl : index = j.toUInt64 := UInt64.toNat_inj.mp (same.trans small.symm)
    simp only [Prod.mk.injEq] at start result
    obtain ⟨base, baseOk, set, unset⟩ := addFlagDelta_getD_self step
    simp only [Array.getD_eq_getD_getElem?, small] at set unset
    refine ⟨base, baseOk, fun present => ?_, fun absent => ?_⟩
    · have marked := (markIndices_getD_iff within inside participating).mpr present
      rw [Array.getD_eq_getD_getElem?] at marked
      obtain ⟨leak, leakOk, reward, penalty⟩ := set marked
      refine ⟨leak, leakOk, ?_, ?_⟩
      · simp only [Array.getD_eq_getD_getElem?, result.1, reward, start.1]
        simp
      · simp only [Array.getD_eq_getD_getElem?, result.2, penalty, start.2]
    · have unmarked : (markIndices state.validators.data.size participating)[j]?.getD false =
          false := by
        rw [← Array.getD_eq_getD_getElem?]
        simpa using mt (markIndices_getD_iff within inside participating).mp absent
      obtain ⟨reward, penalty⟩ := unset unmarked
      refine ⟨?_, ?_⟩
      · simp only [Array.getD_eq_getD_getElem?, result.1, reward, start.1]
      · simp only [Array.getD_eq_getD_getElem?, result.2, penalty, start.2]
        simp

/-! ## The inactivity deltas from Altair -/

/-- One step of the inactivity penalties from Altair keeps the entries of the other validators. -/
theorem addInactivityScorePenalty_getD_of_ne {config : Config} {altair : .altair ≤ fork}
    {targetMatched : Array Bool} {penalties next : Array Gwei} {index : ValidatorIndex}
    (computed : addInactivityScorePenalty config state altair targetMatched penalties index =
      .ok next)
    {j : Nat} (other : j ≠ index.toNat) : next.getD j 0 = penalties.getD j 0 := by
  unfold addInactivityScorePenalty at computed
  split at computed
  · cases computed
    rfl
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, _, _, _, _, ok⟩ := computed
      exact addDelta_getD_of_ne ok other
    · cases computed

/-- One step of the inactivity penalties from Altair, read at the index of its own validator.

A validator that missed the target pays its effective balance times its inactivity score.

That product is divided by the score bias times the penalty quotient, rounding down.

The amount is added to the entry, without overflow. -/
theorem addInactivityScorePenalty_getD_self {config : Config} {altair : .altair ≤ fork}
    {targetMatched : Array Bool} {penalties next : Array Gwei} {index : ValidatorIndex}
    (computed : addInactivityScorePenalty config state altair targetMatched penalties index =
      .ok next)
    (missed : targetMatched.getD index.toNat false = false) :
    ∃ validator score, getValidator state index = .ok validator ∧
      (state.inactivityScores altair).data[index.toNat]? = some score ∧
      (next.getD index.toNat 0).toNat = (penalties.getD index.toNat 0).toNat +
        validator.effectiveBalance.toNat * score.toNat / (config.INACTIVITY_SCORE_BIAS.toNat *
          (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) := by
  unfold addInactivityScorePenalty at computed
  simp only [missed, Bool.false_eq_true, ↓reduceIte, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, validatorOk, computed⟩ := computed
  split at computed
  · rename_i score scoreOk
    simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff] at computed
    obtain ⟨numerator, numeratorOk, denominator, denominatorOk, penalty, penaltyOk, added⟩ :=
      computed
    rw [mulChecked_ok_iff] at numeratorOk denominatorOk
    rw [divChecked_ok_iff] at penaltyOk
    refine ⟨validator, score, validatorOk, scoreOk, ?_⟩
    rw [addDelta_getD_self added, penaltyOk.2, numeratorOk.2, denominatorOk.2]
  · cases computed

/-- A validator of the registry is the one that its own index reads. -/
theorem getValidator_toUInt64 (within : state.RegistryWithinLimit) {j : Nat}
    (inside : j < state.validators.data.size) :
    getValidator state j.toUInt64 = .ok state.validators.data[j] := by
  simp [getValidator, toNat_toUInt64_of_lt within inside, inside]

/-- For a registry within its limit, the inactivity deltas of each validator, from Altair.

They hold no reward.

A validator pays no inactivity penalty if it is not eligible, or if it had a timely target.

An eligible validator that missed the target pays its effective balance times its inactivity score.

That product is divided by the score bias times the penalty quotient, rounding down.

This holds in a leak and outside one. -/
theorem getInactivityPenaltyDeltas_getD_of_altair {config : Config} (altair : .altair ≤ fork)
    {rewards penalties : Array Gwei} (within : state.RegistryWithinLimit)
    (computed : getInactivityPenaltyDeltas config state = .ok (rewards, penalties)) :
    ∃ matching, getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
        (getPreviousEpoch state) = .ok matching ∧
      ∀ j (inside : j < state.validators.data.size), ∃ eligible,
        isEligibleValidator (getPreviousEpoch state) state.validators.data[j] = .ok eligible ∧
        rewards.getD j 0 = 0 ∧
        (eligible = false ∨ j.toUInt64 ∈ matching → penalties.getD j 0 = 0) ∧
        (eligible = true → j.toUInt64 ∉ matching → ∃ score,
          (state.inactivityScores altair).data[j]? = some score ∧
          (penalties.getD j 0).toNat = state.validators.data[j].effectiveBalance.toNat *
            score.toNat / (config.INACTIVITY_SCORE_BIAS.toNat *
              (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat)) := by
  have noRewards := getInactivityPenaltyDeltas_rewards computed
  unfold getInactivityPenaltyDeltas at computed
  dsimp only at computed
  simp only [altair, ↓reduceDIte, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq, Prod.mk.injEq] at computed
  obtain ⟨matching, matchingOk, eligible, eligibleOk, penalties, folded, -, rfl⟩ := computed
  obtain ⟨distinct, decided⟩ := getEligibleValidatorIndices_ok within eligibleOk
  refine ⟨matching, matchingOk, fun j inside => ?_⟩
  obtain ⟨isEligible, eligibleJ, named⟩ := decided j inside
  have small := toNat_toUInt64_of_lt within inside
  -- Only the step of the validator itself changes its entry, and it starts at zero.
  have entry := foldlM_entry (entry := fun deltas : Array Gwei => deltas.getD j 0) (j := j)
    (fun _ _ _ step other => addInactivityScorePenalty_getD_of_ne step (Ne.symm other))
    distinct folded
  have zero : (Array.replicate state.validators.data.size (0 : Gwei)).getD j 0 = 0 := by
    simp [Array.getD_eq_getD_getElem?, inside]
  rw [zero] at entry
  refine ⟨isEligible, eligibleJ, noRewards j, fun exempt => ?_, fun yes missed => ?_⟩
  · rcases exempt with no | present
    · exact entry.1 fun index member same =>
        Bool.false_ne_true (no ▸ named.mp ⟨index, member, same⟩)
    · by_cases listed : ∃ index ∈ eligible, index.toNat = j
      · obtain ⟨index, member, same⟩ := listed
        obtain ⟨last, next, start, step, result⟩ := entry.2 index member same
        obtain rfl : index = j.toUInt64 := UInt64.toNat_inj.mp (same.trans small.symm)
        have marked := (markIndices_getD_iff within inside matching).mpr present
        rw [result, ← small, addInactivityScorePenalty_matched step (small.symm ▸ marked), small,
          start]
      · exact entry.1 fun index member same => listed ⟨index, member, same⟩
  · obtain ⟨index, member, same⟩ := named.mpr yes
    obtain ⟨last, next, start, step, result⟩ := entry.2 index member same
    obtain rfl : index = j.toUInt64 := UInt64.toNat_inj.mp (same.trans small.symm)
    have unmarked : (markIndices state.validators.data.size matching).getD j.toUInt64.toNat false =
        false := by
      rw [small]
      simpa using mt (markIndices_getD_iff within inside matching).mp missed
    obtain ⟨validator, score, validatorOk, scoreOk, penalty⟩ :=
      addInactivityScorePenalty_getD_self step unmarked
    rw [getValidator_toUInt64 within inside, Except.ok.injEq] at validatorOk
    subst validatorOk
    rw [small] at scoreOk penalty
    refine ⟨score, scoreOk, ?_⟩
    rw [result, penalty, start]
    simp

end EthLib.Consensus
