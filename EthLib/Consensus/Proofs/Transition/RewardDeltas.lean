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

/-! ## The deltas of each kind of vote before Altair -/

/-- A validator whose vote matches reads the leak, and pays no penalty for that kind of vote.

In a leak it earns its base reward.

Otherwise it earns its base reward times the attesting increments, over the active increments.

That quotient rounds down, and so do the increments. -/
theorem componentDelta_matched {base attestingBalance total reward penalty : Gwei}
    (computed : componentDelta state true base attestingBalance total = .ok (reward, penalty)) :
    ∃ leak, isInInactivityLeak state = .ok leak ∧ penalty = 0 ∧
      reward.toNat = if leak then base.toNat else
        base.toNat * (attestingBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) /
          (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  simp only [componentDelta, ↓reduceIte, bind_ok_iff] at computed
  obtain ⟨leak, leakOk, computed⟩ := computed
  refine ⟨leak, leakOk, ?_⟩
  cases leak
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok_iff, liftAccessor_ok, liftArith,
      mapError_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨numerator, numeratorOk, rfl, rfl⟩ := computed
    rw [mulChecked_ok_iff] at numeratorOk
    simp [UInt64.toNat_div, numeratorOk.2]
  · simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨rfl, rfl⟩ := computed
    simp

/-- For a registry within its limit, the deltas of each validator for one kind of vote.

The matching votes are those of some pending attestations.

A validator that is not eligible has no reward and no penalty.

An eligible validator among the unslashed signers reads the leak, and pays no penalty.

In a leak it earns its base reward.

Otherwise it earns its base reward times the attesting increments, over the active increments.

That quotient rounds down, and so do the increments.

An eligible validator that is not among them earns nothing and pays its base reward. -/
theorem getAttestationComponentDeltas_getD {attestations : Array (PendingAttestation preset)}
    {rewards penalties : Array Gwei} (within : state.RegistryWithinLimit)
    (computed : getAttestationComponentDeltas state attestations = .ok (rewards, penalties)) :
    ∃ total attesters attestingBalance, getTotalActiveBalance state = .ok total ∧
      getUnslashedAttestingIndices state attestations = .ok attesters ∧
      getTotalBalance state attesters = .ok attestingBalance ∧
      ∀ j (inside : j < state.validators.data.size), ∃ eligible,
        isEligibleValidator (getPreviousEpoch state) state.validators.data[j] = .ok eligible ∧
        (eligible = false → rewards.getD j 0 = 0 ∧ penalties.getD j 0 = 0) ∧
        (eligible = true → ∃ base, getBaseReward state total j.toUInt64 = .ok base ∧
          (j.toUInt64 ∈ attesters → ∃ leak, isInInactivityLeak state = .ok leak ∧
            (rewards.getD j 0).toNat = (if leak then base.toNat else
              base.toNat * (attestingBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) /
                (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ∧
            penalties.getD j 0 = 0) ∧
          (j.toUInt64 ∉ attesters → rewards.getD j 0 = 0 ∧ penalties.getD j 0 = base)) := by
  simp only [getAttestationComponentDeltas, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨total, totalOk, attesters, attestersOk, attestingBalance, balanceOk, eligible,
    eligibleOk, folded⟩ := computed
  obtain ⟨distinct, decided⟩ := getEligibleValidatorIndices_ok within eligibleOk
  refine ⟨total, attesters, attestingBalance, totalOk, attestersOk, balanceOk,
    fun j inside => ?_⟩
  obtain ⟨isEligible, eligibleJ, named⟩ := decided j inside
  have small := toNat_toUInt64_of_lt within inside
  -- Only the step of the validator itself changes its entries, and they start at zero.
  have entry := foldlM_entry (entry := fun deltas : Array Gwei × Array Gwei =>
      (deltas.1.getD j 0, deltas.2.getD j 0)) (j := j) (fun ⟨rewards, penalties⟩ index next step
        other => by
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
      obtain ⟨_, _, ⟨_, _⟩, _, _, rewardsOk, _, penaltiesOk, rfl⟩ := step
      rw [addDelta_getD_of_ne rewardsOk (Ne.symm other),
        addDelta_getD_of_ne penaltiesOk (Ne.symm other)]) distinct folded
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, inside, ↓reduceIte,
    Option.getD_some] at entry
  refine ⟨isEligible, eligibleJ, fun no => ?_, fun yes => ?_⟩
  · have := entry.1 fun index member same =>
      Bool.false_ne_true (no ▸ named.mp ⟨index, member, same⟩)
    simp only [Prod.mk.injEq] at this
    simp only [Array.getD_eq_getD_getElem?, this, and_self]
  · obtain ⟨index, member, same⟩ := named.mpr yes
    obtain ⟨⟨lastRewards, lastPenalties⟩, next, start, step, result⟩ := entry.2 index member same
    obtain rfl : index = j.toUInt64 := UInt64.toNat_inj.mp (same.trans small.symm)
    simp only [Prod.mk.injEq] at start result
    simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at step
    obtain ⟨base, baseOk, ⟨reward, penalty⟩, delta, newRewards, rewardsOk, newPenalties,
      penaltiesOk, rfl⟩ := step
    have rewardAdded := addDelta_getD_self rewardsOk
    have penaltyAdded := addDelta_getD_self penaltiesOk
    simp only [small, Array.getD_eq_getD_getElem?, start] at rewardAdded penaltyAdded
    refine ⟨base, baseOk, fun present => ?_, fun absent => ?_⟩
    · have marked := (markIndices_getD_iff within inside attesters).mpr present
      rw [Array.getD_eq_getD_getElem?] at marked
      rw [small, marked] at delta
      obtain ⟨leak, leakOk, rfl, value⟩ := componentDelta_matched delta
      refine ⟨leak, leakOk, ?_, ?_⟩
      · simp only [Array.getD_eq_getD_getElem?, result.1, rewardAdded, value]
        simp
      · apply UInt64.toNat_inj.mp
        simp only [Array.getD_eq_getD_getElem?, result.2, penaltyAdded]
        simp
    · have unmarked : (markIndices state.validators.data.size attesters).getD j false = false := by
        simpa using mt (markIndices_getD_iff within inside attesters).mp absent
      rw [Array.getD_eq_getD_getElem?] at unmarked
      rw [small, unmarked, componentDelta_unmatched, Except.ok.injEq, Prod.mk.injEq] at delta
      obtain ⟨rfl, rfl⟩ := delta
      refine ⟨?_, ?_⟩
      · apply UInt64.toNat_inj.mp
        simp only [Array.getD_eq_getD_getElem?, result.1, rewardAdded]
        simp
      · apply UInt64.toNat_inj.mp
        simp only [Array.getD_eq_getD_getElem?, result.2, penaltyAdded]
        simp

/-- One step of the inactivity penalties before Altair keeps the entries of the other validators. -/
theorem addInactivityPenalty_getD_of_ne {total : Gwei} {delay : Epoch}
    {targetMatched : Array Bool} {penalties next : Array Gwei} {index : ValidatorIndex}
    (computed : addInactivityPenalty state total delay targetMatched penalties index = .ok next)
    {j : Nat} (other : j ≠ index.toNat) : next.getD j 0 = penalties.getD j 0 := by
  simp only [addInactivityPenalty, bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, paid, paidOk, computed⟩ := computed
  rw [← addDelta_getD_of_ne paidOk other]
  split at computed
  · cases computed
    rfl
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, added⟩ := computed
    exact addDelta_getD_of_ne added other

/-- One step of the inactivity penalties before Altair, read at the index of its own validator.

The validator pays four base rewards less the proposer share of one.

If it missed the target, it also pays its effective balance times the finality delay.

That product is divided by the penalty quotient, rounding down.

The amounts are added to the entry, without overflow or underflow. -/
theorem addInactivityPenalty_getD_self {total : Gwei} {delay : Epoch}
    {targetMatched : Array Bool} {penalties next : Array Gwei} {index : ValidatorIndex}
    (computed : addInactivityPenalty state total delay targetMatched penalties index = .ok next) :
    ∃ base, getBaseReward state total index = .ok base ∧
      (targetMatched.getD index.toNat false = true →
        (next.getD index.toNat 0).toNat = (penalties.getD index.toNat 0).toNat +
          (BASE_REWARDS_PER_EPOCH.toNat * base.toNat -
            base.toNat / preset.PROPOSER_REWARD_QUOTIENT.toNat)) ∧
      (targetMatched.getD index.toNat false = false → ∃ validator,
        getValidator state index = .ok validator ∧
        (next.getD index.toNat 0).toNat = (penalties.getD index.toNat 0).toNat +
          (BASE_REWARDS_PER_EPOCH.toNat * base.toNat -
            base.toNat / preset.PROPOSER_REWARD_QUOTIENT.toNat) +
          validator.effectiveBalance.toNat * delay.toNat /
            (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) := by
  simp only [addInactivityPenalty, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff] at computed
  obtain ⟨base, baseOk, full, fullOk, paidBack, paidBackOk, paid, paidOk, computed⟩ := computed
  rw [mulChecked_ok_iff] at fullOk
  rw [subChecked_ok_iff] at paidBackOk
  have first := addDelta_getD_self paidOk
  rw [paidBackOk.2, fullOk.2, proposerReward, UInt64.toNat_div] at first
  refine ⟨base, baseOk, fun matched => ?_, fun missed => ?_⟩
  · simp only [matched, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact first
  · simp only [missed, Bool.false_eq_true, ↓reduceIte, bind_ok_iff, liftAccessor_ok,
      mapError_ok_iff] at computed
    obtain ⟨validator, validatorOk, scaled, scaledOk, added⟩ := computed
    rw [mulChecked_ok_iff] at scaledOk
    refine ⟨validator, validatorOk, ?_⟩
    rw [addDelta_getD_self added, first, UInt64.toNat_div, scaledOk.2]

/-- For a registry within its limit, the inactivity deltas of each validator, before Altair.

They hold no reward, and outside a leak no penalty.

In a leak, a validator that is not eligible pays nothing.

An eligible validator pays four base rewards less the proposer share of one.

If it is not among the unslashed signers of the target, it also pays more.

That amount is its effective balance times the finality delay, over the penalty quotient.

The quotients round down. -/
theorem getInactivityPenaltyDeltas_getD_of_lt_altair {config : Config} (before : fork < .altair)
    {rewards penalties : Array Gwei} (within : state.RegistryWithinLimit)
    (computed : getInactivityPenaltyDeltas config state = .ok (rewards, penalties)) :
    (∀ j, rewards.getD j 0 = 0) ∧ ∃ leak, isInInactivityLeak state = .ok leak ∧
      (leak = false → ∀ j, penalties.getD j 0 = 0) ∧
      (leak = true → ∃ attestations attesters total delay,
        getMatchingTargetAttestations state before (getPreviousEpoch state) = .ok attestations ∧
        getUnslashedAttestingIndices state attestations = .ok attesters ∧
        getTotalActiveBalance state = .ok total ∧ getFinalityDelay state = .ok delay ∧
        ∀ j (inside : j < state.validators.data.size), ∃ eligible,
          isEligibleValidator (getPreviousEpoch state) state.validators.data[j] = .ok eligible ∧
          (eligible = false → penalties.getD j 0 = 0) ∧
          (eligible = true → ∃ base, getBaseReward state total j.toUInt64 = .ok base ∧
            (penalties.getD j 0).toNat = BASE_REWARDS_PER_EPOCH.toNat * base.toNat -
              base.toNat / preset.PROPOSER_REWARD_QUOTIENT.toNat +
              (if j.toUInt64 ∈ attesters then 0 else
                state.validators.data[j].effectiveBalance.toNat * delay.toNat /
                  (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat))) := by
  refine ⟨getInactivityPenaltyDeltas_rewards computed, ?_⟩
  have notAltair : ¬ .altair ≤ fork := Nat.not_le_of_lt before
  unfold getInactivityPenaltyDeltas at computed
  dsimp only at computed
  simp only [notAltair, ↓reduceDIte, bind_ok_iff] at computed
  obtain ⟨leak, leakOk, computed⟩ := computed
  refine ⟨leak, leakOk, fun outside j => ?_, fun leaking => ?_⟩
  · subst outside
    simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at computed
    obtain ⟨-, rfl⟩ := computed
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  subst leaking
  simp only [↓reduceIte, bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq] at computed
  obtain ⟨attestations, attestationsOk, attesters, attestersOk, total, totalOk, delay, delayOk,
    eligible, eligibleOk, penalties, folded, -, rfl⟩ := computed
  obtain ⟨distinct, decided⟩ := getEligibleValidatorIndices_ok within eligibleOk
  refine ⟨attestations, attesters, total, delay, attestationsOk, attestersOk, totalOk, delayOk,
    fun j inside => ?_⟩
  obtain ⟨isEligible, eligibleJ, named⟩ := decided j inside
  have small := toNat_toUInt64_of_lt within inside
  -- Only the step of the validator itself changes its entry, and it starts at zero.
  have entry := foldlM_entry (entry := fun deltas : Array Gwei => deltas.getD j 0) (j := j)
    (fun _ _ _ step other => addInactivityPenalty_getD_of_ne step (Ne.symm other))
    distinct folded
  have zero : (Array.replicate state.validators.data.size (0 : Gwei)).getD j 0 = 0 := by
    simp [Array.getD_eq_getD_getElem?, inside]
  rw [zero] at entry
  refine ⟨isEligible, eligibleJ, fun no => ?_, fun yes => ?_⟩
  · exact entry.1 fun index member same =>
      Bool.false_ne_true (no ▸ named.mp ⟨index, member, same⟩)
  · obtain ⟨index, member, same⟩ := named.mpr yes
    obtain ⟨last, next, start, step, result⟩ := entry.2 index member same
    obtain rfl : index = j.toUInt64 := UInt64.toNat_inj.mp (same.trans small.symm)
    obtain ⟨base, baseOk, matched, missed⟩ := addInactivityPenalty_getD_self step
    refine ⟨base, baseOk, ?_⟩
    rw [small] at matched missed
    rw [result]
    by_cases present : j.toUInt64 ∈ attesters
    · rw [matched ((markIndices_getD_iff within inside attesters).mpr present), start]
      simp [present]
    · obtain ⟨validator, validatorOk, value⟩ :=
        missed (by simpa using mt (markIndices_getD_iff within inside attesters).mp present)
      rw [getValidator_toUInt64 within inside, Except.ok.injEq] at validatorOk
      subst validatorOk
      rw [value, start]
      simp [present]

/-! ## The inclusion rewards before Altair -/

/-- Adding a delta adds the amount to the entry at its index, and keeps the other entries. -/
theorem addDelta_getD {deltas result : Array Gwei} {index : ValidatorIndex} {amount : Gwei}
    (computed : addDelta deltas index amount = .ok result) (j : Nat) :
    (result.getD j 0).toNat =
      (deltas.getD j 0).toNat + if index.toNat = j then amount.toNat else 0 := by
  by_cases same : index.toNat = j
  · subst same
    simpa using addDelta_getD_self computed
  · simp [addDelta_getD_of_ne computed (Ne.symm same), same]

/-- One step of the inclusion rewards, for one attester.

The attester has an earliest inclusion, with a nonzero inclusion delay.

The proposer of that inclusion earns the proposer share of the base reward of the attester.

The attester earns the rest of its base reward, divided by the inclusion delay, rounding down.

The amounts are added to the entries, without overflow or underflow. -/
theorem addInclusionReward_getD {total : Gwei}
    {earliest : Array (Option (PendingAttestation preset))} {rewards next : Array Gwei}
    {index : ValidatorIndex}
    (computed : addInclusionReward state total earliest rewards index = .ok next) :
    ∃ attestation base, earliest.getD index.toNat none = some attestation ∧
      getBaseReward state total index = .ok base ∧ attestation.inclusionDelay ≠ 0 ∧
      ∀ j, (next.getD j 0).toNat = (rewards.getD j 0).toNat +
        ((if attestation.proposerIndex.toNat = j then
            base.toNat / preset.PROPOSER_REWARD_QUOTIENT.toNat else 0) +
          if index.toNat = j then
            (base.toNat - base.toNat / preset.PROPOSER_REWARD_QUOTIENT.toNat) /
              attestation.inclusionDelay.toNat else 0) := by
  unfold addInclusionReward at computed
  split at computed
  · rename_i attestation found
    simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff] at computed
    obtain ⟨base, baseOk, raised, raisedOk, rest, restOk, _, checked, added⟩ := computed
    have nonzero := ensure_ok_iff.mp checked
    rw [subChecked_ok_iff] at restOk
    refine ⟨attestation, base, found, baseOk, nonzero, fun j => ?_⟩
    rw [addDelta_getD added, addDelta_getD raisedOk, UInt64.toNat_div, restOk.2, proposerReward,
      UInt64.toNat_div, Nat.add_assoc]
  · cases computed

/-- A fold of inclusion rewards over some attesters adds the share of each one to each entry.

Each attester has an earliest inclusion, with a nonzero inclusion delay, and a base reward.

Its share goes to the proposer of that inclusion and to the attester itself. -/
theorem foldlM_addInclusionReward_getD {total : Gwei}
    {earliest : Array (Option (PendingAttestation preset))} :
    ∀ {attesters : List ValidatorIndex} {start result : Array Gwei},
      attesters.foldlM (addInclusionReward state total earliest) start = .ok result →
      ∃ shares : List (ValidatorIndex × PendingAttestation preset × Gwei),
        shares.map (·.1) = attesters ∧
        (∀ share ∈ shares, earliest.getD share.1.toNat none = some share.2.1 ∧
          getBaseReward state total share.1 = .ok share.2.2 ∧ share.2.1.inclusionDelay ≠ 0) ∧
        ∀ j, (result.getD j 0).toNat = (start.getD j 0).toNat + (shares.map fun share =>
          (if share.2.1.proposerIndex.toNat = j then
            share.2.2.toNat / preset.PROPOSER_REWARD_QUOTIENT.toNat else 0) +
          if share.1.toNat = j then
            (share.2.2.toNat - share.2.2.toNat / preset.PROPOSER_REWARD_QUOTIENT.toNat) /
              share.2.1.inclusionDelay.toNat else 0).sum
  | [], start, result, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨[], rfl, fun _ absent => absurd absent List.not_mem_nil, fun _ => by simp⟩
  | index :: rest, start, result, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, stepped, folded⟩ := computed
    obtain ⟨attestation, base, found, baseOk, nonzero, added⟩ := addInclusionReward_getD stepped
    obtain ⟨shares, named, facts, sums⟩ := foldlM_addInclusionReward_getD folded
    refine ⟨(index, attestation, base) :: shares, by simp [named], fun share member => ?_,
      fun j => ?_⟩
    · rcases List.mem_cons.mp member with rfl | member
      · exact ⟨found, baseOk, nonzero⟩
      · exact facts share member
    · rw [sums j, added j, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- The inclusion rewards before Altair, at each entry.

They hold no penalty.

Each unslashed signer of the matching source attestations has an earliest inclusion.

That inclusion has a nonzero inclusion delay, and the signer has a base reward.

The proposer of that inclusion earns the proposer share of that base reward.

The signer earns the rest of its base reward, divided by the inclusion delay, rounding down.

So a reward entry is the sum of these amounts over the signers, for the validator of that entry.

A proposer earns the shares of every signer whose earliest inclusion it proposed. -/
theorem getInclusionDelayDeltas_getD (before : fork < .altair) {rewards penalties : Array Gwei}
    (computed : getInclusionDelayDeltas state before = .ok (rewards, penalties)) :
    (∀ j, penalties.getD j 0 = 0) ∧
    ∃ attestations signers attesters total,
      getMatchingSourceAttestations state before (getPreviousEpoch state) = .ok attestations ∧
      attestations.toList.mapM (getPendingAttestingIndices state) = .ok signers ∧
      unslashedAmong state signers = .ok attesters ∧
      getTotalActiveBalance state = .ok total ∧
      ∃ shares : List (ValidatorIndex × PendingAttestation preset × Gwei),
        shares.map (·.1) = attesters ∧
        (∀ share ∈ shares, (earliestInclusions state.validators.data.size
            (attestations.zip signers.toArray)).getD share.1.toNat none = some share.2.1 ∧
          getBaseReward state total share.1 = .ok share.2.2 ∧ share.2.1.inclusionDelay ≠ 0) ∧
        ∀ j, (rewards.getD j 0).toNat = (shares.map fun share =>
          (if share.2.1.proposerIndex.toNat = j then
            share.2.2.toNat / preset.PROPOSER_REWARD_QUOTIENT.toNat else 0) +
          if share.1.toNat = j then
            (share.2.2.toNat - share.2.2.toNat / preset.PROPOSER_REWARD_QUOTIENT.toNat) /
              share.2.1.inclusionDelay.toNat else 0).sum := by
  simp only [getInclusionDelayDeltas, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq, Prod.mk.injEq] at computed
  obtain ⟨attestations, attestationsOk, signers, signersOk, attesters, attestersOk, total,
    totalOk, rewards, folded, rfl, rfl⟩ := computed
  have zero (j : Nat) : (Array.replicate state.validators.data.size (0 : Gwei)).getD j 0 = 0 := by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  obtain ⟨shares, named, facts, sums⟩ := foldlM_addInclusionReward_getD folded
  refine ⟨zero, attestations, signers, attesters, total, attestationsOk, signersOk, attestersOk,
    totalOk, shares, named, facts, fun j => ?_⟩
  rw [sums j, zero j]
  simp

/-! ## The attestation deltas before Altair -/

/-- Adding a delta keeps the number of entries. -/
theorem addDelta_size {deltas result : Array Gwei} {index : ValidatorIndex} {amount : Gwei}
    (computed : addDelta deltas index amount = .ok result) : result.size = deltas.size := by
  unfold addDelta at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    simp
  · cases computed

/-- The deltas for one kind of vote have one reward and one penalty for each validator. -/
theorem getAttestationComponentDeltas_size {attestations : Array (PendingAttestation preset)}
    {rewards penalties : Array Gwei}
    (computed : getAttestationComponentDeltas state attestations = .ok (rewards, penalties)) :
    rewards.size = state.validators.data.size ∧ penalties.size = state.validators.data.size := by
  simp only [getAttestationComponentDeltas, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, folded⟩ := computed
  refine foldlM_ok_invariant (fun deltas : Array Gwei × Array Gwei =>
      deltas.1.size = state.validators.data.size ∧ deltas.2.size = state.validators.data.size)
    (fun ⟨rewards, penalties⟩ index next sizes step => ?_) (by simp) folded
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
  obtain ⟨_, _, _, _, _, rewardsOk, _, penaltiesOk, rfl⟩ := step
  exact ⟨(addDelta_size rewardsOk).trans sizes.1, (addDelta_size penaltiesOk).trans sizes.2⟩

/-- The sums of four lists of deltas have one entry for each entry of the first list.

Each entry is the sum of the four entries at its index, without overflow.

An entry past the end of a list counts as zero. -/
theorem sumDeltas_getD {first second third fourth result : Array Gwei}
    (computed : sumDeltas first second third fourth = .ok result) (j : Nat) :
    (result.getD j 0).toNat = if j < first.size then (first.getD j 0).toNat +
      (second.getD j 0).toNat + (third.getD j 0).toNat + (fourth.getD j 0).toNat else 0 := by
  obtain ⟨sizes, entries⟩ := array_mapM_ok computed
  rw [Array.size_range] at sizes
  by_cases inside : j < first.size
  · simp only [inside, ↓reduceIte]
    have entry := entries j (by simpa using inside) (sizes ▸ inside)
    simp only [Array.getElem_range, liftAccessor_ok, liftArith, mapError_ok_iff,
      bind_ok_iff] at entry
    obtain ⟨pair, pairOk, triple, tripleOk, totalOk⟩ := entry
    rw [addChecked_ok_iff] at pairOk tripleOk totalOk
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (sizes ▸ inside),
      Option.getD_some, totalOk.2, tripleOk.2, pairOk.2]
  · simp [Array.getD_eq_getD_getElem?, sizes, inside]

/-- Before Altair, the attestation deltas of each validator are the sums of their parts.

The rewards are those of the source, target and head votes, and of the inclusion.

The penalties are those of the source, target and head votes, and of inactivity.

The sums do not overflow. -/
theorem getAttestationDeltas_getD {config : Config} (before : fork < .altair)
    {rewards penalties : Array Gwei}
    (computed : getAttestationDeltas config state before = .ok (rewards, penalties)) :
    ∃ source target head inclusion inactivity,
      getSourceDeltas state before = .ok source ∧ getTargetDeltas state before = .ok target ∧
      getHeadDeltas state before = .ok head ∧
      getInclusionDelayDeltas state before = .ok inclusion ∧
      getInactivityPenaltyDeltas config state = .ok inactivity ∧
      ∀ j, j < state.validators.data.size →
        (rewards.getD j 0).toNat = (source.1.getD j 0).toNat + (target.1.getD j 0).toNat +
          (head.1.getD j 0).toNat + (inclusion.1.getD j 0).toNat ∧
        (penalties.getD j 0).toNat = (source.2.getD j 0).toNat + (target.2.getD j 0).toNat +
          (head.2.getD j 0).toNat + (inactivity.2.getD j 0).toNat := by
  simp only [getAttestationDeltas, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨⟨sourceRewards, sourcePenalties⟩, sourceOk, ⟨targetRewards, targetPenalties⟩, targetOk,
    ⟨headRewards, headPenalties⟩, headOk, ⟨inclusionRewards, inclusionPenalties⟩, inclusionOk,
    ⟨inactivityRewards, inactivityPenalties⟩, inactivityOk, summedRewards, rewardsOk,
    summedPenalties, penaltiesOk, computed⟩ := computed
  simp only [Prod.mk.injEq] at computed
  obtain ⟨rfl, rfl⟩ := computed
  -- The source deltas have one entry for each validator, so every validator has a sum.
  have sizes : sourceRewards.size = state.validators.data.size ∧
      sourcePenalties.size = state.validators.data.size := by
    simp only [getSourceDeltas, bind_ok_iff] at sourceOk
    obtain ⟨_, _, sourceOk⟩ := sourceOk
    exact getAttestationComponentDeltas_size sourceOk
  refine ⟨_, _, _, _, _, sourceOk, targetOk, headOk, inclusionOk, inactivityOk,
    fun j inside => ⟨?_, ?_⟩⟩
  · rw [sumDeltas_getD rewardsOk j]
    simp only [show j < sourceRewards.size from sizes.1 ▸ inside, ↓reduceIte]
  · rw [sumDeltas_getD penaltiesOk j]
    simp only [show j < sourcePenalties.size from sizes.2 ▸ inside, ↓reduceIte]

end EthLib.Consensus
