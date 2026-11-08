module

public import EthLib.Consensus.Proofs.Transition.EpochRewards

/-!
# Proofs: the amount of each reward and penalty

For each validator of a registry within its limit, these proofs state its reward and penalty.

They cover the flag and inactivity deltas from Altair, and the attestation deltas before Altair.

Each eligible validator appears once among the eligible indices, so a fold touches its entry once.

The proposer of the earliest inclusion of a signer earns a share of the signer's base reward.

The signer earns the rest, divided by its inclusion delay.

Every quotient rounds down, and no sum or product overflows.

No EIP specifies these Phase 0 and Altair rules, so the theorems below state them.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {state : BeaconState preset fork}

/-! ## The eligible validators -/

/-- For a registry within its limit, the eligible indices name each validator at most once.

A position is listed exactly when its validator is eligible.

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
  have succeeds := filterMapM_ok_of_mem computed
  have member {x : Validator × Nat} : x ∈ state.validators.data.toList.zipIdx ↔
      ∃ inside : x.2 < state.validators.data.size, state.validators.data[x.2] = x.1 := by
    rw [List.mem_zipIdx_iff_getElem?, Array.getElem?_toList, Array.getElem?_eq_some_iff]
  -- Each step succeeds, so it keeps the position exactly when it decides that it is eligible.
  obtain rfl := getEligibleValidatorIndices_eq computed
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
    · rename_i passes chose
      obtain ⟨passed, picked⟩ := Option.ite_none_right_eq_some.mp image
      obtain rfl := Option.some.inj picked
      obtain rfl : k = j := (toNat_toUInt64_of_lt within lt).symm.trans named
      rw [ok, Except.ok.injEq] at chose
      exact chose ▸ passed
    · simp at image
  · refine ⟨j.toUInt64, List.mem_filterMap.mpr ⟨(state.validators.data[j], j),
      member.mpr ⟨inside, rfl⟩, by simp [ok, yes]⟩, toNat_toUInt64_of_lt within inside⟩

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

For a validator that set the flag, the reward depends on the leak.

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
  · -- The set branch adds the reward of a set flag, and keeps the penalty.
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

An eligible validator among the unslashed participants pays no penalty.

Its reward depends on the leak.

In a leak it earns nothing.

Otherwise it earns its base reward times the weight of the flag times the participating increments.

That product is divided by the active increments times the weight denominator, rounding down.

An eligible validator that is not among them earns nothing.

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
  have whole := computed
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
    obtain ⟨base, baseOk, -, unset⟩ := addFlagDelta_getD_self step
    simp only [Array.getD_eq_getD_getElem?, small] at unset
    refine ⟨base, baseOk, fun present => ?_, fun absent => ?_⟩
    -- A participant's reward and penalty are the merged theorems on the set flag.
    · obtain ⟨base', leak, baseOk', leakOk, reward⟩ :=
        getFlagIndexDeltas_reward within whole participatingOk balanceOk totalOk present
      obtain rfl : base' = base := Except.ok.inj (baseOk'.symm.trans baseOk)
      have penalty := getFlagIndexDeltas_present whole participatingOk present
        (by rw [small]; exact inside)
      rw [small] at reward penalty
      exact ⟨leak, leakOk, reward, penalty⟩
    · have unmarked : (markIndices state.validators.data.size participating)[j]?.getD false =
          false := by
        rw [← Array.getD_eq_getD_getElem?]
        simpa using mt (markIndices_getD_iff within inside participating).mp absent
      obtain ⟨-, penalty⟩ := unset unmarked
      refine ⟨getFlagIndexDeltas_absent whole participatingOk fun participant member named =>
        absent (UInt64.toNat_inj.mp (named.trans small.symm) ▸ member), ?_⟩
      simp only [Array.getD_eq_getD_getElem?, result.2, penalty, start.2]
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

A validator pays no inactivity penalty if it is not eligible.

Neither does one among the unslashed validators with a timely target.

Any other eligible validator pays its effective balance times its inactivity score.

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
  have whole := computed
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
  rw [replicate_getD_zero] at entry
  refine ⟨isEligible, eligibleJ, noRewards j, fun exempt => ?_, fun yes missed => ?_⟩
  · rcases exempt with no | present
    · exact entry.1 fun index member same =>
        Bool.false_ne_true (no ▸ named.mp ⟨index, member, same⟩)
    -- A timely target is the merged theorem.
    · have penalty := getInactivityPenaltyDeltas_target altair whole matchingOk present
        (by rw [small]; exact inside)
      rwa [small] at penalty
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

/-- A validator whose vote matches pays no penalty for that kind of vote.

Its reward depends on the leak.

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

An eligible validator among the unslashed signers pays no penalty.

Its reward depends on the leak.

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
  have whole := computed
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
      -- An absent signer earns nothing, by the merged theorem.
      refine ⟨getAttestationComponentDeltas_absent whole attestersOk fun attester member named =>
        absent (UInt64.toNat_inj.mp (named.trans small.symm) ▸ member), ?_⟩
      apply UInt64.toNat_inj.mp
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
    exact replicate_getD_zero _ _
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
  rw [replicate_getD_zero] at entry
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

/-- The earliest inclusion kept after one more attestation: the old one, unless it is later. -/
def keepEarliest (attestation : PendingAttestation preset) :
    Option (PendingAttestation preset) → Option (PendingAttestation preset)
  | some kept => if attestation.inclusionDelay < kept.inclusionDelay then some attestation
      else some kept
  | none => some attestation

/-- Keeping the earliest of the same attestation twice keeps it once. -/
private theorem keepEarliest_keepEarliest (attestation : PendingAttestation preset)
    (kept : Option (PendingAttestation preset)) :
    keepEarliest attestation (keepEarliest attestation kept) = keepEarliest attestation kept := by
  cases kept with
  | none => simp [keepEarliest]
  | some kept =>
    by_cases earlier : attestation.inclusionDelay < kept.inclusionDelay
    · simp [keepEarliest, earlier]
    · simp [keepEarliest, earlier]

/-- The signers of one attestation each keep the earlier of their inclusion and this one. -/
private theorem foldl_signers_getElem? (attestation : PendingAttestation preset) (i : Nat) :
    ∀ (signers : List ValidatorIndex) (best : Array (Option (PendingAttestation preset))),
      (signers.foldl (init := best) fun best index =>
          match best.getD index.toNat none with
          | some kept => if attestation.inclusionDelay < kept.inclusionDelay then
              best.setIfInBounds index.toNat (some attestation) else best
          | none => best.setIfInBounds index.toNat (some attestation))[i]? =
        if signers.any (·.toNat == i) then best[i]?.map (keepEarliest attestation) else best[i]?
  | [], best => by simp
  | index :: signers, best => by
    rw [List.foldl_cons, foldl_signers_getElem? attestation i signers]
    -- The step changes the entry of its own signer only, and keeps the earliest there.
    have step : (match best.getD index.toNat none with
        | some kept => if attestation.inclusionDelay < kept.inclusionDelay then
            best.setIfInBounds index.toNat (some attestation) else best
        | none => best.setIfInBounds index.toNat (some attestation))[i]? =
        if index.toNat = i then best[i]?.map (keepEarliest attestation) else best[i]? := by
      by_cases same : index.toNat = i
      · subst same
        rw [Array.getD_eq_getD_getElem?]
        by_cases inside : index.toNat < best.size
        · rw [Array.getElem?_eq_getElem inside, Option.getD_some]
          cases found : best[index.toNat] with
          | none => simp [keepEarliest, inside]
          | some kept =>
            by_cases earlier : attestation.inclusionDelay < kept.inclusionDelay
            · simp [keepEarliest, earlier, inside]
            · simp [keepEarliest, earlier, Array.getElem?_eq_getElem inside, found]
        · have outside : best[index.toNat]? = none := Array.getElem?_eq_none (by omega)
          simp [Nat.le_of_not_lt inside]
      · simp only [same, ↓reduceIte]
        split
        · split <;> simp [same]
        · simp [same]
    rw [step]
    by_cases same : index.toNat = i
    · simp only [same, ↓reduceIte, List.any_cons, beq_self_eq_true, Bool.true_or]
      split
      · rw [Option.map_map]
        congr 1
        funext kept
        exact keepEarliest_keepEarliest attestation kept
      · rfl
    · simp [same]

/-- Keeping the earliest over a list of attestations of a given length, from none.

It keeps none exactly when the list is empty.

Otherwise it keeps the first attestation with the least inclusion delay. -/
private theorem foldl_keepEarliest_of_length (count : Nat) :
    ∀ attestations : List (PendingAttestation preset), attestations.length = count →
      (attestations.foldl (fun kept attestation => keepEarliest attestation kept) none = none ↔
        attestations = []) ∧
      ∀ earliest, attestations.foldl (fun kept attestation => keepEarliest attestation kept) none =
          some earliest →
        ∃ k, ∃ inside : k < attestations.length, attestations[k] = earliest ∧
          (∀ other ∈ attestations, earliest.inclusionDelay ≤ other.inclusionDelay) ∧
          ∀ k' (before : k' < k), earliest.inclusionDelay < attestations[k'].inclusionDelay := by
  -- The fold reads the attestations from the left, so take off the last one.
  induction count with
  | zero =>
    intro attestations counted
    obtain rfl := List.eq_nil_of_length_eq_zero counted
    simp
  | succ count ih =>
    intro attestations counted
    obtain rfl | ⟨attestations, last, rfl⟩ := List.eq_nil_or_concat attestations
    · cases counted
    rw [List.concat_eq_append, List.length_append, List.length_singleton,
      Nat.add_right_cancel_iff] at counted
    have ih := ih attestations counted
    rw [List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨?_, fun earliest kept => ?_⟩
    · cases attestations.foldl (fun kept attestation => keepEarliest attestation kept) none with
      | none => simp [keepEarliest]
      | some first =>
        simp only [keepEarliest]
        split <;> simp
    cases found : attestations.foldl (fun kept attestation => keepEarliest attestation kept)
      none with
    | none =>
      rw [found] at kept
      obtain rfl := ih.1.mp found
      simp only [keepEarliest, Option.some.injEq] at kept
      subst kept
      exact ⟨0, by simp, rfl, by simp, fun _ before => absurd before (Nat.not_lt_zero _)⟩
    | some first =>
      obtain ⟨k, inside, named, least, strictly⟩ := ih.2 first found
      rw [found] at kept
      simp only [keepEarliest] at kept
      split at kept
      · rename_i earlier
        simp only [Option.some.injEq] at kept
        subst kept
        refine ⟨attestations.length, by simp, by simp, fun other member => ?_,
          fun k' before => ?_⟩
        · rcases List.mem_append.mp member with member | member
          · exact Nat.le_of_lt (Nat.lt_of_lt_of_le earlier (least other member))
          · simp only [List.mem_singleton] at member
            subst member
            exact Nat.le_refl _
        · rw [List.getElem_append_left before]
          exact Nat.lt_of_lt_of_le earlier (least _ (List.getElem_mem _))
      · rename_i later
        simp only [Option.some.injEq] at kept
        subst kept
        refine ⟨k, (by simp; omega), (by rw [List.getElem_append_left inside]; exact named),
          fun other member => ?_, fun k' before => ?_⟩
        · rcases List.mem_append.mp member with member | member
          · exact least other member
          · simp only [List.mem_singleton] at member
            subst member
            exact Nat.le_of_not_lt later
        · rw [List.getElem_append_left (by omega)]
          exact strictly k' before

/-- Keeping the earliest over a list of attestations, from none, keeps the first earliest one.

It keeps none exactly when the list is empty.

Otherwise it keeps one with the least inclusion delay, before which every one has a larger delay. -/
theorem foldl_keepEarliest (attestations : List (PendingAttestation preset)) :
    (attestations.foldl (fun kept attestation => keepEarliest attestation kept) none = none ↔
      attestations = []) ∧
    ∀ earliest, attestations.foldl (fun kept attestation => keepEarliest attestation kept) none =
        some earliest →
      ∃ k, ∃ inside : k < attestations.length, attestations[k] = earliest ∧
        (∀ other ∈ attestations, earliest.inclusionDelay ≤ other.inclusionDelay) ∧
        ∀ k' (before : k' < k), earliest.inclusionDelay < attestations[k'].inclusionDelay :=
  foldl_keepEarliest_of_length _ attestations rfl

/-- The attestations of some signed pairs that list a validator as a signer, in their order. -/
def attestationsListing (signed : List (PendingAttestation preset × List ValidatorIndex))
    (i : Nat) : List (PendingAttestation preset) :=
  (signed.filter fun pair => pair.2.any fun signer => signer.toNat == i).map Prod.fst

/-- The earliest inclusion of a validator, among the signed attestations, in their order.

A validator of the registry has none exactly when no attestation lists it as a signer.

Otherwise it has one of the attestations that list it, with the least inclusion delay.

Every attestation before it in the list that lists the validator has a larger delay. -/
theorem earliestInclusions_getD {size : Nat}
    {signed : Array (PendingAttestation preset × List ValidatorIndex)} {i : Nat}
    (inside : i < size) :
    ((earliestInclusions size signed).getD i none = none ↔
      ∀ pair ∈ signed.toList, ∀ signer ∈ pair.2, signer.toNat ≠ i) ∧
    ∀ earliest, (earliestInclusions size signed).getD i none = some earliest →
      ∃ k, ∃ listed : k < (attestationsListing signed.toList i).length,
        (attestationsListing signed.toList i)[k] = earliest ∧
        (∀ other ∈ attestationsListing signed.toList i,
          earliest.inclusionDelay ≤ other.inclusionDelay) ∧
        ∀ k' (before : k' < k), earliest.inclusionDelay <
          (attestationsListing signed.toList i)[k'].inclusionDelay := by
  -- The entry of the validator keeps the earliest over the attestations that list it.
  have entry : ∀ (pairs : List (PendingAttestation preset × List ValidatorIndex))
      (best : Array (Option (PendingAttestation preset))),
      (pairs.foldl (init := best) fun best (attestation, signers) =>
          signers.foldl (init := best) fun best index =>
            match best.getD index.toNat none with
            | some kept => if attestation.inclusionDelay < kept.inclusionDelay then
                best.setIfInBounds index.toNat (some attestation) else best
            | none => best.setIfInBounds index.toNat (some attestation))[i]? =
        best[i]?.map fun kept => (attestationsListing pairs i).foldl
          (fun kept attestation => keepEarliest attestation kept) kept := by
    intro pairs
    induction pairs with
    | nil =>
      intro best
      simp [attestationsListing]
    | cons pair pairs ih =>
      intro best
      obtain ⟨attestation, signers⟩ := pair
      rw [List.foldl_cons, ih, foldl_signers_getElem?]
      by_cases listed : signers.any (·.toNat == i)
      · simp only [listed, ↓reduceIte, Option.map_map, attestationsListing, List.filter_cons,
          List.map_cons, List.foldl_cons]
        rfl
      · simp only [listed, Bool.false_eq_true, ↓reduceIte, attestationsListing, List.filter_cons]
  have kept : (earliestInclusions size signed)[i]? =
      some ((attestationsListing signed.toList i).foldl
        (fun kept attestation => keepEarliest attestation kept) none) := by
    unfold earliestInclusions
    rw [← Array.foldl_toList]
    refine (entry signed.toList (Array.replicate size none)).trans ?_
    simp [inside]
  have found : (earliestInclusions size signed).getD i none =
      (attestationsListing signed.toList i).foldl
        (fun kept attestation => keepEarliest attestation kept) none := by
    rw [Array.getD_eq_getD_getElem?, kept, Option.getD_some]
  rw [found]
  obtain ⟨empty, chosen⟩ := foldl_keepEarliest
    (attestationsListing signed.toList i)
  refine ⟨empty.trans ?_, chosen⟩
  simp only [attestationsListing, List.map_eq_nil_iff, List.filter_eq_nil_iff, List.any_eq_true,
    beq_iff_eq, not_exists, not_and]

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
  have zero := replicate_getD_zero state.validators.data.size
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

/-- The sums of four lists of deltas, read at one index below the size of the first list.

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
