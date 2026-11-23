module

public import EthLib.Consensus.Proofs.Transition.RewardDeltas
public import EthLib.Consensus.Proofs.Transition.BalanceDrift
public import EthLib.Consensus.Proofs.Participation
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.BlockRewards
public import EthLib.Consensus.BeaconApi.Duties
import EthLib.Consensus.Proofs.Transition.EpochParticipation
import EthLib.Consensus.Proofs.Transition.ForkBoundary
import EthLib.Consensus.Proofs.Transition.Slot
import EthLib.Consensus.Proofs.Transition.SyncCommitteeProvenance

/-!
# The reads of one epoch, as natural numbers

The active total, the sync reward and the seats of a validator have values as natural numbers.

From Altair, the rewards pass moves the balance of one validator within an envelope.

The envelope reads only three things before the pass.

They are the effective balances, the balances and the inactivity scores.

Inside one epoch a run keeps its fork and the keys of its current sync committee.

A run that ends in the next epoch splits at the one slot that crosses.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The active effective balances of a state as a natural number, at least one increment.

It sums over the positions of the registry that are active in the current epoch.

It is the value of each successful active-balance read, and says nothing about success. -/
def activeBalanceTotal {fork : Fork} (state : BeaconState preset fork) : ℕ :=
  max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    (∑ i ∈ (Finset.range state.validators.data.size).filter
        (fun i => isActiveAt state (getCurrentEpoch state) i = true),
      ((state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0)

/-- A successful active-balance read is the sum of the effective balances of the active validators.

A total below one increment is read as one increment. -/
theorem getTotalActiveBalance_toNat {fork : Fork} {state : BeaconState preset fork}
    {total : Gwei} (computed : getTotalActiveBalance state = .ok total) :
    total.toNat = activeBalanceTotal state := by
  unfold activeBalanceTotal
  obtain ⟨indices, checked, computed⟩ := bind_ok_iff.mp computed
  obtain ⟨-, lt, rfl⟩ := getTotalBalance_ok_iff.mp computed
  have sum : sumMarked state.validators.data (markIndices state.validators.data.size indices) =
      ∑ i ∈ (Finset.range state.validators.data.size).filter
          (fun i => isActiveAt state (getCurrentEpoch state) i = true),
        ((state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0 := by
    rw [sumMarked_eq_sum, Finset.sum_filter, Finset.sum_eq_multiset_sum, Finset.range_val,
      ← Multiset.coe_range, Multiset.map_coe, Multiset.sum_coe]
    congr 1
    refine List.map_congr_left fun j member => ?_
    have inside := List.mem_range.mp member
    -- The mark of a position is set exactly when the position is active.
    have marked : (indices.any (·.toNat == j)) = isActiveAt state (getCurrentEpoch state) j := by
      rw [Bool.eq_iff_iff, List.any_eq_true, isActiveAt_eq_true_iff]
      constructor
      · rintro ⟨x, member, equal⟩
        have := (mem_iff_of_getActiveValidatorIndicesChecked_ok checked).mp member
        rw [beq_iff_eq] at equal
        rwa [equal] at this
      · rintro ⟨validator, found, active⟩
        have fits := lt_of_getActiveValidatorIndicesChecked_ok checked found active
        have same : j.toUInt64.toNat = j := by
          rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' fits]
        refine ⟨j.toUInt64, (mem_iff_of_getActiveValidatorIndicesChecked_ok checked).mpr
          ⟨validator, by rw [same]; exact found, active⟩, ?_⟩
        rw [beq_iff_eq, same]
    rw [getElem?_markIndices]
    simp only [inside, ↓reduceIte, Option.getD_some, marked]
  rw [← sum, toNat_max, Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' lt]

/-- The participant reward of the sync committee as a natural number, from the active total.

It is the value of each successful read of that reward, and says nothing about success. -/
def syncRewardAt {fork : Fork} (state : BeaconState preset fork) : ℕ :=
  preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat /
      (activeBalanceTotal state).sqrt *
      (activeBalanceTotal state / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) *
    SYNC_REWARD_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat / preset.SLOTS_PER_EPOCH.toNat /
      preset.SYNC_COMMITTEE_SIZE.toNat

/-- A successful read of the participant reward of the sync committee is its natural value. -/
theorem syncParticipantReward_toNat {fork : Fork} {state : BeaconState preset fork}
    {reward : Gwei} (computed : syncParticipantReward state = .ok reward) :
    reward.toNat = syncRewardAt state := by
  obtain ⟨total, perIncrement, totalOk, perOk, perValue, rewardValue⟩ :=
    syncParticipantReward_ok computed
  rw [rewardValue, perValue, getTotalActiveBalance_toNat totalOk]
  rfl

/-- The seats of a validator in the current sync committee: the members that hold its key. -/
def syncSeats {fork : Fork} (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (i : ℕ) : ℕ :=
  ((state.currentSyncCommittee altair).value.pubkeys.toList.filter fun key =>
    (state.validators.data[i]?).any (·.pubkey == key)).length

/-- The entries of a numbered list that hold a value are as many as the matches in the list. -/
private theorem length_filter_zipIdx {α : Type} [BEq α] [LawfulBEq α] (l : List α) (x : α) :
    ((l.zipIdx).filter (·.1 == x)).length = (l.filter (fun k => x == k)).length := by
  have numbered : (l.zipIdx.filter (·.1 == x)).map Prod.fst =
      (l.zipIdx.map Prod.fst).filter (· == x) := by
    rw [List.filter_map]
    rfl
  rw [← List.length_map (f := Prod.fst), numbered, List.zipIdx_map_fst]
  congr 1
  exact List.filter_congr fun k _ => by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    exact ⟨Eq.symm, Eq.symm⟩

/-- The seats of a validator are as many as the seats that the duties of the beacon API list. -/
theorem syncSeats_eq_length {fork : Fork} (state : BeaconState preset fork)
    (altair : .altair ≤ fork) {i : ℕ} {validator : Validator}
    (found : state.validators.data[i]? = some validator) :
    syncSeats state altair i =
      (BeaconApi.syncSeats (state.currentSyncCommittee altair).value validator.pubkey).length := by
  unfold syncSeats BeaconApi.syncSeats
  rw [found, List.length_map, length_filter_zipIdx]
  rfl

/-- Deltas applied in turn to one balance move it up by at most their rewards.

They move it down by at most their penalties.

Each addition of a reward is checked, so none wraps. -/
private theorem foldlM_deltas_bounds {j : Nat} :
    ∀ {deltas : List (Array Gwei × Array Gwei)} {balance result : Gwei},
      deltas.foldlM (fun balance delta => (addChecked balance (delta.1.getD j 0)).map
          fun raised => saturatingSub raised (delta.2.getD j 0)) balance = .ok result →
        result.toNat ≤ balance.toNat + (deltas.map fun delta => (delta.1.getD j 0).toNat).sum ∧
          balance.toNat ≤ result.toNat + (deltas.map fun delta => (delta.2.getD j 0).toNat).sum
  | [], balance, result, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp
  | delta :: rest, balance, result, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨next, stepped, folded⟩ := computed
    obtain ⟨up, down⟩ := foldlM_deltas_bounds folded
    cases added : addChecked balance (delta.1.getD j 0) with
    | error failure =>
      rw [added] at stepped
      cases stepped
    | ok raised =>
      rw [added] at stepped
      simp only [Except.map, Except.ok.injEq] at stepped
      subst stepped
      have sum := (addChecked_ok_iff.mp added).2
      simp only [List.map_cons, List.sum_cons, toNat_saturatingSub] at up down ⊢
      omega

/-- The balance of a set of validators active in the previous epoch, in whole increments.

It is at most the effective balance of all validators active then, in whole increments, and one.

A balance below one increment is read as one increment. -/
private theorem getTotalBalance_increments_le {fork : Fork} {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit)
    {indices : List ValidatorIndex} {balance : Gwei}
    (weighed : getTotalBalance state indices = .ok balance)
    (active : ∀ index ∈ indices, index ∈ getActiveValidatorIndices state (getPreviousEpoch state)) :
    balance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      max 1 ((∑ i ∈ (Finset.range state.validators.data.size).filter
          (fun i => isActiveAt state (getPreviousEpoch state) i = true),
        ((state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0) /
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  obtain ⟨_, small, rfl⟩ := getTotalBalance_ok_iff.mp weighed
  rw [toNat_max, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt small]
  -- Each marked validator is active in the previous epoch.
  have marked : sumMarked state.validators.data
      (markIndices state.validators.data.size indices) ≤
      ∑ i ∈ (Finset.range state.validators.data.size).filter
          (fun i => isActiveAt state (getPreviousEpoch state) i = true),
        ((state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0 := by
    rw [sumMarked_eq_sum, Finset.sum_filter, Finset.sum_eq_multiset_sum, Finset.range_val,
      ← Multiset.coe_range, Multiset.map_coe, Multiset.sum_coe]
    refine sum_map_le_sum_map fun j member => ?_
    have inside := List.mem_range.mp member
    rw [getElem?_markIndices]
    simp only [inside, ↓reduceIte, Option.getD_some]
    split
    · rename_i listed
      obtain ⟨index, member, named⟩ := List.any_eq_true.mp listed
      obtain ⟨validator, found, isActive⟩ :=
        (mem_getActiveValidatorIndices within).mp (active index member)
      rw [beq_iff_eq] at named
      rw [named] at found
      have activeAt : isActiveAt state (getPreviousEpoch state) j = true :=
        isActiveAt_eq_true_iff.mpr ⟨validator, found, isActive⟩
      simp [activeAt]
    · exact Nat.zero_le _
  generalize preset.EFFECTIVE_BALANCE_INCREMENT.toNat = inc at *
  rcases Nat.eq_zero_or_pos inc with zero | positive
  · simp [zero]
  -- One increment counts as one, and a larger balance counts its whole increments.
  have bound : max inc (sumMarked state.validators.data
      (markIndices state.validators.data.size indices)) / inc ≤
      max 1 (sumMarked state.validators.data
        (markIndices state.validators.data.size indices) / inc) := by
    rcases Nat.le_total inc (sumMarked state.validators.data
      (markIndices state.validators.data.size indices)) with le | le
    · rw [Nat.max_eq_right le]
      exact Nat.le_max_right _ _
    · rw [Nat.max_eq_left le, Nat.div_self positive]
      exact Nat.le_max_left _ _
  exact bound.trans (Nat.max_le.mpr ⟨Nat.le_max_left _ _,
    (Nat.div_le_div_right marked).trans (Nat.le_max_right _ _)⟩)

/-- From Altair, the end of an epoch moves the balance of one validator within an envelope.

It gains at most its base reward times 54/64, scaled by the ratio of two balances.

The numerator is the effective balance active in the previous epoch, in increments and at least one.

The denominator is the total active balance, in increments and at least one.

It loses at most its base reward plus its inactivity penalty at its present score.

The base reward is any bound on each successful read of it at the validator.

The total is the active effective balance, at least one increment, as a successful read returns.

That needs a registry within its limit. -/
private theorem processRewardsAndPenalties_balance_le_of_altair
    {fork : Fork} {state : BeaconState preset fork}
    {after : BeaconState preset fork} (altair : .altair ≤ fork) (within : state.RegistryWithinLimit)
    (computed : processRewardsAndPenalties config state = .ok after)
    (j : Nat) (inside : j < state.validators.data.size)
    {base : ℕ} (based : ∀ total reward, getTotalActiveBalance state = .ok total →
      getBaseReward state total j.toUInt64 = .ok reward → reward.toNat ≤ base) :
    let inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    let effective (i : Nat) := ((state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0
    let total := max inc (∑ i ∈ (Finset.range state.validators.data.size).filter
      (fun i => isActiveAt state (getCurrentEpoch state) i = true), effective i)
    let num := max 1 ((∑ i ∈ (Finset.range state.validators.data.size).filter
      (fun i => isActiveAt state (getPreviousEpoch state) i = true), effective i) / inc)
    let den := max 1 (total / inc)
    let score := (((state.inactivityScores altair).data[j]?).map (·.toNat)).getD 0
    ((after.balances.data[j]?).map (·.toNat)).getD 0 ≤
        ((state.balances.data[j]?).map (·.toNat)).getD 0 +
          base * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum * num /
            (WEIGHT_DENOMINATOR.toNat * den) ∧
      ((state.balances.data[j]?).map (·.toNat)).getD 0 ≤
        ((after.balances.data[j]?).map (·.toNat)).getD 0 + base + effective j * score /
          (config.INACTIVITY_SCORE_BIAS.toNat *
            (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) := by
  intro inc effective total num den score
  by_cases genesis : getCurrentEpoch state = GENESIS_EPOCH
  · rw [processRewardsAndPenalties_genesis config genesis] at computed
    cases computed
    exact ⟨Nat.le_add_right _ _, (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)⟩
  obtain ⟨flagDeltas, inactivityDeltas, flagged, penalized, balances⟩ :=
    processRewardsAndPenalties_balances_of_altair altair genesis computed
  have finRange : List.finRange PARTICIPATION_FLAG_WEIGHTS.length =
      [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩] := rfl
  rw [finRange] at flagged
  simp only [List.mapM_cons, List.mapM_nil, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at flagged
  obtain ⟨⟨sourceRewards, sourcePenalties⟩, sourceOk, _, ⟨⟨targetRewards, targetPenalties⟩,
    targetOk, _, ⟨⟨headRewards, headPenalties⟩, headOk, _, rfl, rfl⟩, rfl⟩, rfl⟩ := flagged
  obtain ⟨inactivityRewards, inactivityPenalties⟩ := inactivityDeltas
  -- A missing balance stays missing, and both sides read zero.
  rcases found : state.balances.data[j]? with _ | balance
  · rw [(balances j).1 inside, found]
    simp
  have fits := (balances j).2.1 inside balance found
  rw [(balances j).1 inside, found]
  obtain ⟨up, down⟩ := foldlM_deltas_bounds fits
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero, getInactivityPenaltyDeltas_rewards penalized,
    UInt64.toNat_zero] at up down
  simp only [Option.map_some, Option.getD_some, List.cons_append, List.nil_append]
  -- The reads of the deltas: the participants, the total and the base reward.
  obtain ⟨source, sourceBalance, total', sourceOk', sourceWeighed, totalOk, sourceFacts⟩ :=
    getFlagIndexDeltas_getD within sourceOk
  obtain ⟨target, targetBalance, total'', targetOk', targetWeighed, totalOk', targetFacts⟩ :=
    getFlagIndexDeltas_getD within targetOk
  obtain ⟨head, headBalance, total''', headOk', headWeighed, totalOk'', headFacts⟩ :=
    getFlagIndexDeltas_getD within headOk
  obtain rfl : total' = total'' := Except.ok.inj (totalOk.symm.trans totalOk')
  obtain rfl : total' = total''' := Except.ok.inj (totalOk.symm.trans totalOk'')
  have totalValue : total'.toNat = total := getTotalActiveBalance_toNat totalOk
  -- A base reward at the validator is at most `base`, as the premise says.
  have baseBound {base' : Gwei} (read : getBaseReward state total' j.toUInt64 = .ok base') :
      base'.toNat ≤ base :=
    based total' base' totalOk read
  -- Each participant set lies in the previous epoch, so it weighs at most the numerator.
  have numerator {flag : Fin PARTICIPATION_FLAG_WEIGHTS.length} {participants : List ValidatorIndex}
      {weight : Gwei}
      (listed : getUnslashedParticipatingIndices state altair flag.val.toUInt64
        (getPreviousEpoch state) = .ok participants)
      (weighed : getTotalBalance state participants = .ok weight) :
      weight.toNat / inc ≤ num :=
    getTotalBalance_increments_le within weighed fun index member =>
      (mem_getUnslashedParticipatingIndices listed index member).1
  -- One flag earns at most its weight of the base reward, scaled by the two balances.
  have flagReward {flag : Fin PARTICIPATION_FLAG_WEIGHTS.length}
      {participants : List ValidatorIndex}
      {weight : Gwei} {reward : Nat}
      (listed : getUnslashedParticipatingIndices state altair flag.val.toUInt64
        (getPreviousEpoch state) = .ok participants)
      (weighed : getTotalBalance state participants = .ok weight)
      {base' : Gwei} (based : getBaseReward state total' j.toUInt64 = .ok base') {leak : Bool}
      (value : reward = if leak then 0 else
        base'.toNat * PARTICIPATION_FLAG_WEIGHTS[flag].toNat * (weight.toNat / inc) /
          (total'.toNat / inc * WEIGHT_DENOMINATOR.toNat)) :
      reward * (WEIGHT_DENOMINATOR.toNat * den) ≤
        PARTICIPATION_FLAG_WEIGHTS[flag].toNat * (base * num) := by
    subst value
    rw [totalValue]
    split
    · simp
    rcases Nat.eq_zero_or_pos (total / inc) with zero | positive
    · simp [zero]
    have same : den = total / inc := Nat.max_eq_right positive
    rw [same, Nat.mul_comm WEIGHT_DENOMINATOR.toNat]
    refine (Nat.div_mul_le_self _ _).trans ?_
    calc base'.toNat * PARTICIPATION_FLAG_WEIGHTS[flag].toNat * (weight.toNat / inc)
        ≤ base * PARTICIPATION_FLAG_WEIGHTS[flag].toNat * num :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ (baseBound based)) (numerator listed weighed)
      _ = PARTICIPATION_FLAG_WEIGHTS[flag].toNat * (base * num) := by ac_rfl
  -- The reward of one flag at the validator.
  have flagUp {flag : Fin PARTICIPATION_FLAG_WEIGHTS.length} {rewards penalties : Array Gwei}
      {participants : List ValidatorIndex} {weight : Gwei}
      (listed : getUnslashedParticipatingIndices state altair flag.val.toUInt64
        (getPreviousEpoch state) = .ok participants)
      (weighed : getTotalBalance state participants = .ok weight)
      (facts : ∀ j (inside : j < state.validators.data.size), ∃ eligible,
        isEligibleValidator (getPreviousEpoch state) state.validators.data[j] = .ok eligible ∧
        (eligible = false → rewards.getD j 0 = 0 ∧ penalties.getD j 0 = 0) ∧
        (eligible = true → ∃ base, getBaseReward state total' j.toUInt64 = .ok base ∧
          (j.toUInt64 ∈ participants → ∃ leak, isInInactivityLeak state = .ok leak ∧
            (rewards.getD j 0).toNat = (if leak then 0 else
              base.toNat * PARTICIPATION_FLAG_WEIGHTS[flag].toNat *
                (weight.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) /
                (total'.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
                  WEIGHT_DENOMINATOR.toNat)) ∧
            penalties.getD j 0 = 0) ∧
          (j.toUInt64 ∉ participants → rewards.getD j 0 = 0 ∧
            (penalties.getD j 0).toNat = (if flag.val.toUInt64 = TIMELY_HEAD_FLAG_INDEX then 0
              else base.toNat * PARTICIPATION_FLAG_WEIGHTS[flag].toNat /
                WEIGHT_DENOMINATOR.toNat)))) :
      (rewards.getD j 0).toNat * (WEIGHT_DENOMINATOR.toNat * den) ≤
          PARTICIPATION_FLAG_WEIGHTS[flag].toNat * (base * num) := by
    obtain ⟨eligible, -, no, yes⟩ := facts j inside
    cases eligible with
    | false => simp [(no rfl).1]
    | true =>
      obtain ⟨base', based, present, absent⟩ := yes rfl
      by_cases member : j.toUInt64 ∈ participants
      · obtain ⟨leak, -, reward, -⟩ := present member
        exact flagReward listed weighed based reward
      · simp [(absent member).1]
  have sourceUp := flagUp sourceOk' sourceWeighed sourceFacts
  have targetUp := flagUp targetOk' targetWeighed targetFacts
  have headUp := flagUp headOk' headWeighed headFacts
  have weights : (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum = 54 := by decide
  have w0 : (PARTICIPATION_FLAG_WEIGHTS[(⟨0, by decide⟩ :
      Fin PARTICIPATION_FLAG_WEIGHTS.length)]).toNat = 14 := rfl
  have w1 : (PARTICIPATION_FLAG_WEIGHTS[(⟨1, by decide⟩ :
      Fin PARTICIPATION_FLAG_WEIGHTS.length)]).toNat = 26 := rfl
  have w2 : (PARTICIPATION_FLAG_WEIGHTS[(⟨2, by decide⟩ :
      Fin PARTICIPATION_FLAG_WEIGHTS.length)]).toNat = 14 := rfl
  have denominator : WEIGHT_DENOMINATOR.toNat = 64 := by decide
  simp only [w0, denominator] at sourceUp
  simp only [w1, denominator] at targetUp
  simp only [w2, denominator] at headUp
  -- The four penalties are at most 40/64 of a base reward and the inactivity penalty.
  have penalties : (sourcePenalties.getD j 0).toNat + (targetPenalties.getD j 0).toNat +
      (headPenalties.getD j 0).toNat + (inactivityPenalties.getD j 0).toNat ≤
      base + effective j * score /
        (config.INACTIVITY_SCORE_BIAS.toNat *
          (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) := by
    rcases penaltyEntries_le (config := config) altair within totalOk sourceOk targetOk headOk
      penalized inside with zero | ⟨base', -, based, bound⟩
    · simp only at zero
      have := Nat.zero_le (effective j * score / (config.INACTIVITY_SCORE_BIAS.toNat *
        (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat))
      omega
    · simp only at bound
      have weightSum : TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat = 40 := by decide
      rw [weightSum, denominator] at bound
      have read : effective j = state.validators.data[j].effectiveBalance.toNat := by
        simp [effective, Array.getElem?_eq_getElem inside]
      have scoreRead : (((state.inactivityScores altair).data[j]?.map UInt64.toNat).getD 0) =
          score := rfl
      rw [scoreRead, ← read] at bound
      have := baseBound based
      have : base'.toNat * 40 / 64 ≤ base := by omega
      omega
  rw [weights, denominator]
  have positive : 0 < 64 * den := Nat.mul_pos (by decide) (Nat.lt_of_lt_of_le Nat.one_pos
    (Nat.le_max_left _ _))
  constructor
  · -- The three flag rewards, in units of the common divisor, add up to the weight sum.
    have sum : ((sourceRewards.getD j 0).toNat + (targetRewards.getD j 0).toNat +
        (headRewards.getD j 0).toNat) * (64 * den) ≤ base * 54 * num := by
      rw [Nat.add_mul, Nat.add_mul, Nat.mul_right_comm, Nat.mul_comm (base * num)]
      generalize base * num = scale at *
      omega
    have := (Nat.le_div_iff_mul_le positive).mpr sum
    omega
  · omega

/-- From Altair, take the rewards pass after the update of the inactivity scores.

It moves one balance within the same envelope, read before that update.

The update keeps the registry, the balances and the slot.

It raises the score of the validator by at most the score bias.

So the inactivity penalty reads the score before the update plus that bias.

The base reward is any bound on each successful read of it at the validator, before the update. -/
theorem processRewardsAndPenalties_balance_le_of_inactivityUpdates
    {fork : Fork}
    {state scored after : BeaconState preset fork} (altair : .altair ≤ fork)
    (within : state.RegistryWithinLimit)
    (updated : processInactivityUpdates config state altair = .ok scored)
    (computed : processRewardsAndPenalties config scored = .ok after)
    (j : Nat) (inside : j < state.validators.data.size)
    {base : ℕ} (based : ∀ total reward, getTotalActiveBalance state = .ok total →
      getBaseReward state total j.toUInt64 = .ok reward → reward.toNat ≤ base) :
    let inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    let effective (i : Nat) := ((state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0
    let total := max inc (∑ i ∈ (Finset.range state.validators.data.size).filter
      (fun i => isActiveAt state (getCurrentEpoch state) i = true), effective i)
    let num := max 1 ((∑ i ∈ (Finset.range state.validators.data.size).filter
      (fun i => isActiveAt state (getPreviousEpoch state) i = true), effective i) / inc)
    let den := max 1 (total / inc)
    let score := (((state.inactivityScores altair).data[j]?).map (·.toNat)).getD 0
    ((after.balances.data[j]?).map (·.toNat)).getD 0 ≤
        ((state.balances.data[j]?).map (·.toNat)).getD 0 +
          base * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum * num /
            (WEIGHT_DENOMINATOR.toNat * den) ∧
      ((state.balances.data[j]?).map (·.toNat)).getD 0 ≤
        ((after.balances.data[j]?).map (·.toNat)).getD 0 + base +
          effective j * (score + config.INACTIVITY_SCORE_BIAS.toNat) /
            (config.INACTIVITY_SCORE_BIAS.toNat *
              (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) := by
  dsimp only
  have frame := processInactivityUpdates_frame updated
  have validators : scored.validators = state.validators := by rw [frame]
  have balances : scored.balances = state.balances := by rw [frame]
  have current : getCurrentEpoch scored = getCurrentEpoch state := by
    simp only [getCurrentEpoch, show scored.slot = state.slot by rw [frame]]
  have previous : getPreviousEpoch scored = getPreviousEpoch state := by
    unfold getPreviousEpoch
    rw [current]
  have active (epoch : Epoch) (i : Nat) : isActiveAt scored epoch i = isActiveAt state epoch i := by
    simp only [isActiveAt, validators]
  -- The update raises the score of the validator by at most the bias.
  have raised : (((scored.inactivityScores altair).data[j]?).map (·.toNat)).getD 0 ≤
      (((state.inactivityScores altair).data[j]?).map (·.toNat)).getD 0 +
        config.INACTIVITY_SCORE_BIAS.toNat := by
    by_cases genesis : getCurrentEpoch state = GENESIS_EPOCH
    · unfold processInactivityUpdates at updated
      simp only [genesis, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at updated
      subst updated
      exact Nat.le_add_right _ _
    obtain ⟨eligible, -, unlisted, listed⟩ := processInactivityUpdates_scores genesis updated
    by_cases named : ∃ index ∈ eligible, index.toNat = j
    · obtain ⟨index, member, rfl⟩ := named
      obtain ⟨hitters, leak, score, score', -, -, before, after, value⟩ := listed index member
      rw [before, after]
      simp only [Option.map_some, Option.getD_some]
      split at value <;> split at value <;> omega
    · rw [unlisted j fun index member same => named ⟨index, member, same⟩]
      exact Nat.le_add_right _ _
  have within' : scored.RegistryWithinLimit := by
    unfold BeaconState.RegistryWithinLimit
    rw [validators]
    exact within
  -- The update keeps the registry and the slot, so the reads of the base reward stay.
  have totalSame : getTotalActiveBalance scored = getTotalActiveBalance state := by
    unfold getTotalActiveBalance getActiveValidatorIndicesChecked getTotalBalance
    simp only [current, validators]
  have baseSame (t : Gwei) :
      getBaseReward scored t j.toUInt64 = getBaseReward state t j.toUInt64 := by
    unfold getBaseReward getValidator
    simp only [validators]
  have core := processRewardsAndPenalties_balance_le_of_altair altair within' computed j
    (by rw [validators]; exact inside) (base := base) fun t reward totalOk read =>
      based t reward (totalSame ▸ totalOk) (baseSame t ▸ read)
  dsimp only at core
  simp only [active, current, previous, validators, balances] at core
  obtain ⟨up, down⟩ := core
  exact ⟨up, down.trans (Nat.add_le_add_left (Nat.div_le_div_right
    (Nat.mul_le_mul_left _ raised)) _)⟩

/-- Take a run that ends one epoch after it starts.

It stays in its first epoch up to one slot, and in the next epoch after that slot. -/
theorem Run.split_next {x y : ForkedBeaconState preset} (run : Run config checks x y)
    (next : (getCurrentEpoch y.state).toNat = (getCurrentEpoch x.state).toNat + 1) :
    ∃ (z z' : ForkedBeaconState preset) (_ : Run config checks x z)
      (_ : advanceSlotAcross config checks z = .ok z') (_ : Run config checks z' y),
      getCurrentEpoch z.state = getCurrentEpoch x.state ∧
      getCurrentEpoch z'.state = getCurrentEpoch y.state := by
  obtain ⟨z, z', pre, slot, post, -, first, second⟩ :=
    run.cross_split (getCurrentEpoch x.state).toNat (Nat.le_refl _) (by omega)
  exact ⟨z, z', pre, slot, post, UInt64.toNat_inj.mp first,
    UInt64.toNat_inj.mp (second.trans next.symm)⟩

/-- A run inside one epoch keeps its fork.

No upgrade comes before the first slot of an epoch. -/
theorem Run.fork_eq_of_same_epoch {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (same : getCurrentEpoch y.state = getCurrentEpoch x.state) :
    y.fork = x.fork := by
  induction tail with
  | nil => rfl
  | @snoc middle last pre step ih =>
    have low := currentEpoch_le_of_chainSteps pre.chainSteps
    have high := step.chainStep.currentEpoch_le
    have midEpoch : getCurrentEpoch middle.state = getCurrentEpoch x.state :=
      UInt64.le_antisymm (same ▸ high) low
    have prior := ih midEpoch
    cases step with
    | block engine signed due ok => exact prior
    | slot ok =>
      obtain ⟨cached, next, -, rfl⟩ := advanceSlotAcross_of_same_epoch ok (same.trans midEpoch.symm)
      exact prior

/-- Inside one epoch, from Altair, the keys of the current sync committee stay.

Blocks keep the committee, and slots inside the epoch only cache the slot. -/
theorem Run.currentSyncCommittee_eq_of_same_epoch {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (same : getCurrentEpoch y.state = getCurrentEpoch x.state)
    (altair : .altair ≤ y.fork) (altair' : .altair ≤ x.fork) :
    (y.state.currentSyncCommittee altair).value.pubkeys.toList =
      (x.state.currentSyncCommittee altair').value.pubkeys.toList :=
  tail.currentSyncCommittee_eq_of_same_period (by rw [same]) altair altair'

/-- The positions active in an epoch are the same in two registries when activity stays.

The later registry keeps the positions of the earlier one.

A position past them is inactive in both. -/
theorem activeFilter_eq {f g : Fork} {a : BeaconState preset f}
    {b : BeaconState preset g} {ep : Epoch} (active : ∀ i, isActiveAt b ep i = isActiveAt a ep i)
    (grows : a.validators.data.size ≤ b.validators.data.size) :
    (Finset.range b.validators.data.size).filter (fun i => isActiveAt b ep i = true) =
      (Finset.range a.validators.data.size).filter (fun i => isActiveAt a ep i = true) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, active]
  constructor
  · rintro ⟨-, hit⟩
    obtain ⟨v, found, -⟩ := isActiveAt_eq_true_iff.mp hit
    exact ⟨(Array.getElem?_eq_some_iff.mp found).1, hit⟩
  · rintro ⟨inside, hit⟩
    exact ⟨Nat.lt_of_lt_of_le inside grows, hit⟩

/-- The effective balances active in an epoch sum the same when three things stay.

These are activity in that epoch, the effective balances and the registry before. -/
theorem activeSum_eq {f h : Fork} {a : BeaconState preset f} {b : BeaconState preset h}
    {e : Epoch} (active : ∀ i, isActiveAt b e i = isActiveAt a e i) (kept : EffectiveKept a b)
    (grows : a.validators.data.size ≤ b.validators.data.size) :
    ∑ i ∈ (Finset.range b.validators.data.size).filter (fun i => isActiveAt b e i = true),
        ((b.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0 =
      ∑ i ∈ (Finset.range a.validators.data.size).filter (fun i => isActiveAt a e i = true),
        ((a.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0 := by
  rw [activeFilter_eq active grows]
  refine Finset.sum_congr rfl fun i member => ?_
  exact kept i (Finset.mem_range.mp (Finset.mem_filter.mp member).1)

/-- Take two states with the same keys of the current sync committee.

They also hold the same key at the position of a validator.

Then the seats of that validator read the same from both states. -/
theorem seats_eq {f h : Fork} {a : BeaconState preset f} {b : BeaconState preset h}
    (altairA : .altair ≤ f) (altairB : .altair ≤ h) {i : ℕ}
    (keys : (a.currentSyncCommittee altairA).value.pubkeys.toList =
      (b.currentSyncCommittee altairB).value.pubkeys.toList)
    (pub : (a.validators.data[i]?).map (·.pubkey) = (b.validators.data[i]?).map (·.pubkey)) :
    syncSeats a altairA i = syncSeats b altairB i := by
  unfold syncSeats
  have any : ∀ (o : Option Validator) (key : Cryptography.Bls.BLSPubkey),
      o.any (·.pubkey == key) = (o.map (·.pubkey)).any (· == key) := by
    intro o key
    cases o <;> rfl
  rw [keys]
  congr 1
  refine List.filter_congr fun key _ => ?_
  rw [any, any, pub]

end EthLib.Consensus
