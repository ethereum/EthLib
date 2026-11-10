module

public import EthLib.Base.Proofs.FoldlM
public import EthLib.Consensus.Proofs.Transition.EpochRewards
public import EthLib.Consensus.Proofs.Transition.Totality.Inactivity
public import Mathlib.Data.Nat.Sqrt

/-!
# Proofs: the rewards and penalties succeed from Altair

From Altair the step computes the deltas of each participation flag, then those of inactivity.

It then applies each list of deltas to the balances in turn.

Its checked operations are products, sums and divisions of 64-bit integers.

A base reward is the whole increments of an effective balance times the reward of one increment.

That reward is a fixed factor of the increment over the square root of the total active balance.

The total is at least one increment, so the reward of one increment is at most its value there.

The reward of a flag multiplies the base reward by the weight of the flag.

It also multiplies by the increments that set the flag, which the budget bounds.

These increments are those of the previous epoch, while the total is that of the current epoch.

So the first can exceed the second, and the bound does not use the square root of the total.

The inactivity penalty multiplies the effective balance by the inactivity score.

So the scores must stay small, which bounds the epochs of a run.

Each delta is added once to a zero entry, since each eligible index comes once.

A balance rises by at most the rewards of the three flags, which the budget must leave room for.

The bounds on the presets and configurations are named here, with mainnet and minimal as cases.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

/-- The largest cap on an effective balance, at any fork and for any credentials. -/
def Preset.largestEffectiveBalance (preset : Preset) : Nat :=
  max preset.MAX_EFFECTIVE_BALANCE.toNat
    (max preset.MIN_ACTIVATION_BALANCE.toNat preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat)

/-- The cap on the effective balance of a validator is at most the largest cap. -/
theorem withdrawalMaxEffectiveBalance_le_largestEffectiveBalance (preset : Preset)
    (fork : Base.Fork) (validator : Validator) :
    (withdrawalMaxEffectiveBalance preset fork validator).toNat ≤
      preset.largestEffectiveBalance := by
  unfold withdrawalMaxEffectiveBalance getMaxEffectiveBalance Preset.largestEffectiveBalance
  split
  · split <;> omega
  · omega

/-- From Altair, a bound on the base reward of a validator.

It counts the whole increments of the largest cap.

Each of them earns the reward of one increment at the smallest total active balance.

That total is one increment. -/
def Preset.baseRewardCeiling (preset : Preset) : Nat :=
  preset.largestEffectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
    (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat /
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat.sqrt)

/-- The whole increments of a budget, or of one increment if the budget is smaller.

A total balance of the step is at most one increment or the budget, so it has at most these. -/
def Preset.budgetIncrements (preset : Preset) (budget : Nat) : Nat :=
  max preset.EFFECTIVE_BALANCE_INCREMENT.toNat budget / preset.EFFECTIVE_BALANCE_INCREMENT.toNat

/-- From Altair, the bounds under which the rewards and penalties fit in 64 bits.

The budget bounds the balances and the sum of the effective balances.

The score bound bounds the inactivity scores.

The increment times the base reward factor must fit.

So must the increments of the budget times the weight denominator, 64.

The base reward bound times the weight of a flag times the increments of the budget must fit.

A balance of the budget plus the rewards of the three flags must fit.

Those rewards are at most that product summed over the weights, divided by 64.

The largest cap times the score bound must fit.

So must the score bias times the inactivity penalty quotient of each fork. -/
structure RewardsFit (preset : Preset) (config : Config) (budget scoreBound : Nat) : Prop where
  perIncrement :
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64
  activeIncrements : preset.budgetIncrements budget * WEIGHT_DENOMINATOR.toNat < 2 ^ 64
  flagNumerator : ∀ weight ∈ PARTICIPATION_FLAG_WEIGHTS,
    preset.baseRewardCeiling * weight.toNat * preset.budgetIncrements budget < 2 ^ 64
  flagRewards : budget + preset.baseRewardCeiling *
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum * preset.budgetIncrements budget /
        WEIGHT_DENOMINATOR.toNat < 2 ^ 64
  scorePenalty : preset.largestEffectiveBalance * scoreBound < 2 ^ 64
  penaltyQuotient : ∀ fork : Base.Fork, config.INACTIVITY_SCORE_BIAS.toNat *
    (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat < 2 ^ 64

/-- Under the bounds, the budget is below 2^64. -/
theorem RewardsFit.budget_lt {preset : Preset} {config : Config} {budget scoreBound : Nat}
    (fit : RewardsFit preset config budget scoreBound) : budget < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.le_add_right _ _) fit.flagRewards

/-- The rewards of mainnet fit under a budget of 2^57 Gwei and scores up to 2^23.

That budget is about 1.44 * 10^8 ETH.

The score bound is the score bias times 2^21 epochs. -/
theorem rewardsFit_mainnet : RewardsFit Preset.mainnet Config.mainnet (2 ^ 57) (2 ^ 23) := by
  have root : (Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT.toNat).sqrt = 31622 :=
    (Nat.eq_sqrt.mpr ⟨by decide, by decide⟩).symm
  constructor
  · decide
  · decide
  · intro weight member
    simp only [PARTICIPATION_FLAG_WEIGHTS, List.mem_cons, List.not_mem_nil, or_false] at member
    simp only [Preset.baseRewardCeiling, root]
    rcases member with rfl | rfl | rfl <;> decide
  · simp only [Preset.baseRewardCeiling, root]
    decide
  · decide
  · intro fork
    simp only [parameters]
    split_ifs <;> decide

/-- The rewards of minimal fit under a budget of 2^57 Gwei and scores up to 2^23. -/
theorem rewardsFit_minimal : RewardsFit Preset.minimal Config.minimal (2 ^ 57) (2 ^ 23) := by
  have root : (Preset.minimal.EFFECTIVE_BALANCE_INCREMENT.toNat).sqrt = 31622 :=
    (Nat.eq_sqrt.mpr ⟨by decide, by decide⟩).symm
  constructor
  · decide
  · decide
  · intro weight member
    simp only [PARTICIPATION_FLAG_WEIGHTS, List.mem_cons, List.not_mem_nil, or_false] at member
    simp only [Preset.baseRewardCeiling, root]
    rcases member with rfl | rfl | rfl <;> decide
  · simp only [Preset.baseRewardCeiling, root]
    decide
  · decide
  · intro fork
    simp only [parameters]
    split_ifs <;> decide

variable {preset : Preset} {fork : Base.Fork} {state : BeaconState preset fork}

/-- The reward of one increment succeeds when the total is at least one positive increment.

It is then at most its value at a total of one increment. -/
private theorem getBaseRewardPerIncrement_le (positive : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0)
    (fits : preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64)
    {total : Gwei} (low : preset.EFFECTIVE_BALANCE_INCREMENT ≤ total) :
    ∃ per, getBaseRewardPerIncrement preset total = .ok per ∧
      per.toNat ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat /
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat.sqrt := by
  have incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    Nat.pos_of_ne_zero fun zero => positive (UInt64.toNat_inj.mp (by simpa using zero))
  have lowNat := UInt64.le_iff_toNat_le.mp low
  have root := toNat_integerSquareroot total
  have rootLow := Nat.sqrt_le_sqrt lowNat
  have rootPos := Nat.sqrt_pos.mpr incPos
  have nonzero : integerSquareroot total ≠ 0 := fun zero => by
    rw [zero, UInt64.toNat_zero] at root
    omega
  refine ⟨preset.EFFECTIVE_BALANCE_INCREMENT * preset.BASE_REWARD_FACTOR /
    integerSquareroot total, ?_, ?_⟩
  · simp only [getBaseRewardPerIncrement, liftArith, mulChecked_of_lt fits, bind, Except.bind,
      divChecked, nonzero, ite_false, Except.mapError]
  · rw [UInt64.toNat_div, UInt64.toNat_mul, Nat.mod_eq_of_lt fits, root]
    exact Nat.div_le_div_left rootLow rootPos

/-- From Altair, the base reward of a validator under the largest cap succeeds.

The reward of one increment must be at most its value at a total of one increment.

The bound on the base reward must fit in 64 bits, and the reward is then at most that bound. -/
private theorem getBaseReward_le (altair : .altair ≤ fork) {total per : Gwei}
    (perOk : getBaseRewardPerIncrement preset total = .ok per)
    (perLe : per.toNat ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      preset.BASE_REWARD_FACTOR.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat.sqrt)
    (fits : preset.baseRewardCeiling < 2 ^ 64) {index : ValidatorIndex} {validator : Validator}
    (found : state.validators.data[index.toNat]? = some validator)
    (capped : validator.effectiveBalance.toNat ≤ preset.largestEffectiveBalance) :
    ∃ base, getBaseReward state total index = .ok base ∧
      base.toNat ≤ preset.baseRewardCeiling := by
  have bound : (validator.effectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT).toNat *
      per.toNat ≤ preset.baseRewardCeiling := by
    rw [UInt64.toNat_div]
    exact Nat.mul_le_mul (Nat.div_le_div_right capped) perLe
  refine ⟨validator.effectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT * per, ?_, ?_⟩
  · simp only [getBaseReward, getValidator, found, altair, ↓reduceIte, perOk, liftArith,
      mulChecked_of_lt (Nat.lt_of_le_of_lt bound fits), bind, Except.bind, Except.mapError]
  · rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt bound fits)]
    exact bound

/-- Adding an amount to the deltas succeeds when the index is inside and the sum fits. -/
theorem addDelta_exists_ok {deltas : Array Gwei} {index : ValidatorIndex}
    {amount : Gwei} (inside : index.toNat < deltas.size)
    (fits : (deltas.getD index.toNat 0).toNat + amount.toNat < 2 ^ 64) :
    ∃ result, addDelta deltas index amount = .ok result := by
  have entry : deltas.getD index.toNat 0 = deltas[index.toNat] := by
    simp [Array.getD_eq_getD_getElem?, inside]
  rw [entry] at fits
  refine ⟨deltas.set index.toNat (deltas[index.toNat] + amount) inside, ?_⟩
  simp only [addDelta, inside, ↓reduceDIte, liftAccessor, liftArith, addChecked_of_lt fits,
    Except.mapError, bind, Except.bind, pure, Except.pure]

/-- Adding an amount to a zero entry of the deltas succeeds. -/
theorem addDelta_exists_ok_of_zero {deltas : Array Gwei} {index : ValidatorIndex}
    (amount : Gwei) (inside : index.toNat < deltas.size)
    (zero : deltas.getD index.toNat 0 = 0) :
    ∃ result, addDelta deltas index amount = .ok result :=
  addDelta_exists_ok inside (by rw [zero, UInt64.toNat_zero, Nat.zero_add]; exact amount.toNat_lt)

/-- One step of the deltas of a flag succeeds at an index whose two entries are zero.

It keeps the sizes of the two arrays.

The base reward and the test for a leak must succeed.

The base reward times the weight, and that times the participating increments, must fit.

The active increments times the weight denominator must fit and be positive. -/
private theorem addFlagDelta_exists_ok {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length}
    {participated : Array Bool} {total participatingIncrements activeIncrements : Gwei}
    {leak : Bool} (leaking : isInInactivityLeak state = .ok leak)
    (active : activeIncrements.toNat * WEIGHT_DENOMINATOR.toNat < 2 ^ 64)
    (activePos : 0 < activeIncrements.toNat)
    {rewards penalties : Array Gwei} {index : ValidatorIndex} {base : Gwei}
    (based : getBaseReward state total index = .ok base)
    (weighted : base.toNat * PARTICIPATION_FLAG_WEIGHTS[flagIndex].toNat < 2 ^ 64)
    (fits : base.toNat * PARTICIPATION_FLAG_WEIGHTS[flagIndex].toNat *
      participatingIncrements.toNat < 2 ^ 64)
    (insideRewards : index.toNat < rewards.size) (insidePenalties : index.toNat < penalties.size)
    (zeroRewards : rewards.getD index.toNat 0 = 0)
    (zeroPenalties : penalties.getD index.toNat 0 = 0) :
    ∃ next, addFlagDelta state flagIndex participated total participatingIncrements
      activeIncrements (rewards, penalties) index = .ok next ∧
        next.1.size = rewards.size ∧ next.2.size = penalties.size := by
  have weightOk := mulChecked_of_lt weighted
  have product : (base * PARTICIPATION_FLAG_WEIGHTS[flagIndex]).toNat *
      participatingIncrements.toNat < 2 ^ 64 := by
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt weighted]
    exact fits
  have numeratorOk := mulChecked_of_lt product
  have denominatorOk := mulChecked_of_lt active
  have nonzero : activeIncrements * WEIGHT_DENOMINATOR ≠ 0 := fun zero => by
    have := congrArg UInt64.toNat zero
    have denominator : WEIGHT_DENOMINATOR.toNat = 64 := rfl
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt active, UInt64.toNat_zero, denominator] at this
    omega
  obtain ⟨penalized, penalizedOk⟩ := addDelta_exists_ok_of_zero
    (base * PARTICIPATION_FLAG_WEIGHTS[flagIndex] / WEIGHT_DENOMINATOR) insidePenalties
    zeroPenalties
  obtain ⟨rewarded, rewardedOk⟩ := addDelta_exists_ok_of_zero
    (base * PARTICIPATION_FLAG_WEIGHTS[flagIndex] * participatingIncrements /
      (activeIncrements * WEIGHT_DENOMINATOR)) insideRewards zeroRewards
  simp only [addFlagDelta, based, leaking, liftAccessor, liftArith, weightOk, numeratorOk,
    denominatorOk, divChecked, nonzero, ite_false, Except.mapError, bind, Except.bind,
    rewardedOk, penalizedOk]
  split
  · split
    · exact ⟨_, rfl, rfl, rfl⟩
    · exact ⟨_, rfl, addDelta_size rewardedOk, rfl⟩
  · split
    · exact ⟨_, rfl, rfl, rfl⟩
    · exact ⟨_, rfl, rfl, addDelta_size penalizedOk⟩

/-- A product of two positive 64-bit integers that fits is not zero. -/
private theorem mul_ne_zero_of_lt {a b : UInt64} (left : a ≠ 0) (right : b ≠ 0)
    (fits : a.toNat * b.toNat < 2 ^ 64) : a * b ≠ 0 := fun zero => by
  have := congrArg UInt64.toNat zero
  rw [UInt64.toNat_mul, Nat.mod_eq_of_lt fits, UInt64.toNat_zero] at this
  rcases Nat.mul_eq_zero.mp this with first | second
  · exact left (UInt64.toNat_inj.mp (by simpa using first))
  · exact right (UInt64.toNat_inj.mp (by simpa using second))

/-- From Altair, one step of the inactivity penalties succeeds at an index with a zero entry.

The validator and its score must be in range, and the score must be at most a bound.

The largest cap times that bound must fit.

The score bias times the quotient must fit, and both must be positive.

It keeps the size of the penalties. -/
private theorem addInactivityScorePenalty_exists_ok {config : Config} (altair : .altair ≤ fork)
    {targetMatched : Array Bool} {penalties : Array Gwei} {index : ValidatorIndex}
    {validator : Validator} {score : UInt64} {scoreBound : Nat}
    (found : state.validators.data[index.toNat]? = some validator)
    (capped : validator.effectiveBalance.toNat ≤ preset.largestEffectiveBalance)
    (read : (state.inactivityScores altair).data[index.toNat]? = some score)
    (scored : score.toNat ≤ scoreBound)
    (fits : preset.largestEffectiveBalance * scoreBound < 2 ^ 64)
    (quotient : config.INACTIVITY_SCORE_BIAS.toNat *
      (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat < 2 ^ 64)
    (biased : config.INACTIVITY_SCORE_BIAS ≠ 0)
    (positive : (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT ≠ 0)
    (inside : index.toNat < penalties.size) (zero : penalties.getD index.toNat 0 = 0) :
    ∃ next, addInactivityScorePenalty config state altair targetMatched penalties index =
      .ok next ∧ next.size = penalties.size := by
  have product : validator.effectiveBalance.toNat * score.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul capped scored) fits
  have nonzero := mul_ne_zero_of_lt biased positive quotient
  obtain ⟨penalized, penalizedOk⟩ := addDelta_exists_ok_of_zero
    (validator.effectiveBalance * score /
      (config.INACTIVITY_SCORE_BIAS * (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT))
    inside zero
  unfold addInactivityScorePenalty
  split
  · exact ⟨_, rfl, rfl⟩
  · simp only [getValidator, found, read, liftAccessor, liftArith, mulChecked_of_lt product,
      mulChecked_of_lt quotient, divChecked, nonzero, ite_false, Except.mapError, bind,
      Except.bind, penalizedOk]
    exact ⟨_, rfl, addDelta_size penalizedOk⟩

/-- Some deltas apply when each balance of the registry plus its reward fits in 64 bits.

The registry must have one balance for each validator, and fewer than 2^64 validators. -/
theorem applyAllDeltas_exists_ok {rewards penalties : Array Gwei}
    (matched : BalancesMatch state) (small : state.validators.data.size < 2 ^ 64)
    (fits : ∀ i (inside : i < state.balances.data.size),
      state.balances.data[i].toNat + (rewards.getD i 0).toNat < 2 ^ 64) :
    ∃ after, applyAllDeltas state (rewards, penalties) = .ok after := by
  unfold applyAllDeltas BalancesMatch at *
  refine foldlM_exists_ok_of_distinct id (fun (last : BeaconState preset fork) i =>
      ∃ inside : i < last.balances.data.size, i < 2 ^ 64 ∧
        last.balances.data[i].toNat + (rewards.getD i 0).toNat < 2 ^ 64)
    (fun last i ⟨inside, lt, fit⟩ => ?_) _ state (by simpa using List.nodup_range) ?_
  · intro i member
    have lt := List.mem_range.mp member
    exact ⟨by omega, by omega, fits i (by omega)⟩
  · refine ⟨_, applyDeltas_eq_ok_iff.mpr ⟨lt, inside, fit, rfl⟩,
      fun j other ⟨insideJ, ltJ, fitJ⟩ => ?_⟩
    have ne : i ≠ j := fun same => other same.symm
    exact ⟨by simpa [BeaconState.putBalance] using insideJ, ltJ,
      by simpa [BeaconState.putBalance, Array.getElem_set, ne] using fitJ⟩

/-- A list of deltas applies in turn when each balance plus all its rewards fits in 64 bits.

The registry must have one balance for each validator, and fewer than 2^64 validators. -/
private theorem foldlM_applyAllDeltas_exists_ok :
    ∀ (deltas : List (Array Gwei × Array Gwei)) (state : BeaconState preset fork),
      BalancesMatch state → state.validators.data.size < 2 ^ 64 →
      (∀ i (inside : i < state.balances.data.size), state.balances.data[i].toNat +
        (deltas.map fun delta => (delta.1.getD i 0).toNat).sum < 2 ^ 64) →
      ∃ after, deltas.foldlM applyAllDeltas state = .ok after
  | [], state, _, _, _ => ⟨state, rfl⟩
  | (rewards, penalties) :: rest, state, matched, small, fits => by
    simp only [List.map_cons, List.sum_cons] at fits
    obtain ⟨middle, applied⟩ := applyAllDeltas_exists_ok (rewards := rewards)
      (penalties := penalties) matched small fun i inside => by have := fits i inside; omega
    have sizes := sameSizes_applyAllDeltas applied
    have matchedMiddle := balancesMatch_of_sameSizes sizes matched
    obtain ⟨out, folded⟩ := foldlM_applyAllDeltas_exists_ok rest middle matchedMiddle
      (by rw [sizes.1]; exact small) fun i inside => by
        have inRegistry : i < state.validators.data.size := by
          unfold BalancesMatch at matchedMiddle
          rw [← sizes.1, ← matchedMiddle]
          exact inside
        obtain ⟨balance, found, fit, raised⟩ := (applyAllDeltas_balances applied i).1 inRegistry
        have old : state.balances.data[i]'(by unfold BalancesMatch at matched; omega) =
            balance := Option.some.inj ((Array.getElem?_eq_getElem _).symm.trans found)
        have new : middle.balances.data[i] =
            saturatingSub (balance + rewards.getD i 0) (penalties.getD i 0) := by
          simpa [Array.getElem?_eq_getElem inside] using raised
        have := fits i (by unfold BalancesMatch at matched; omega)
        rw [old] at this
        rw [new, toNat_saturatingSub, toNat_add_of_lt fit]
        omega
    exact ⟨out, by rw [List.foldlM_cons, applied]; exact folded⟩

/-- The whole increments of a budget are at least one, for a positive increment. -/
theorem one_le_budgetIncrements (positive : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0)
    (budget : Nat) : 1 ≤ preset.budgetIncrements budget := by
  have incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    Nat.pos_of_ne_zero fun zero => positive (UInt64.toNat_inj.mp (by simpa using zero))
  exact Nat.div_pos (Nat.le_max_left _ _) incPos

/-- An amount up to the budget or one increment has at most the whole increments of the budget. -/
theorem toNat_div_le_budgetIncrements {amount : Gwei} {budget : Nat}
    (bounded : amount.toNat ≤ max preset.EFFECTIVE_BALANCE_INCREMENT.toNat budget) :
    (amount / preset.EFFECTIVE_BALANCE_INCREMENT).toNat ≤ preset.budgetIncrements budget := by
  rw [UInt64.toNat_div]
  exact Nat.div_le_div_right bounded

/-- From Altair, the deltas of a flag succeed under bounds.

The total active balance must be at least one increment and at most the budget or one increment.

Each base reward of the registry must succeed, at most the bound on base rewards.

The finalized epoch must be at most the previous epoch, so that the test for a leak succeeds. -/
private theorem getFlagIndexDeltas_exists_ok {config : Config} {budget scoreBound : Nat}
    (altair : .altair ≤ fork) (positive : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0)
    (fit : RewardsFit preset config budget scoreBound) (within : state.RegistryWithinLimit)
    (summed : effectiveBalanceSum state ≤ budget) (finalized : FinalizedSettled state)
    (sized : ParticipationMatches state) {total : Gwei}
    (totalOk : getTotalActiveBalance state = .ok total)
    (low : preset.EFFECTIVE_BALANCE_INCREMENT ≤ total)
    (high : total.toNat ≤ max preset.EFFECTIVE_BALANCE_INCREMENT.toNat budget)
    (baseOk : ∀ index : ValidatorIndex, index.toNat < state.validators.data.size →
      ∃ base, getBaseReward state total index = .ok base ∧
        base.toNat ≤ preset.baseRewardCeiling)
    (flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length) :
    ∃ deltas, getFlagIndexDeltas state altair flagIndex = .ok deltas := by
  have incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    Nat.pos_of_ne_zero fun zero => positive (UInt64.toNat_inj.mp (by simpa using zero))
  have budgetLt : budget < 2 ^ 64 := fit.budget_lt
  obtain ⟨participating, participatingOk, inRange⟩ := getUnslashedParticipatingIndices_exists_ok
    within altair flagIndex.val.toUInt64 (Or.inl rfl) sized
  obtain ⟨participatingBalance, balanceOk, balanceLe⟩ :=
    getTotalBalance_exists_ok inRange (Nat.lt_of_le_of_lt summed budgetLt)
  obtain ⟨eligible, eligibleOk⟩ := getEligibleValidatorIndices_exists_ok within
  have distinct := (getEligibleValidatorIndices_ok within eligibleOk).1
  have eligibleLt := getEligibleValidatorIndices_lt within eligibleOk
  have leakOk := isInInactivityLeak_eq_ok finalized
  -- The increments that set the flag, and the active ones, are at most those of the budget.
  have participatingLe : (participatingBalance / preset.EFFECTIVE_BALANCE_INCREMENT).toNat ≤
      preset.budgetIncrements budget := toNat_div_le_budgetIncrements (by omega)
  have activeLe : (total / preset.EFFECTIVE_BALANCE_INCREMENT).toNat ≤
      preset.budgetIncrements budget := toNat_div_le_budgetIncrements high
  have activePos : 0 < (total / preset.EFFECTIVE_BALANCE_INCREMENT).toNat := by
    rw [UInt64.toNat_div]
    exact Nat.div_pos (UInt64.le_iff_toNat_le.mp low) incPos
  have activeFits : (total / preset.EFFECTIVE_BALANCE_INCREMENT).toNat *
      WEIGHT_DENOMINATOR.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ activeLe) fit.activeIncrements
  have numerator := fit.flagNumerator _ (List.getElem_mem flagIndex.isLt)
  have one := one_le_budgetIncrements positive budget
  obtain ⟨deltas, folded⟩ := foldlM_exists_ok_of_distinct UInt64.toNat
    (fun (last : Array Gwei × Array Gwei) (index : ValidatorIndex) =>
      index.toNat < state.validators.data.size ∧ index.toNat < last.1.size ∧
        index.toNat < last.2.size ∧ last.1.getD index.toNat 0 = 0 ∧
          last.2.getD index.toNat 0 = 0)
    (step := addFlagDelta state flagIndex
      (markIndices state.validators.data.size participating) total
      (participatingBalance / preset.EFFECTIVE_BALANCE_INCREMENT)
      (total / preset.EFFECTIVE_BALANCE_INCREMENT))
    (fun ⟨rewards, penalties⟩ index ⟨lt, insideRewards, insidePenalties, zeroRewards,
        zeroPenalties⟩ => by
      obtain ⟨base, based, baseLe⟩ := baseOk index lt
      have fits : base.toNat * PARTICIPATION_FLAG_WEIGHTS[flagIndex].toNat *
          (participatingBalance / preset.EFFECTIVE_BALANCE_INCREMENT).toNat < 2 ^ 64 :=
        Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.mul_le_mul_right _ baseLe) participatingLe)
          numerator
      have weighted : base.toNat * PARTICIPATION_FLAG_WEIGHTS[flagIndex].toNat < 2 ^ 64 :=
        Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ one)
          (Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.mul_le_mul_right _ baseLe) (Nat.le_refl _))
            numerator)
      obtain ⟨next, stepped, sizeRewards, sizePenalties⟩ := addFlagDelta_exists_ok
        (participated := markIndices state.validators.data.size participating) leakOk
        activeFits activePos based weighted fits insideRewards insidePenalties zeroRewards
        zeroPenalties
      refine ⟨next, stepped, fun other ne ⟨lt', insideRewards', insidePenalties', zeroRewards',
        zeroPenalties'⟩ => ?_⟩
      have kept := addFlagDelta_getD_of_ne stepped ne
      simp only [Prod.mk.injEq] at kept
      exact ⟨lt', by rw [sizeRewards]; exact insideRewards',
        by rw [sizePenalties]; exact insidePenalties', kept.1.trans zeroRewards',
        kept.2.trans zeroPenalties'⟩)
    eligible (Array.replicate state.validators.data.size 0,
      Array.replicate state.validators.data.size 0) distinct
    (fun index member => by
      have lt := eligibleLt index member
      exact ⟨lt, by simpa using lt, by simpa using lt, replicate_getD_zero _ _,
        replicate_getD_zero _ _⟩)
  refine ⟨deltas, ?_⟩
  simp only [getFlagIndexDeltas, liftAccessor, participatingOk, balanceOk, totalOk, eligibleOk,
    Except.mapError, bind, Except.bind]
  exact folded

/-- A quotient by a positive multiple of a divisor, times that divisor, is at most the dividend. -/
private theorem div_mul_mul_le {dividend factor divisor bound : Nat} (pos : 0 < factor)
    (le : dividend ≤ bound) : dividend / (factor * divisor) * divisor ≤ bound := by
  have scaled := Nat.div_mul_le_self dividend (factor * divisor)
  have grow := Nat.mul_le_mul_left (dividend / (factor * divisor))
    (Nat.le_mul_of_pos_left divisor pos)
  omega

/-- From Altair, each reward of a flag times the weight denominator is at most a bound.

The bound is the bound on base rewards, times the weight of the flag and the budget increments.

The hypotheses are those under which the deltas of the flag succeed. -/
private theorem getFlagIndexDeltas_reward_le {config : Config} {budget scoreBound : Nat}
    {altair : .altair ≤ fork} (positive : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0)
    (fit : RewardsFit preset config budget scoreBound) (within : state.RegistryWithinLimit)
    (summed : effectiveBalanceSum state ≤ budget) (sized : ParticipationMatches state)
    {total : Gwei} (totalOk : getTotalActiveBalance state = .ok total)
    (low : preset.EFFECTIVE_BALANCE_INCREMENT ≤ total)
    (baseOk : ∀ index : ValidatorIndex, index.toNat < state.validators.data.size →
      ∃ base, getBaseReward state total index = .ok base ∧
        base.toNat ≤ preset.baseRewardCeiling)
    {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length} {rewards penalties : Array Gwei}
    (computed : getFlagIndexDeltas state altair flagIndex = .ok (rewards, penalties))
    (j : Nat) (inside : j < state.validators.data.size) :
    (rewards.getD j 0).toNat * WEIGHT_DENOMINATOR.toNat ≤ preset.baseRewardCeiling *
      PARTICIPATION_FLAG_WEIGHTS[flagIndex].toNat * preset.budgetIncrements budget := by
  have incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    Nat.pos_of_ne_zero fun zero => positive (UInt64.toNat_inj.mp (by simpa using zero))
  have budgetLt : budget < 2 ^ 64 := fit.budget_lt
  obtain ⟨participating, participatingBalance, total', participatingOk, balanceOk, totalOk',
    entries⟩ := getFlagIndexDeltas_getD within computed
  obtain rfl : total = total' := Except.ok.inj (totalOk.symm.trans totalOk')
  obtain ⟨participating', participatingOk', inRange⟩ := getUnslashedParticipatingIndices_exists_ok
    within altair flagIndex.val.toUInt64 (Or.inl rfl) sized
  obtain rfl : participating = participating' :=
    Except.ok.inj (participatingOk.symm.trans participatingOk')
  obtain ⟨participatingBalance', balanceOk', balanceLe⟩ :=
    getTotalBalance_exists_ok inRange (Nat.lt_of_le_of_lt summed budgetLt)
  obtain rfl : participatingBalance = participatingBalance' :=
    Except.ok.inj (balanceOk.symm.trans balanceOk')
  have participatingLe : participatingBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      preset.budgetIncrements budget := Nat.div_le_div_right (by omega)
  have activePos : 0 < total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    Nat.div_pos (UInt64.le_iff_toNat_le.mp low) incPos
  obtain ⟨eligible, -, notEligible, isEligible⟩ := entries j inside
  cases eligible
  · rw [(notEligible rfl).1]
    simp
  · obtain ⟨base, based, present, absent⟩ := isEligible rfl
    obtain ⟨base', based', baseLe⟩ := baseOk j.toUInt64
      (by rw [toNat_toUInt64_of_lt within inside]; exact inside)
    obtain rfl : base = base' := Except.ok.inj (based.symm.trans based')
    by_cases member : j.toUInt64 ∈ participating
    · obtain ⟨leak, -, value, -⟩ := present member
      rw [value]
      split
      · simp
      · exact div_mul_mul_le activePos
          (Nat.mul_le_mul (Nat.mul_le_mul_right _ baseLe) participatingLe)
    · rw [(absent member).1]
      simp

/-- From Altair, the inactivity deltas succeed under bounds.

Each effective balance must be at most the largest cap, and each score at most the score bound.

The lists of scores and of flags must have one entry for each validator. -/
private theorem getInactivityPenaltyDeltas_exists_ok {config : Config} {budget scoreBound : Nat}
    (altair : .altair ≤ fork) (positive : preset.DivisorsPositive)
    (biased : config.INACTIVITY_SCORE_BIAS ≠ 0) (fit : RewardsFit preset config budget scoreBound)
    (within : state.RegistryWithinLimit)
    (capped : ∀ validator ∈ state.validators.data,
      validator.effectiveBalance.toNat ≤ preset.largestEffectiveBalance)
    (scored : ∀ score ∈ (state.inactivityScores altair).data, score.toNat ≤ scoreBound)
    (scoresMatch : InactivityScoresMatch state) (sized : ParticipationMatches state) :
    ∃ deltas, getInactivityPenaltyDeltas config state = .ok deltas := by
  have quotientPos : (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT ≠ 0 := by
    simp only [parameters]
    split_ifs
    · exact positive.inactivityPenaltyBellatrix
    · exact positive.inactivityPenaltyAltair
  obtain ⟨matching, matchingOk, -⟩ := getUnslashedParticipatingIndices_exists_ok within altair
    TIMELY_TARGET_FLAG_INDEX (Or.inl rfl) sized
  obtain ⟨eligible, eligibleOk⟩ := getEligibleValidatorIndices_exists_ok within
  have distinct := (getEligibleValidatorIndices_ok within eligibleOk).1
  have eligibleLt := getEligibleValidatorIndices_lt within eligibleOk
  obtain ⟨penalties, folded⟩ := foldlM_exists_ok_of_distinct UInt64.toNat
    (fun (last : Array Gwei) (index : ValidatorIndex) =>
      index.toNat < state.validators.data.size ∧ index.toNat < last.size ∧
        last.getD index.toNat 0 = 0)
    (step := addInactivityScorePenalty config state altair
      (markIndices state.validators.data.size matching))
    (fun last index ⟨lt, insideLast, zero⟩ => by
      have scoreInside : index.toNat < (state.inactivityScores altair).data.size := by
        rw [scoresMatch altair]
        exact lt
      obtain ⟨next, stepped, size⟩ := addInactivityScorePenalty_exists_ok altair
        (targetMatched := markIndices state.validators.data.size matching)
        (Array.getElem?_eq_getElem lt) (capped _ (Array.getElem_mem lt))
        (Array.getElem?_eq_getElem scoreInside) (scored _ (Array.getElem_mem scoreInside))
        fit.scorePenalty (fit.penaltyQuotient fork) biased quotientPos insideLast zero
      refine ⟨next, stepped, fun other ne ⟨lt', inside', zero'⟩ => ⟨lt', ?_, ?_⟩⟩
      · rw [size]
        exact inside'
      · rw [addInactivityScorePenalty_getD_of_ne stepped ne]
        exact zero')
    eligible (Array.replicate state.validators.data.size 0) distinct
    (fun index member => by
      have lt := eligibleLt index member
      exact ⟨lt, by simpa using lt, replicate_getD_zero _ _⟩)
  refine ⟨(Array.replicate state.validators.data.size 0, penalties), ?_⟩
  simp only [getInactivityPenaltyDeltas, altair, ↓reduceDIte, liftAccessor, matchingOk,
    eligibleOk, Except.mapError, bind, Except.bind, folded]
  rfl

/-- The weights of the flags, read in order of their indices, are the list of weights. -/
private theorem map_flag_weights :
    ((List.finRange PARTICIPATION_FLAG_WEIGHTS.length).map fun flagIndex =>
      PARTICIPATION_FLAG_WEIGHTS[flagIndex].toNat) = PARTICIPATION_FLAG_WEIGHTS.map (·.toNat) := by
  decide

/-- From Altair, the rewards and penalties succeed under bounds.

The registry must stay within its limit, with one balance for each validator.

Each effective balance must be at most the largest cap, as the cap of its validator is.

The sum of the effective balances and each balance must be at most the budget.

Each inactivity score must be at most the score bound, and the bounds must fit.

The finalized epoch must be at most the previous epoch, so that the test for a leak succeeds.

The lists of scores and of flags must have one entry for each validator.

The divisors of the preset and of the configuration must be positive.

The hypotheses are read on the state that the update of the inactivity scores returns.

A run must show that they hold there. -/
theorem processRewardsAndPenalties_total {config : Config} {budget scoreBound : Nat}
    (altair : .altair ≤ fork) (positive : preset.DivisorsPositive)
    (configPositive : config.DivisorsPositive) (fit : RewardsFit preset config budget scoreBound)
    (within : state.RegistryWithinLimit) (matched : BalancesMatch state)
    (capped : ∀ validator ∈ state.validators.data,
      validator.effectiveBalance.toNat ≤ preset.largestEffectiveBalance)
    (summed : effectiveBalanceSum state ≤ budget)
    (funded : ∀ balance ∈ state.balances.data, balance.toNat ≤ budget)
    (scored : ∀ score ∈ (state.inactivityScores altair).data, score.toNat ≤ scoreBound)
    (finalized : FinalizedSettled state) (scoresMatch : InactivityScoresMatch state)
    (sized : ParticipationMatches state) :
    ∃ after, processRewardsAndPenalties config state = .ok after := by
  by_cases genesis : getCurrentEpoch state = GENESIS_EPOCH
  · exact ⟨state, processRewardsAndPenalties_genesis config genesis⟩
  have budgetLt : budget < 2 ^ 64 := fit.budget_lt
  obtain ⟨total, totalOk, low, highCases⟩ :=
    getTotalActiveBalance_exists_ok within (Nat.lt_of_le_of_lt summed budgetLt)
  have high : total.toNat ≤ max preset.EFFECTIVE_BALANCE_INCREMENT.toNat budget := by
    rcases highCases with same | le
    · rw [same]
      exact Nat.le_max_left _ _
    · omega
  obtain ⟨per, perOk, perLe⟩ :=
    getBaseRewardPerIncrement_le positive.increment fit.perIncrement low
  have one := one_le_budgetIncrements positive.increment budget
  -- The bound on base rewards fits, since the source weight and the budget increments are positive.
  have ceilingLt : preset.baseRewardCeiling < 2 ^ 64 := by
    have numerator := fit.flagNumerator _ (List.getElem_mem (l := PARTICIPATION_FLAG_WEIGHTS)
      (n := 0) (by decide))
    have weight : 0 < PARTICIPATION_FLAG_WEIGHTS[0].toNat := by decide
    exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_mul_of_pos_right _ weight)
      (Nat.le_mul_of_pos_right _ one)) numerator
  have largest := capped
  have baseOk : ∀ index : ValidatorIndex, index.toNat < state.validators.data.size →
      ∃ base, getBaseReward state total index = .ok base ∧
        base.toNat ≤ preset.baseRewardCeiling := fun index lt =>
    getBaseReward_le altair perOk perLe ceilingLt (Array.getElem?_eq_getElem lt)
      (largest _ (Array.getElem_mem lt))
  obtain ⟨flagDeltas, flagOk⟩ := mapM_exists_ok (f := getFlagIndexDeltas state altair)
    (xs := List.finRange PARTICIPATION_FLAG_WEIGHTS.length) fun flagIndex _ =>
      getFlagIndexDeltas_exists_ok altair positive.increment fit within summed finalized sized
        totalOk low high baseOk flagIndex
  obtain ⟨⟨inactivityRewards, inactivityPenalties⟩, inactivityOk⟩ :=
    getInactivityPenaltyDeltas_exists_ok altair positive configPositive.scoreBias fit within largest
      scored scoresMatch sized
  have small : state.validators.data.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt within preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
  obtain ⟨after, applied⟩ := foldlM_applyAllDeltas_exists_ok
    (flagDeltas ++ [(inactivityRewards, inactivityPenalties)]) state matched small
    fun i inside => by
      have inRegistry : i < state.validators.data.size := by
        unfold BalancesMatch at matched
        omega
      have rewards := sum_map_le_sum_map_of_mapM_ok
        (value := fun delta : Array Gwei × Array Gwei =>
          (delta.1.getD i 0).toNat * WEIGHT_DENOMINATOR.toNat)
        (bound := fun flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length =>
          preset.baseRewardCeiling * PARTICIPATION_FLAG_WEIGHTS[flagIndex].toNat *
            preset.budgetIncrements budget)
        (fun flagIndex ⟨rewards, penalties⟩ computed =>
          getFlagIndexDeltas_reward_le positive.increment fit within summed sized totalOk low
            baseOk computed i inRegistry) flagOk
      rw [sum_map_mul_right (fun delta : Array Gwei × Array Gwei => (delta.1.getD i 0).toNat),
        sum_map_mul_right (fun flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length =>
          preset.baseRewardCeiling * PARTICIPATION_FLAG_WEIGHTS[flagIndex].toNat),
        sum_map_mul_left preset.baseRewardCeiling
          (fun flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length =>
            PARTICIPATION_FLAG_WEIGHTS[flagIndex].toNat), map_flag_weights] at rewards
      have balance := funded _ (Array.getElem_mem inside)
      have inactive := getInactivityPenaltyDeltas_rewards inactivityOk i
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, inactive, UInt64.toNat_zero]
      have quotient := (Nat.le_div_iff_mul_le (by decide : 0 < WEIGHT_DENOMINATOR.toNat)).mpr
        rewards
      have := fit.flagRewards
      omega
  refine ⟨after, ?_⟩
  simp only [processRewardsAndPenalties, genesis, altair, ↓reduceIte, ↓reduceDIte, flagOk,
    inactivityOk, bind, Except.bind]
  exact applied

end EthLib.Consensus
