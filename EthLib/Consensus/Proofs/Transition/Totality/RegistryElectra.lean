module

public import EthLib.Consensus.Proofs.Transition.Totality.Bound
public import EthLib.Consensus.Proofs.Transition.Totality.Registry

/-!
# Proofs: registry updates from Electra succeed

From Electra, one pass over the registry queues, ejects or activates each validator in turn.

An ejection starts an exit, which takes its place in a queue of balance.

The queue spends a churn of balance each epoch, which is at least one increment.

The queue opens no earlier than the first epoch an exit may take, which a ceiling bounds.

So an exit raises that ceiling by at most its effective balance in increments, plus one.

Only a validator that has not started to exit can start, and its cost then leaves the total.

So the end of the queue plus the cost still owed does not grow, and the same holds for each exit.

The churn left over stays at most the larger of its value at the start and a bound on one churn.

Room for these bounds, with a positive churn, excludes every checked error.

The step keeps the slot, the balances and every effective balance.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork}

/-- A bound on the epochs by which the exits not yet started can move the end of the exit queue.

Each validator without an exit epoch counts its effective balance in increments, plus one. -/
def exitCost (preset : Preset) (state : BeaconState preset fork) : Nat :=
  ((state.validators.data.toList.filter (·.exitEpoch = FAR_FUTURE_EPOCH)).map fun validator =>
    validator.effectiveBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1).sum

/-- A bound on the churn of exits of an epoch.

It is the least churn, plus the sum of the effective balances, plus one increment. -/
def exitChurnCeiling (config : Config) (state : BeaconState preset fork) : Nat :=
  config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat + effectiveBalanceSum state +
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat

/-- The queue succeeds when its churn is positive and an amount plus one churn is at most `2^64`.

The later of the two epochs plus the amount in churns, plus one, must fit too. -/
private theorem churnQueue_exists_ok
    {earliestEpoch firstEpoch perEpochChurn churnLeft amount : UInt64}
    (positive : 0 < perEpochChurn.toNat)
    (epochRoom : (max earliestEpoch firstEpoch).toNat + amount.toNat / perEpochChurn.toNat + 1 <
      2 ^ 64)
    (churnRoom : amount.toNat + perEpochChurn.toNat ≤ 2 ^ 64) :
    ∃ epoch left,
      churnQueue earliestEpoch firstEpoch perEpochChurn churnLeft amount = .ok (epoch, left) := by
  unfold churnQueue
  dsimp only
  generalize max earliestEpoch firstEpoch = first at epochRoom ⊢
  generalize (if earliestEpoch < first then perEpochChurn else churnLeft) = available
  split
  · exact ⟨_, _, rfl⟩
  · rename_i over
    have over : available.toNat < amount.toNat := by
      rw [UInt64.le_iff_toNat_le] at over
      omega
    have nonzero : perEpochChurn ≠ 0 := by
      intro zero
      subst zero
      simp at positive
    have rest : (amount - available - 1).toNat = amount.toNat - available.toNat - 1 := by
      have difference : (amount - available).toNat = amount.toNat - available.toNat :=
        UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt over))
      have one : (1 : UInt64) ≤ amount - available := by
        rw [UInt64.le_iff_toNat_le, difference]
        show 1 ≤ _
        omega
      rw [UInt64.toNat_sub_of_le _ _ one, difference]
      rfl
    have quotientValue : ((amount - available - 1) / perEpochChurn).toNat =
        (amount.toNat - available.toNat - 1) / perEpochChurn.toNat := by
      rw [UInt64.toNat_div, rest]
    generalize named : (amount - available - 1) / perEpochChurn = quotient at quotientValue
    have divided : divChecked (amount - available - 1) perEpochChurn = .ok quotient := by
      simp only [divChecked, nonzero, ↓reduceIte, named]
    have quotientLe : quotient.toNat ≤ amount.toNat / perEpochChurn.toNat :=
      quotientValue ▸ Nat.div_le_div_right (by omega)
    have quotientMul : quotient.toNat * perEpochChurn.toNat ≤
        amount.toNat - available.toNat - 1 :=
      quotientValue ▸ Nat.div_mul_le_self _ _
    have additional : (quotient + 1).toNat = quotient.toNat + 1 :=
      toNat_add_of_lt (by simp; omega)
    have epochFits : first.toNat + (quotient + 1).toNat < 2 ^ 64 := by omega
    have productFits : (quotient + 1).toNat * perEpochChurn.toNat < 2 ^ 64 := by
      rw [additional, Nat.add_mul, Nat.one_mul]
      omega
    have productValue : ((quotient + 1) * perEpochChurn).toNat =
        (quotient + 1).toNat * perEpochChurn.toNat := by
      rw [UInt64.toNat_mul, Nat.mod_eq_of_lt productFits]
    have sumFits : available.toNat + ((quotient + 1) * perEpochChurn).toNat < 2 ^ 64 := by
      rw [productValue, additional, Nat.add_mul, Nat.one_mul]
      omega
    simp only [divided, addChecked_of_lt epochFits, mulChecked_of_lt productFits,
      addChecked_of_lt sumFits, bind, Except.bind, pure, Except.pure]
    exact ⟨_, _, rfl⟩

/-- A share of a total, at least the least churn and rounded down to an increment, is bounded.

It is at least one increment, and at most the least churn plus the total. -/
private theorem roundToIncrement_share_bounds {config : Config} (total quotient : Gwei)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT)
    (minimum : preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA) :
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
        (roundToIncrement preset (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
          (total / quotient))).toNat ∧
      (roundToIncrement preset (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
          (total / quotient))).toNat ≤
        config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat + total.toNat := by
  rw [toNat_roundToIncrement, toNat_max, UInt64.toNat_div]
  have positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    UInt64.lt_iff_toNat_lt.mp increment
  have minimum := UInt64.le_iff_toNat_le.mp minimum
  have share := Nat.div_le_self total.toNat quotient.toNat
  have amountLower : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat (total.toNat / quotient.toNat) := by
    omega
  have amountUpper : max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
      (total.toNat / quotient.toNat) ≤
        config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat + total.toNat := by
    omega
  generalize max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat (total.toNat / quotient.toNat) =
    amount at *
  have split := Nat.mod_add_div amount preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  have whole : 1 ≤ amount / preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    (Nat.le_div_iff_mul_le positive).mpr (by omega)
  have lower : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      amount - amount % preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    have := Nat.le_mul_of_pos_right preset.EFFECTIVE_BALANCE_INCREMENT.toNat whole
    omega
  exact ⟨lower, Nat.le_trans (Nat.sub_le _ _) amountUpper⟩

/-- The churn of exits succeeds within the registry limit, with effective balances that fit.

It is at least one increment, and at most the bound of the exit churn. -/
private theorem exitChurnLimit_exists_ok {config : Config} {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) (summed : effectiveBalanceSum state < 2 ^ 64)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT)
    (minimum : preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA)
    (maximum :
      preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT) :
    ∃ churn, exitChurnLimit config state = .ok churn ∧
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ churn.toNat ∧
      churn.toNat ≤ exitChurnCeiling config state := by
  obtain ⟨total, totalOk, -, totalLe⟩ := getTotalActiveBalance_exists_ok within summed
  have totalLe :
      total.toNat ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat + effectiveBalanceSum state := by
    rcases totalLe with rfl | le <;> omega
  unfold exitChurnLimit exitChurnCeiling
  split
  · obtain ⟨lower, upper⟩ := roundToIncrement_share_bounds (config := config) total
      config.CHURN_LIMIT_QUOTIENT_GLOAS increment minimum
    refine ⟨_, by simp only [getExitChurnLimit, totalOk, bind, Except.bind, pure, Except.pure],
      lower, by omega⟩
  · obtain ⟨lower, upper⟩ := roundToIncrement_share_bounds (config := config) total
      config.CHURN_LIMIT_QUOTIENT increment minimum
    refine ⟨_, by simp only [getActivationExitChurnLimit, getBalanceChurnLimit, totalOk, bind,
      Except.bind, pure, Except.pure]; rfl, ?_⟩
    rw [toNat_min]
    have maximum := UInt64.le_iff_toNat_le.mp maximum
    omega

/-- Epochs of a churn of at least one increment hold an amount plus less than one churn.

Then there are at most the amount in increments, plus one. -/
private theorem epochs_le_div_add_one {epochs churn increment left amount : Nat}
    (positive : 0 < increment) (least : increment ≤ churn)
    (spent : epochs * churn ≤ left + amount) (below : left < churn) :
    epochs ≤ amount / increment + 1 := by
  cases epochs with
  | zero => exact Nat.zero_le _
  | succ epochs =>
    rw [Nat.add_mul, Nat.one_mul] at spent
    have scaled := Nat.mul_le_mul_left epochs least
    have bounded : epochs * increment ≤ amount := by omega
    have := (Nat.le_div_iff_mul_le positive).mpr bounded
    omega

/-- The bounds that hold along the pass, from a start state, below a ceiling on the exit epochs.

The slot, the balances and the effective balances stay those of the start.

The end of the exit queue and every exit epoch are at most the ceiling.

The churn left over is at most the larger of the one at the start and one churn bound. -/
private def Kept (config : Config) (electra : .pectra ≤ fork)
    (start state : BeaconState preset fork) (bound : Nat) : Prop :=
  state.slot = start.slot ∧ state.balances = start.balances ∧
    state.validators.data.map (·.effectiveBalance) =
      start.validators.data.map (·.effectiveBalance) ∧
    (state.earliestExitEpoch electra).toNat ≤ bound ∧
    (∀ validator ∈ state.validators.data, validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
      validator.exitEpoch.toNat ≤ bound) ∧
    (state.exitBalanceToConsume electra).toNat ≤
      max (start.exitBalanceToConsume electra).toNat (exitChurnCeiling config start)

/-- A state that keeps the effective balances of the start keeps the size of its registry. -/
private theorem Kept.size {config : Config} {electra : .pectra ≤ fork}
    {start state : BeaconState preset fork} {bound : Nat}
    (kept : Kept config electra start state bound) :
    state.validators.data.size = start.validators.data.size := by
  have := congrArg Array.size kept.2.2.1
  simpa using this

/-- A state that keeps the effective balances of the start keeps their sum. -/
private theorem Kept.sum {config : Config} {electra : .pectra ≤ fork}
    {start state : BeaconState preset fork} {bound : Nat}
    (kept : Kept config electra start state bound) :
    effectiveBalanceSum state = effectiveBalanceSum start := by
  unfold effectiveBalanceSum
  have := congrArg (fun data => (data.toList.map UInt64.toNat).sum) kept.2.2.1
  simpa [List.map_map, Function.comp_def] using this

/-- A state that keeps the slot of the start keeps its current epoch. -/
private theorem Kept.epoch {config : Config} {electra : .pectra ≤ fork}
    {start state : BeaconState preset fork} {bound : Nat}
    (kept : Kept config electra start state bound) :
    getCurrentEpoch state = getCurrentEpoch start := by
  simp [getCurrentEpoch, kept.1]

/-- An exit of an amount up to the sum of the effective balances spends churn within the bounds.

The new end of the queue is at most the ceiling plus the amount in increments, plus one.

The churn left over stays within its bound. -/
private theorem computeExitEpochAndUpdateChurn_kept {config : Config} {electra : .pectra ≤ fork}
    {start state : BeaconState preset fork} {bound : Nat} {amount : Gwei}
    (within : start.RegistryWithinLimit) (summed : effectiveBalanceSum start < 2 ^ 64)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT)
    (minimum : preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA)
    (maximum :
      preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT)
    (first : (getCurrentEpoch start).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ bound)
    (carried : (start.exitBalanceToConsume electra).toNat + 3 * exitChurnCeiling config start <
      2 ^ 64)
    (kept : Kept config electra start state bound)
    (amountLe : amount.toNat ≤ effectiveBalanceSum start)
    (room : bound + (amount.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1) < 2 ^ 64) :
    ∃ epoch left, computeExitEpochAndUpdateChurn config state electra amount =
        .ok ({ state with
          exitBalanceToConsume := fun _ => left, earliestExitEpoch := fun _ => epoch }, epoch) ∧
      epoch.toNat ≤ bound + (amount.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1) ∧
      left.toNat ≤
        max (start.exitBalanceToConsume electra).toNat (exitChurnCeiling config start) := by
  have boundLt : bound < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) room
  have stateWithin : state.RegistryWithinLimit := by
    unfold BeaconState.RegistryWithinLimit
    rw [kept.size]
    exact within
  obtain ⟨churn, churnOk, churnLower, churnUpper⟩ := exitChurnLimit_exists_ok (config := config)
    stateWithin (kept.sum ▸ summed) increment minimum maximum
  have ceilingSame : exitChurnCeiling config state = exitChurnCeiling config start := by
    simp only [exitChurnCeiling, kept.sum]
  rw [ceilingSame] at churnUpper
  have ceilingGe : effectiveBalanceSum start ≤ exitChurnCeiling config start := by
    unfold exitChurnCeiling
    omega
  have current := kept.epoch
  let firstEpoch := ((getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat).toUInt64
  have firstValue : firstEpoch.toNat =
      (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat := by
    change (_ % 2 ^ 64) = _
    exact Nat.mod_eq_of_lt (by rw [current]; omega)
  have firstOk : computeActivationExitEpoch preset (getCurrentEpoch state) = .ok firstEpoch :=
    computeActivationExitEpoch_ok_iff.mpr ⟨by rw [current]; omega, firstValue⟩
  have earliestLe := kept.2.2.2.1
  have leftLe := kept.2.2.2.2.2
  rw [current] at firstValue
  have openLe : (max (state.earliestExitEpoch electra) firstEpoch).toNat ≤ bound := by
    rw [toNat_max]
    omega
  have positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    UInt64.lt_iff_toNat_lt.mp increment
  have shares : amount.toNat / churn.toNat ≤
      amount.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    Nat.div_le_div_left churnLower positive
  obtain ⟨epoch, left, queueOk⟩ := churnQueue_exists_ok
    (earliestEpoch := state.earliestExitEpoch electra) (firstEpoch := firstEpoch)
    (perEpochChurn := churn) (churnLeft := state.exitBalanceToConsume electra) (amount := amount)
    (by omega) (by omega) (by omega)
  obtain ⟨placed, spent, last⟩ := churnQueue_spend queueOk
  have availableLe : (if state.earliestExitEpoch electra <
      max (state.earliestExitEpoch electra) firstEpoch then churn
      else state.exitBalanceToConsume electra).toNat ≤
        max (start.exitBalanceToConsume electra).toNat (exitChurnCeiling config start) := by
    split <;> omega
  generalize (if state.earliestExitEpoch electra <
      max (state.earliestExitEpoch electra) firstEpoch then churn
      else state.exitBalanceToConsume electra) = available at spent availableLe
  have placed := UInt64.le_iff_toNat_le.mp placed
  refine ⟨epoch, left, ?_, ?_, ?_⟩
  · simp only [computeExitEpochAndUpdateChurn, firstOk, churnOk, queueOk, liftArith,
      Except.mapError, bind, Except.bind, pure, Except.pure]
  · rcases last with same | below
    · rw [same]
      have := Nat.zero_le (amount.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
      omega
    · have epochs := epochs_le_div_add_one
        (epochs := epoch.toNat - (max (state.earliestExitEpoch electra) firstEpoch).toNat)
        (amount := amount.toNat) positive churnLower (by omega) below
      omega
  · rcases last with same | below
    · rw [same, Nat.sub_self, Nat.zero_mul] at spent
      omega
    · omega

/-- A state with a bound keeps the bounds below any larger one. -/
private theorem Kept.mono {config : Config} {electra : .pectra ≤ fork}
    {start state : BeaconState preset fork} {bound later : Nat}
    (kept : Kept config electra start state bound) (le : bound ≤ later) :
    Kept config electra start state later := by
  obtain ⟨slot, balances, effective, earliest, exits, left⟩ := kept
  exact ⟨slot, balances, effective, by omega,
    fun validator member finite => Nat.le_trans (exits validator member finite) le, left⟩

/-- A validator replaced with the same effective balance keeps the bounds below a larger one.

Its exit epoch, if it has one, must lie below the larger bound. -/
private theorem Kept.putValidator {config : Config} {electra : .pectra ≤ fork}
    {start state : BeaconState preset fork} {bound later index : Nat}
    (inside : index < state.validators.data.size) {validator : Validator}
    (kept : Kept config electra start state bound) (le : bound ≤ later)
    (same : validator.effectiveBalance = state.validators.data[index].effectiveBalance)
    (exit : validator.exitEpoch ≠ FAR_FUTURE_EPOCH → validator.exitEpoch.toNat ≤ later) :
    Kept config electra start (state.putValidator index inside validator) later := by
  obtain ⟨slot, balances, effective, earliest, exits, left⟩ := kept.mono le
  refine ⟨slot, balances, ?_, earliest, ?_, left⟩
  · simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set]
    rw [← effective]
    apply Array.ext (by simp)
    intro position first second
    simp only [Array.getElem_map, Array.getElem_set]
    split
    · subst_vars
      exact same
    · rfl
  · intro other member finite
    simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set] at member
    rcases Array.mem_or_eq_of_mem_set (w := inside) member with old | rfl
    · exact exits other old finite
    · exact exit finite

/-- The cost of a validator in the exit queue: its effective balance in increments, plus one.

A validator that has started to exit costs nothing. -/
private def exitCostOf (preset : Preset) (validator : Validator) : Nat :=
  if validator.exitEpoch = FAR_FUTURE_EPOCH then
    validator.effectiveBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1
  else 0

/-- The cost of the exits not yet started at some positions of the registry. -/
private def exitCostAt (state : BeaconState preset fork) (indices : List Nat) : Nat :=
  (indices.map fun index => ((state.validators.data[index]?).map (exitCostOf preset)).getD 0).sum

/-- The cost at one position inside the registry is the cost of its validator. -/
private theorem exitCostAt_single {state : BeaconState preset fork} {index : Nat}
    (inside : index < state.validators.data.size) :
    exitCostAt state [index] = exitCostOf preset state.validators.data[index] := by
  simp [exitCostAt, Array.getElem?_eq_getElem inside]

/-- The cost at the position of a replaced validator is the cost of the new validator. -/
private theorem exitCostAt_putValidator {state : BeaconState preset fork} {index : Nat}
    (inside : index < state.validators.data.size) (validator : Validator) :
    exitCostAt (state.putValidator index inside validator) [index] =
      exitCostOf preset validator := by
  simp [exitCostAt, BeaconState.putValidator, inside]

/-- A validator replaced at one position leaves the validators at the other positions. -/
private theorem putValidator_getElem?_ne {state : BeaconState preset fork} {index other : Nat}
    (inside : index < state.validators.data.size) (validator : Validator)
    (different : other ≠ index) :
    (state.putValidator index inside validator).validators.data[other]? =
      state.validators.data[other]? := by
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set]
  exact Array.getElem?_set_ne inside (Ne.symm different)

/-- An exit started within the bounds keeps the bound plus the cost at its position.

The validator stops owing its cost, and the bound grows by at most that cost.

It changes no other validator. -/
private theorem initiateValidatorExit_kept {config : Config} {electra : .pectra ≤ fork}
    {start state : BeaconState preset fork} {bound : Nat} {index : ValidatorIndex}
    (within : start.RegistryWithinLimit) (summed : effectiveBalanceSum start < 2 ^ 64)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT)
    (minimum : preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA)
    (maximum :
      preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT)
    (first : (getCurrentEpoch start).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ bound)
    (carried : (start.exitBalanceToConsume electra).toNat + 3 * exitChurnCeiling config start <
      2 ^ 64)
    (kept : Kept config electra start state bound)
    (inside : index.toNat < state.validators.data.size)
    (room : bound + exitCostOf preset state.validators.data[index.toNat] +
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat < 2 ^ 64 - 1) :
    ∃ after, initiateValidatorExit config state index = .ok after ∧
      ∃ later, bound ≤ later ∧ Kept config electra start after later ∧
        later + exitCostAt after [index.toNat] ≤ bound + exitCostAt state [index.toNat] ∧
        ∀ other, other ≠ index.toNat →
          after.validators.data[other]? = state.validators.data[other]? := by
  let validator := state.validators.data[index.toNat]
  have found : getValidator state index = .ok validator := by
    simp [getValidator, Array.getElem?_eq_getElem inside, validator]
  by_cases far : validator.exitEpoch = FAR_FUTURE_EPOCH
  · have cost : exitCostOf preset validator =
        validator.effectiveBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1 := by
      simp only [exitCostOf, far, ↓reduceIte]
    have amountLe : validator.effectiveBalance.toNat ≤ effectiveBalanceSum start := by
      rw [← kept.sum]
      exact List.le_sum_of_mem (List.mem_map_of_mem
        (f := fun validator : Validator => validator.effectiveBalance.toNat)
        (Array.mem_toList_iff.mpr (Array.getElem_mem inside)))
    change bound + exitCostOf preset validator + _ < _ at room
    rw [cost] at room
    obtain ⟨epoch, left, queueOk, epochLe, leftLe⟩ := computeExitEpochAndUpdateChurn_kept
      within summed increment minimum maximum first carried kept amountLe (by omega)
    have delayFits :
        epoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat < 2 ^ 64 := by omega
    have started : epoch ≠ FAR_FUTURE_EPOCH := by
      intro equal
      have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
      rw [equal, far] at epochLe
      omega
    let changed : Validator := { validator with
      exitEpoch := epoch, withdrawableEpoch := epoch + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY }
    have changedCost : exitCostOf preset changed = 0 := by
      simp only [exitCostOf, changed, started, ↓reduceIte]
    let queued : BeaconState preset fork := { state with
      exitBalanceToConsume := fun _ => left, earliestExitEpoch := fun _ => epoch }
    have queuedKept : Kept config electra start queued
        (bound + (validator.effectiveBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
          1)) :=
      ⟨kept.1, kept.2.1, kept.2.2.1, epochLe, fun other member finite =>
        Nat.le_trans (kept.2.2.2.2.1 other member finite) (Nat.le_add_right _ _), leftLe⟩
    refine ⟨queued.putValidator index.toNat inside changed, ?_, _, Nat.le_add_right _ _,
      Kept.putValidator (state := queued) (validator := changed) inside queuedKept
        (Nat.le_refl _) rfl (fun _ => epochLe), ?_,
      fun _ different => putValidator_getElem?_ne (state := queued) inside changed different⟩
    · simp only [initiateValidatorExit, found, far, bne_self_eq_false, exitQueue, electra,
        ↓reduceDIte, queueOk, liftArith, addChecked_of_lt delayFits, Except.mapError, bind,
        Except.bind, Bool.false_eq_true, ↓reduceIte]
      simp [BeaconState.setValidator, inside, queued, changed]
    · rw [exitCostAt_putValidator (state := queued) inside changed, changedCost,
        exitCostAt_single inside]
      change _ ≤ bound + exitCostOf preset validator
      rw [cost]
      omega
  · refine ⟨state, ?_, bound, Nat.le_refl _, kept, Nat.le_refl _, fun _ _ => rfl⟩
    simp [initiateValidatorExit, found, far, bind, Except.bind, pure, Except.pure]

/-- One registry update from Electra keeps the bound plus the cost at its position.

Only a validator that starts to exit raises the bound, by the cost it stops owing.

It changes no other validator. -/
private theorem updateRegistryEntryElectra_kept {config : Config} {electra : .pectra ≤ fork}
    {start state : BeaconState preset fork} {bound index : Nat} {activationEpoch : Epoch}
    (within : start.RegistryWithinLimit) (summed : effectiveBalanceSum start < 2 ^ 64)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT)
    (minimum : preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA)
    (maximum :
      preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT)
    (first : (getCurrentEpoch start).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ bound)
    (carried : (start.exitBalanceToConsume electra).toNat + 3 * exitChurnCeiling config start <
      2 ^ 64)
    (kept : Kept config electra start state bound)
    (inside : index < state.validators.data.size)
    (room : bound + exitCostOf preset state.validators.data[index] +
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat < 2 ^ 64 - 1) :
    ∃ after, updateRegistryEntryElectra config activationEpoch state index = .ok after ∧
      ∃ later, bound ≤ later ∧ Kept config electra start after later ∧
        later + exitCostAt after [index] ≤ bound + exitCostAt state [index] ∧
        ∀ other, other ≠ index →
          after.validators.data[other]? = state.validators.data[other]? := by
  let validator := state.validators.data[index]
  have found : getValidatorAt state index = .ok validator := by
    simp [getValidatorAt, Array.getElem?_eq_getElem inside, validator]
  have current := kept.epoch
  have old : validator.exitEpoch ≠ FAR_FUTURE_EPOCH → validator.exitEpoch.toNat ≤ bound :=
    kept.2.2.2.2.1 validator (Array.getElem_mem inside)
  have unchanged (changed : Validator) (sameExit : changed.exitEpoch = validator.exitEpoch)
      (sameBalance : changed.effectiveBalance = validator.effectiveBalance) :
      bound + exitCostAt (state.putValidator index inside changed) [index] ≤
        bound + exitCostAt state [index] := by
    rw [exitCostAt_putValidator inside, exitCostAt_single inside]
    simp only [exitCostOf, sameExit, sameBalance, validator, Nat.le_refl]
  by_cases eligible : isEligibleForActivationQueue preset fork validator
  · have fits : (getCurrentEpoch state).toNat + (1 : UInt64).toNat < 2 ^ 64 := by
      simp only [UInt64.toNat_one, current]
      omega
    let changed := { validator with activationEligibilityEpoch := getCurrentEpoch state + 1 }
    refine ⟨state.putValidator index inside changed, ?_, bound, Nat.le_refl _,
      Kept.putValidator (validator := changed) inside kept (Nat.le_refl _) rfl old,
      unchanged changed rfl rfl,
      fun _ different => putValidator_getElem?_ne inside changed different⟩
    simp [updateRegistryEntryElectra, liftAccessor, found, eligible, liftArith,
      addChecked_of_lt fits, Except.mapError, bind, Except.bind, BeaconState.setValidatorAt,
      inside, changed, validator]
  by_cases eject : isActiveValidator validator (getCurrentEpoch state) &&
      validator.effectiveBalance ≤ config.EJECTION_BALANCE
  · have indexFits : index < 2 ^ 64 := Nat.lt_of_lt_of_le inside (by
      rw [kept.size]
      exact Nat.le_trans within (Nat.le_of_lt preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt))
    have converted : ofNatChecked index = .ok index.toUInt64 := ofNatChecked_of_lt indexFits
    have indexValue : index.toUInt64.toNat = index := by
      simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt indexFits]
    obtain ⟨after, exited, later, grown, afterKept, potential, others⟩ :=
      initiateValidatorExit_kept (index := index.toUInt64) within summed increment minimum
        maximum first carried kept (by rw [indexValue]; exact inside)
        (by simpa only [indexValue] using room)
    simp only [indexValue] at potential others
    refine ⟨after, ?_, later, grown, afterKept, potential, others⟩
    simp only [updateRegistryEntryElectra, liftAccessor, found, eligible, eject, liftArith,
      converted, exited, Except.mapError, bind, Except.bind, Bool.false_eq_true, ↓reduceIte]
  by_cases ready : isEligibleForActivation state validator
  · let changed := { validator with activationEpoch }
    refine ⟨state.putValidator index inside changed, ?_, bound, Nat.le_refl _,
      Kept.putValidator (validator := changed) inside kept (Nat.le_refl _) rfl old,
      unchanged changed rfl rfl,
      fun _ different => putValidator_getElem?_ne inside changed different⟩
    simp [updateRegistryEntryElectra, liftAccessor, found, eligible, eject, ready,
      Except.mapError, bind, Except.bind, BeaconState.setValidatorAt, inside, changed, validator]
  · refine ⟨state, ?_, bound, Nat.le_refl _, kept, Nat.le_refl _, fun _ _ => rfl⟩
    simp [updateRegistryEntryElectra, liftAccessor, found, eligible, eject, ready,
      Except.mapError, bind, Except.bind, pure, Except.pure]

/-- The cost of the exits not yet started is their cost at every position of the registry. -/
private theorem exitCost_eq_exitCostAt (state : BeaconState preset fork) :
    exitCost preset state = exitCostAt state (List.range state.validators.data.size) := by
  have filtered : ∀ validators : List Validator,
      ((validators.filter (·.exitEpoch = FAR_FUTURE_EPOCH)).map fun validator =>
        validator.effectiveBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1).sum =
      (validators.map (exitCostOf preset)).sum := by
    intro validators
    induction validators with
    | nil => rfl
    | cons validator rest ih =>
      by_cases far : validator.exitEpoch = FAR_FUTURE_EPOCH <;>
        simp [far, exitCostOf, ih]
  unfold exitCost exitCostAt
  rw [filtered]
  congr 1
  apply List.ext_getElem
  · simp
  · intro position first second
    simp [Array.getElem?_eq_getElem (by simpa using first)]

/-- The cost at some positions splits into the cost at the first one and the rest. -/
private theorem exitCostAt_cons (state : BeaconState preset fork) (index : Nat)
    (rest : List Nat) :
    exitCostAt state (index :: rest) = exitCostAt state [index] + exitCostAt state rest := by
  simp [exitCostAt]

/-- The cost at one of some positions is at most their cost. -/
private theorem exitCostAt_single_le {state : BeaconState preset fork} {index : Nat}
    {indices : List Nat} (member : index ∈ indices) :
    exitCostAt state [index] ≤ exitCostAt state indices := by
  simp only [exitCostAt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  exact List.le_sum_of_mem (List.mem_map_of_mem member)

/-- A change at one of some distinct positions moves their cost by the change there. -/
private theorem exitCostAt_update {state other : BeaconState preset fork} {index : Nat}
    (same : ∀ position, position ≠ index →
      other.validators.data[position]? = state.validators.data[position]?) :
    ∀ {indices : List Nat}, indices.Nodup → index ∈ indices →
      exitCostAt other indices + exitCostAt state [index] =
        exitCostAt state indices + exitCostAt other [index]
  | [], _, member => absurd member List.not_mem_nil
  | position :: rest, distinct, member => by
    obtain ⟨absent, distinct⟩ := List.nodup_cons.mp distinct
    rw [exitCostAt_cons other position rest, exitCostAt_cons state position rest]
    by_cases equal : position = index
    · subst equal
      have kept : exitCostAt other rest = exitCostAt state rest := by
        unfold exitCostAt
        congr 1
        exact List.map_congr_left fun later inRest => by
          rw [same later fun equal => absent (equal ▸ inRest)]
      omega
    · have inRest : index ∈ rest := by
        rcases List.mem_cons.mp member with equal' | inRest
        · exact absurd equal'.symm equal
        · exact inRest
      have here : exitCostAt other [position] = exitCostAt state [position] := by
        simp only [exitCostAt, List.map_cons, List.map_nil, same position equal]
      have := exitCostAt_update same distinct inRest
      omega

/-- The pass from Electra keeps the bounds, and never raises the bound plus the cost still owed.

The cost is counted over a fixed list of distinct positions that holds the positions visited. -/
private theorem foldlM_updateRegistryEntryElectra_kept {config : Config}
    {electra : .pectra ≤ fork} {start : BeaconState preset fork} {activationEpoch : Epoch}
    {positions : List Nat} (distinct : positions.Nodup)
    (within : start.RegistryWithinLimit) (summed : effectiveBalanceSum start < 2 ^ 64)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT)
    (minimum : preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA)
    (maximum :
      preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT)
    (carried : (start.exitBalanceToConsume electra).toNat + 3 * exitChurnCeiling config start <
      2 ^ 64) :
    ∀ (indices : List Nat) (state : BeaconState preset fork) (bound : Nat),
      (∀ index ∈ indices, index < state.validators.data.size ∧ index ∈ positions) →
      (getCurrentEpoch start).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ bound →
      Kept config electra start state bound →
      bound + exitCostAt state positions + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat <
        2 ^ 64 - 1 →
      ∃ after, indices.foldlM (updateRegistryEntryElectra config activationEpoch) state =
          .ok after ∧ ∃ later, Kept config electra start after later ∧
        later + exitCostAt after positions ≤ bound + exitCostAt state positions
  | [], state, bound, _, _, kept, _ => ⟨state, rfl, bound, kept, Nat.le_refl _⟩
  | index :: rest, state, bound, inside, first, kept, room => by
    obtain ⟨inside', member⟩ := inside index List.mem_cons_self
    have single := exitCostAt_single_le (state := state) member
    rw [exitCostAt_single inside'] at single
    obtain ⟨middle, step, middleBound, grown, middleKept, potential, others⟩ :=
      updateRegistryEntryElectra_kept (activationEpoch := activationEpoch) within summed
        increment minimum maximum first carried kept inside' (by omega)
    have moved := exitCostAt_update others distinct member
    obtain ⟨after, folded, later, afterKept, afterPotential⟩ :=
      foldlM_updateRegistryEntryElectra_kept distinct (activationEpoch := activationEpoch)
        within summed increment minimum maximum carried rest middle middleBound
        (fun other inRest => by
          obtain ⟨below, inPositions⟩ := inside other (List.mem_cons_of_mem _ inRest)
          exact ⟨by rw [middleKept.size, ← kept.size]; exact below, inPositions⟩)
        (by omega) middleKept (by omega)
    refine ⟨after, ?_, later, afterKept, by omega⟩
    simp only [List.foldlM_cons, step, folded, bind, Except.bind]

/-- From Electra, registry updates succeed under a ceiling on the exit queue and room above it.

The registry must be within its limit, and the sum of its effective balances below `2^64`.

The increment must be positive.

The least churn and the largest shared churn must each be at least one increment.

A ceiling bounds the first epoch an exit may take, the end of the exit queue, and each exit epoch.

Add to the ceiling the cost of the exits not yet started, and the withdrawability delay.

The sum must stay below the far future epoch, so that no new exit lands on it.

The churn left over plus three churn bounds must fit too.

After the step, the end of the queue plus the cost still owed is at most a sum.

That sum is the ceiling plus the cost before the step.

The same holds for each exit epoch.

After the step, the churn left over is at most the larger of the one before and one churn bound.

The step keeps the slot, the balances and every effective balance. -/
theorem processRegistryUpdates_total_of_electra {config : Config}
    (state : BeaconState preset fork) (electra : .pectra ≤ fork)
    (within : state.RegistryWithinLimit) (summed : effectiveBalanceSum state < 2 ^ 64)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT)
    (minimum : preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA)
    (maximum :
      preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT)
    (ceiling : Nat)
    (first : (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ ceiling)
    (queued : (state.earliestExitEpoch electra).toNat ≤ ceiling)
    (exits : ∀ validator ∈ state.validators.data, validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
      validator.exitEpoch.toNat ≤ ceiling)
    (room : ceiling + exitCost preset state + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat <
      2 ^ 64 - 1)
    (carried : (state.exitBalanceToConsume electra).toNat + 3 * exitChurnCeiling config state <
      2 ^ 64) :
    ∃ after, processRegistryUpdates config state = .ok after ∧
      (after.earliestExitEpoch electra).toNat + exitCost preset after ≤
        ceiling + exitCost preset state ∧
      (∀ validator ∈ after.validators.data, validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
        validator.exitEpoch.toNat + exitCost preset after ≤ ceiling + exitCost preset state) ∧
      (after.exitBalanceToConsume electra).toNat ≤
        max (state.exitBalanceToConsume electra).toNat (exitChurnCeiling config state) ∧
      after.slot = state.slot ∧ after.balances = state.balances ∧
      after.validators.data.map (·.effectiveBalance) =
        state.validators.data.map (·.effectiveBalance) := by
  let activationEpoch :=
    ((getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat).toUInt64
  have activationOk :
      computeActivationExitEpoch preset (getCurrentEpoch state) = .ok activationEpoch :=
    computeActivationExitEpoch_ok_iff.mpr ⟨by omega, by
      change (_ % 2 ^ 64) = _
      exact Nat.mod_eq_of_lt (by omega)⟩
  have kept : Kept config electra state state ceiling :=
    ⟨rfl, rfl, rfl, queued, exits, Nat.le_max_left _ _⟩
  rw [exitCost_eq_exitCostAt] at room
  obtain ⟨after, folded, later, afterKept, potential⟩ :=
    foldlM_updateRegistryEntryElectra_kept (activationEpoch := activationEpoch)
      List.nodup_range within summed increment minimum maximum carried
      (List.range state.validators.data.size) state ceiling
      (fun _ member => ⟨List.mem_range.mp member, member⟩) first kept room
  have size := afterKept.size
  obtain ⟨slot, balances, effective, earliest, afterExits, left⟩ := afterKept
  have owed : exitCost preset after = exitCostAt after (List.range state.validators.data.size) :=
    by rw [exitCost_eq_exitCostAt after, size]
  rw [exitCost_eq_exitCostAt state]
  refine ⟨after, ?_, by omega, fun validator member finite => ?_, left, slot, balances,
    effective⟩
  · simp only [processRegistryUpdates, electra, ↓reduceIte, liftAccessor, liftArith,
      activationOk, Except.mapError, bind, Except.bind]
    exact folded
  · have := afterExits validator member finite
    omega

end EthLib.Consensus
