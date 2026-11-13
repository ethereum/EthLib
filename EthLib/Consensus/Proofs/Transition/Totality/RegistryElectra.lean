module

public import EthLib.Consensus.Proofs.Transition.Totality.Bound
public import EthLib.Consensus.Proofs.Transition.Totality.Registry

/-!
# Proofs: registry updates from Electra succeed

From Electra one pass over the registry queues, ejects and activates validators.

An ejection starts an exit, which takes its place in a queue of balance.

The queue spends a churn of balance each epoch, which is at least one increment.

So an exit moves the end of the queue by at most its effective balance in increments, plus one.

Only a validator that has not started to exit can start, so the moves add up to a fixed cost.

A ceiling on the end of the queue and on the exit epochs, plus that cost, then bounds them after.

The churn left over is below one churn of an epoch, which a share of the effective balances bounds.

Room for these bounds excludes every checked overflow.

The step keeps the slot, the balances and every effective balance.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork}

/-- The most epochs by which the exits not yet started can move the end of the exit queue.

Each validator without an exit epoch counts its effective balance in increments, plus one. -/
def exitCost (preset : Preset) (state : BeaconState preset fork) : Nat :=
  ((state.validators.data.toList.filter (·.exitEpoch = FAR_FUTURE_EPOCH)).map fun validator =>
    validator.effectiveBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1).sum

/-- A bound on the churn of exits of an epoch: the least churn plus the effective balances. -/
def exitChurnCeiling (config : Config) (state : BeaconState preset fork) : Nat :=
  config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat + effectiveBalanceSum state +
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat

/-- The queue succeeds when its churn is positive and an amount plus one churn fits.

The epoch it opens plus the amount in churns, plus one, must fit too. -/
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

/-- A share of a total, at least the least churn and rounded down, lies between two bounds.

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
  have rounded (amount : Gwei) : (roundToIncrement preset amount).toNat =
      amount.toNat - amount.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    unfold roundToIncrement
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
      rw [UInt64.toNat_mod]
      exact Nat.mod_le _ _)), UInt64.toNat_mod]
  rw [rounded, toNat_max, UInt64.toNat_div]
  have positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat := UInt64.lt_iff_toNat_lt.mp increment
  have minimum := UInt64.le_iff_toNat_le.mp minimum
  have share := Nat.div_le_self total.toNat quotient.toNat
  have amountLower : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat (total.toNat / quotient.toNat) := by
    omega
  have amountUpper : max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
      (total.toNat / quotient.toNat) ≤ config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat + total.toNat := by
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
  have totalLe : total.toNat ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat + effectiveBalanceSum state := by
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

/-- Epochs of a churn at least one increment, that an amount fills but for less than one churn.

There are at most the amount in increments, plus one. -/
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
    {start state : BeaconState preset fork} {bound : Nat} (kept : Kept config electra start state bound) :
    state.validators.data.size = start.validators.data.size := by
  have := congrArg Array.size kept.2.2.1
  simpa using this

/-- A state that keeps the effective balances of the start keeps their sum. -/
private theorem Kept.sum {config : Config} {electra : .pectra ≤ fork}
    {start state : BeaconState preset fork} {bound : Nat} (kept : Kept config electra start state bound) :
    effectiveBalanceSum state = effectiveBalanceSum start := by
  unfold effectiveBalanceSum
  have := congrArg (fun data => (data.toList.map UInt64.toNat).sum) kept.2.2.1
  simpa [List.map_map, Function.comp_def] using this

/-- A state that keeps the slot of the start keeps its current epoch. -/
private theorem Kept.epoch {config : Config} {electra : .pectra ≤ fork}
    {start state : BeaconState preset fork} {bound : Nat} (kept : Kept config electra start state bound) :
    getCurrentEpoch state = getCurrentEpoch start := by
  simp [getCurrentEpoch, kept.1]

/-- An exit of an amount up to the sum of the effective balances spends churn within the bounds.

It moves the end of the queue by at most the amount in increments, plus one.

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
      left.toNat ≤ max (start.exitBalanceToConsume electra).toNat (exitChurnCeiling config start) := by
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
  refine ⟨epoch, left, ?_, ?_, ?_⟩
  · simp only [computeExitEpochAndUpdateChurn, firstOk, churnOk, queueOk, liftArith,
      Except.mapError, bind, Except.bind, pure, Except.pure]
  · sorry
  · sorry

/-- From Electra, registry updates succeed under a ceiling on the exit queue and room above it.

The registry must be within its limit, and the sum of its effective balances below `2^64`.

The increment must be positive, and the least churn and the largest shared churn at least one.

A ceiling bounds the first epoch an exit may take, the end of the exit queue, and each exit epoch.

The ceiling plus the cost of the exits not yet started, plus the withdrawability delay, must fit.

The churn left over plus three churn bounds must fit too.

The end of the queue and each exit epoch after it are then at most the ceiling plus that cost.

The churn left over after it is at most the larger of the one before and one churn bound.

The step keeps the slot, the balances and every effective balance. -/
theorem processRegistryUpdates_total_of_electra {config : Config}
    (state : BeaconState preset fork) (electra : .pectra ≤ fork)
    (within : state.RegistryWithinLimit) (summed : effectiveBalanceSum state < 2 ^ 64)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT)
    (minimum : preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA)
    (maximum : preset.EFFECTIVE_BALANCE_INCREMENT ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT)
    (ceiling : Nat)
    (first : (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ ceiling)
    (queued : (state.earliestExitEpoch electra).toNat ≤ ceiling)
    (exits : ∀ validator ∈ state.validators.data, validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
      validator.exitEpoch.toNat ≤ ceiling)
    (room : ceiling + exitCost preset state + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat <
      2 ^ 64)
    (carried : (state.exitBalanceToConsume electra).toNat + 3 * exitChurnCeiling config state <
      2 ^ 64) :
    ∃ after, processRegistryUpdates config state = .ok after ∧
      (after.earliestExitEpoch electra).toNat ≤ ceiling + exitCost preset state ∧
      (∀ validator ∈ after.validators.data, validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
        validator.exitEpoch.toNat ≤ ceiling + exitCost preset state) ∧
      (after.exitBalanceToConsume electra).toNat ≤
        max (state.exitBalanceToConsume electra).toNat (exitChurnCeiling config state) ∧
      after.slot = state.slot ∧ after.balances = state.balances ∧
      after.validators.data.map (·.effectiveBalance) =
        state.validators.data.map (·.effectiveBalance) := by
  sorry

end EthLib.Consensus
