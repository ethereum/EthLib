module

public import EthLib.Consensus.Proofs.Transition.EpochRewards
public import EthLib.Consensus.Transition.EpochUpdates

/-!
# Proofs: the other steps of the epoch transition

An updated effective balance is the old one, or the balance rounded down to an increment and capped.

It is at most the balance plus the downward band of hysteresis.

It does not rise while the balance stays within the upward band of it.

Unless it is the old one, it is at most the balance and at most the largest.

So when the old effective balance is at most the largest, the updated one is too.

It is also at most the greater of the old effective balance and the balance.

The effective balances are aligned when each is a whole number of increments.

When the largest values of the preset are aligned too, the update keeps them aligned.

The registry updates, the slashings and the update of the effective balances keep the sizes.

When the slashings succeed, each balance of the registry loses its penalty if it is due.

That balance stops at zero.

From Electra this holds for a registry within its limit.

For a registry within its limit, the penalty is also expressed in natural numbers.

Successful checked products justify removing the modular reductions in that expression.

When the slashings succeed, the balances past the registry stay.

The slashings reset clears the slashed balance of the next epoch.

The RANDAO reset copies the mix of the current epoch to the next.

The rotation of the pending attestations moves those of the current epoch to the previous one.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-! ## Effective balances -/

/-- An updated effective balance is the old one, or the balance rounded down and capped. -/
theorem updatedEffectiveBalance_cases {largest balance effectiveBalance result : Gwei}
    (computed : updatedEffectiveBalance preset largest balance effectiveBalance = .ok result) :
    result = effectiveBalance ∨
      result = min (balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT) largest := by
  simp only [updatedEffectiveBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, leaves, _, rfl⟩ := computed
  cases leaves
  · exact .inl rfl
  · exact .inr rfl

/-- The downward band of hysteresis, in Gwei: a quarter of an increment on mainnet. -/
abbrev Preset.downwardBand (preset : Preset) : Nat :=
  (preset.EFFECTIVE_BALANCE_INCREMENT / preset.HYSTERESIS_QUOTIENT).toNat *
    preset.HYSTERESIS_DOWNWARD_MULTIPLIER.toNat

/-- The upward band of hysteresis, in Gwei: five quarters of an increment on mainnet. -/
abbrev Preset.upwardBand (preset : Preset) : Nat :=
  (preset.EFFECTIVE_BALANCE_INCREMENT / preset.HYSTERESIS_QUOTIENT).toNat *
    preset.HYSTERESIS_UPWARD_MULTIPLIER.toNat

/-- A successful update either keeps the old value inside the band, or leaves the band.

Inside the band, the balance is at most the old value plus the upward band.

Also inside the band, the old value is at most the balance plus the downward band.

Outside the band, the result is the balance rounded down to an increment, at most the largest. -/
theorem updatedEffectiveBalance_split {largest balance effectiveBalance result : Gwei}
    (computed : updatedEffectiveBalance preset largest balance effectiveBalance = .ok result) :
    (result = effectiveBalance ∧
      balance.toNat ≤ effectiveBalance.toNat + preset.upwardBand ∧
      effectiveBalance.toNat ≤ balance.toNat + preset.downwardBand) ∨
    (result = min (balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT) largest ∧
      (balance.toNat + preset.downwardBand < effectiveBalance.toNat ∨
        effectiveBalance.toNat + preset.upwardBand < balance.toNat)) := by
  simp only [updatedEffectiveBalance, leavesBand, liftAccessor, liftArith, Except.mapError, bind,
    Except.bind, pure, Except.pure] at computed
  rcases hd : mulChecked (preset.EFFECTIVE_BALANCE_INCREMENT / preset.HYSTERESIS_QUOTIENT)
    preset.HYSTERESIS_DOWNWARD_MULTIPLIER with _ | down
  · simp [hd] at computed
  rcases hu : mulChecked (preset.EFFECTIVE_BALANCE_INCREMENT / preset.HYSTERESIS_QUOTIENT)
    preset.HYSTERESIS_UPWARD_MULTIPLIER with _ | up
  · simp [hd, hu] at computed
  have downNat := (mulChecked_ok_iff.mp hd).2
  have upNat := (mulChecked_ok_iff.mp hu).2
  simp [hd, hu] at computed
  have dBand : down.toNat = preset.downwardBand := downNat
  have uBand : up.toNat = preset.upwardBand := upNat
  rcases hs : addChecked balance down with _ | sum
  · simp [hs] at computed
  have sumNat := (addChecked_ok_iff.mp hs).2
  simp only [hs] at computed
  by_cases lt : sum < effectiveBalance
  · simp [lt] at computed
    have := UInt64.lt_iff_toNat_lt.mp lt
    exact .inr ⟨computed.symm, .inl (by omega)⟩
  · simp [lt] at computed
    rcases hs2 : addChecked effectiveBalance up with _ | sum2
    · simp [hs2] at computed
    have sum2Nat := (addChecked_ok_iff.mp hs2).2
    simp only [hs2] at computed
    have := Nat.not_lt.mp (fun h => lt (UInt64.lt_iff_toNat_lt.mpr h))
    by_cases lt2 : sum2 < balance
    · simp [lt2] at computed
      have := UInt64.lt_iff_toNat_lt.mp lt2
      exact .inr ⟨computed.symm, .inr (by omega)⟩
    · simp [lt2] at computed
      have := Nat.not_lt.mp (fun h => lt2 (UInt64.lt_iff_toNat_lt.mpr h))
      exact .inl ⟨computed.symm, by omega, by omega⟩

/-- The balance rounded down to an increment is that balance less the remainder. -/
private theorem toNat_rounded {balance : Gwei} :
    (balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT).toNat =
      balance.toNat - balance.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  have le : balance % preset.EFFECTIVE_BALANCE_INCREMENT ≤ balance :=
    UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_mod]; exact Nat.mod_le _ _)
  rw [UInt64.toNat_sub_of_le _ _ le, UInt64.toNat_mod]

/-- The rounded balance capped at the largest is either the rounded balance or the largest. -/
private theorem toNat_min_rounded {balance largest : Gwei} :
    (min (balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT) largest).toNat =
      min (balance.toNat - balance.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
        largest.toNat := by
  rw [UInt64.min_def, ← toNat_rounded (preset := preset)]
  split
  · rename_i h
    rw [Nat.min_eq_left (UInt64.le_iff_toNat_le.mp h)]
  · rename_i h
    rw [Nat.min_eq_right (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h)))]

/-- An updated effective balance is the old one, or at most both the balance and the largest. -/
theorem updatedEffectiveBalance_eq_or_le {largest balance effectiveBalance result : Gwei}
    (computed : updatedEffectiveBalance preset largest balance effectiveBalance = .ok result) :
    result = effectiveBalance ∨ result ≤ balance ∧ result ≤ largest := by
  rcases updatedEffectiveBalance_cases computed with rfl | rfl
  · exact .inl rfl
  · right
    rw [UInt64.le_iff_toNat_le, UInt64.le_iff_toNat_le, toNat_min_rounded (preset := preset)]
    exact ⟨Nat.le_trans (Nat.min_le_left _ _) (Nat.sub_le _ _), Nat.min_le_right _ _⟩

/-- An updated effective balance is at most the largest when the old one is. -/
theorem updatedEffectiveBalance_le_largest {largest balance effectiveBalance result : Gwei}
    (old : effectiveBalance ≤ largest)
    (computed : updatedEffectiveBalance preset largest balance effectiveBalance = .ok result) :
    result ≤ largest := by
  rcases updatedEffectiveBalance_eq_or_le computed with rfl | ⟨_, capped⟩
  · exact old
  · exact capped

/-- An updated effective balance is at most the greater of the old one and the balance.

A kept old effective balance can exceed the balance, so the bound needs both values. -/
theorem updatedEffectiveBalance_le_max {largest balance effectiveBalance result : Gwei}
    (computed : updatedEffectiveBalance preset largest balance effectiveBalance = .ok result) :
    result.toNat ≤ max effectiveBalance.toNat balance.toNat := by
  rcases updatedEffectiveBalance_eq_or_le computed with rfl | ⟨below, _⟩
  · exact Nat.le_max_left _ _
  · exact Nat.le_trans (UInt64.le_iff_toNat_le.mp below) (Nat.le_max_right _ _)

/-- The increment of a preset is positive and at most its upward band, as the hysteresis needs. -/
abbrev Preset.IncrementWithinUpwardBand (preset : Preset) : Prop :=
  0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∧
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ preset.upwardBand

/-- An updated effective balance is at most the balance plus the downward band. -/
theorem updatedEffectiveBalance_le_add {largest balance effectiveBalance result : Gwei}
    (computed : updatedEffectiveBalance preset largest balance effectiveBalance = .ok result) :
    result.toNat ≤ balance.toNat + preset.downwardBand := by
  rcases updatedEffectiveBalance_split computed with ⟨rfl, _, below⟩ | ⟨rfl, _⟩
  · exact below
  · rw [toNat_min_rounded (preset := preset)]
    have := Nat.mod_le balance.toNat preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    have := Nat.min_le_left
      (balance.toNat - balance.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) largest.toNat
    omega

/-- An updated effective balance is at most the old one in two cases.

The balance may be at most the old one plus the upward band.

Or the old one may already be at least the largest. -/
theorem updatedEffectiveBalance_le_of_band {largest balance effectiveBalance result : Gwei}
    (band : balance.toNat ≤ effectiveBalance.toNat + preset.upwardBand ∨
      largest ≤ effectiveBalance)
    (computed : updatedEffectiveBalance preset largest balance effectiveBalance = .ok result) :
    result ≤ effectiveBalance := by
  rcases updatedEffectiveBalance_split computed with ⟨rfl, _⟩ | ⟨rfl, out⟩
  · exact UInt64.le_refl _
  · rw [UInt64.le_iff_toNat_le, toNat_min_rounded (preset := preset)]
    have := Nat.mod_le balance.toNat preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    have := Nat.min_le_left
      (balance.toNat - balance.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) largest.toNat
    have := Nat.min_le_right
      (balance.toNat - balance.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) largest.toNat
    rcases band with band | big
    · omega
    · have := UInt64.le_iff_toNat_le.mp big
      omega

/-- After an update, the balance is at most the new effective balance plus the upward band.

Otherwise the new effective balance is at least the largest.

The increment must be positive and at most the upward band. -/
theorem updatedEffectiveBalance_band {largest balance effectiveBalance result : Gwei}
    (bands : preset.IncrementWithinUpwardBand)
    (computed : updatedEffectiveBalance preset largest balance effectiveBalance = .ok result) :
    balance.toNat ≤ result.toNat + preset.upwardBand ∨ largest ≤ result := by
  obtain ⟨positive, narrow⟩ := bands
  rcases updatedEffectiveBalance_split computed with ⟨rfl, inside, _⟩ | ⟨rfl, _⟩
  · exact .inl inside
  · rw [UInt64.le_iff_toNat_le, toNat_min_rounded (preset := preset)]
    have := Nat.mod_lt balance.toNat positive
    have := Nat.min_le_left
      (balance.toNat - balance.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) largest.toNat
    rcases Nat.le_total largest.toNat
      (balance.toNat - balance.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) with le | le
    · right
      have := Nat.min_eq_right le
      omega
    · left
      have := Nat.min_eq_left le
      omega

/-- The increment of the mainnet preset is positive and at most its upward band. -/
theorem Preset.incrementWithinUpwardBand_mainnet : Preset.mainnet.IncrementWithinUpwardBand := by
  decide

/-- The increment of the minimal preset is positive and at most its upward band. -/
theorem Preset.incrementWithinUpwardBand_minimal : Preset.minimal.IncrementWithinUpwardBand := by
  decide

/-- An updated effective balance is aligned when the old one and the largest are. -/
theorem updatedEffectiveBalance_aligned {largest balance effectiveBalance result : Gwei}
    (maxAligned : largest % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (old : effectiveBalance % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (computed : updatedEffectiveBalance preset largest balance effectiveBalance = .ok result) :
    result % preset.EFFECTIVE_BALANCE_INCREMENT = 0 := by
  rcases updatedEffectiveBalance_cases computed with rfl | rfl
  · exact old
  · exact min_sub_mod_mod_self _ maxAligned

/-- An aligned validator written at a plain position keeps the effective balances aligned. -/
theorem effectiveBalancesAligned_setValidatorAt {index : Nat} {validator : Validator}
    (holds : EffectiveBalancesAligned state)
    (good : validator.effectiveBalance % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (set : state.setValidatorAt index validator = .ok after) :
    EffectiveBalancesAligned after := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  intro other member
  simp only [BeaconState.putValidator, RootedForkList.data_set] at member
  rcases Array.mem_or_eq_of_mem_set (w := inside) member with old | rfl
  · exact holds other old
  · exact good

/-- Replacing a validator by an aligned one keeps the effective balances aligned. -/
theorem effectiveBalancesAligned_setValidator {index : ValidatorIndex} {validator : Validator}
    (holds : EffectiveBalancesAligned state)
    (good : validator.effectiveBalance % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (set : state.setValidator index validator = .ok after) :
    EffectiveBalancesAligned after :=
  effectiveBalancesAligned_setValidatorAt holds good (by rwa [← setValidator_eq_setValidatorAt])

/-- The update of one effective balance keeps them aligned.

The largest effective balances of the preset must be whole numbers of increments. -/
theorem updateEffectiveBalance_aligned {index : Nat}
    (maxAligned : MaxEffectiveBalancesAligned preset)
    (holds : EffectiveBalancesAligned state)
    (computed : updateEffectiveBalance state index = .ok after) :
    EffectiveBalancesAligned after := by
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, _, _, effectiveBalance, updated, set⟩ := computed
  refine effectiveBalancesAligned_setValidatorAt holds ?_ set
  apply updatedEffectiveBalance_aligned (withdrawalMaxEffectiveBalance_aligned maxAligned validator)
    _ updated
  exact holds _ (mem_of_getValidatorAt found)

/-- The update of the effective balances keeps them aligned.

The largest effective balances of the preset must be whole numbers of increments. -/
theorem processEffectiveBalanceUpdates_aligned
    (maxAligned : MaxEffectiveBalancesAligned preset)
    (holds : EffectiveBalancesAligned state)
    (computed : processEffectiveBalanceUpdates state = .ok after) :
    EffectiveBalancesAligned after := by
  unfold processEffectiveBalanceUpdates at computed
  exact foldlM_ok_invariant EffectiveBalancesAligned
    (fun _ _ _ before step => updateEffectiveBalance_aligned maxAligned before step) holds
    computed

/-- The update of one effective balance keeps the sizes. -/
theorem sameSizes_updateEffectiveBalance {index : Nat}
    (computed : updateEffectiveBalance state index = .ok after) : SameSizes state after := by
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, set⟩ := computed
  exact sameSizes_setValidatorAt set

theorem sameSizes_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) : SameSizes state after := by
  unfold processEffectiveBalanceUpdates at computed
  exact foldlM_ok_invariant (SameSizes state)
    (fun _ _ _ sizes step => sizes.trans (sameSizes_updateEffectiveBalance step))
    (SameSizes.refl state) computed

/-! ## Registry updates and slashings -/

theorem sameSizes_updateRegistryEntry {config : Config} {index : Nat}
    (computed : updateRegistryEntry config state index = .ok after) : SameSizes state after := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, set, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, exited⟩ := computed
    exact (sameSizes_setValidatorAt set).trans (sameSizes_initiateValidatorExit exited)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ sameSizes_setValidatorAt set

theorem sameSizes_activateValidator {index : ValidatorIndex}
    (computed : activateValidator state index = .ok after) : SameSizes state after := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, set⟩ := computed
  exact sameSizes_setValidator set

/-- The activation churn limit is at most the configured maximum and the validator churn limit. -/
theorem getValidatorActivationChurnLimit_le {config : Config} :
    getValidatorActivationChurnLimit config state ≤ config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT ∧
      getValidatorActivationChurnLimit config state ≤ getValidatorChurnLimit config state :=
  ⟨Std.min_le_left, Std.min_le_right⟩

/-- The activation epoch at an index, or the accessor error outside the registry. -/
def activationEpochAt (state : BeaconState preset fork) (index : ValidatorIndex) :
    Except AccessorError Epoch :=
  (getValidator state index).map (·.activationEpoch)

/-- A write of one validator leaves every other activation epoch unchanged. -/
theorem activationEpochAt_setValidator {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after) (other : ValidatorIndex) :
    activationEpochAt after other =
      if other = index then .ok validator.activationEpoch else activationEpochAt state other := by
  by_cases equal : other = index
  · subst other
    simp [activationEpochAt, getValidator_setValidator_self set, Except.map]
  · simp [activationEpochAt, getValidator_setValidator_of_ne set equal, equal]

/-- A write at a plain position leaves every other activation epoch unchanged. -/
theorem activationEpochAt_setValidatorAt {index : Nat} {validator : Validator}
    (set : state.setValidatorAt index validator = .ok after) (other : ValidatorIndex) :
    activationEpochAt after other =
      if other.toNat = index then .ok validator.activationEpoch
      else activationEpochAt state other := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  by_cases equal : other.toNat = index
  · simp [activationEpochAt, getValidator, BeaconState.putValidator, equal, inside, Except.map]
  · simp [activationEpochAt, getValidator, BeaconState.putValidator, equal, Ne.symm equal,
      Except.map]

/-- In a registry within its limit, a queued index has the far-future activation epoch. -/
theorem activationEpochAt_of_mem_activationQueue (within : state.RegistryWithinLimit)
    {index : ValidatorIndex} (member : index ∈ activationQueue state) :
    activationEpochAt state index = .ok FAR_FUTURE_EPOCH := by
  simp only [activationQueue, List.mem_map] at member
  obtain ⟨⟨eligibility, found⟩, sorted, rfl⟩ := member
  have inEligible := (List.mergeSort_perm _ _).mem_iff.mp sorted
  simp only [List.mem_filterMap, Option.ite_none_right_eq_some, Option.some.injEq,
    List.mem_zipIdx_iff_getElem?, Prod.exists, Prod.mk.injEq] at inEligible
  obtain ⟨validator, i, atI, eligible, -, rfl⟩ := inEligible
  have lt : i < state.validators.data.size := by
    have := (List.getElem?_eq_some_iff.mp atI).1
    simpa using this
  -- The queue holds only validators whose activation epoch is still the far future.
  simp only [isEligibleForActivation, Bool.and_eq_true, beq_iff_eq] at eligible
  simp only [activationEpochAt, getValidator, toNat_toUInt64_of_lt within lt]
  simp only [Array.getElem?_toList] at atI
  simp only [atI]
  exact congrArg Except.ok eligible.2

/-- Starting an exit keeps the slot and all activation epochs, at every fork. -/
theorem initiateValidatorExit_activationEpochs {config : Config} {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) :
    after.slot = state.slot ∧
      ∀ other, activationEpochAt after other = activationEpochAt state other := by
  obtain ⟨validator, found, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact ⟨rfl, fun _ => rfl⟩
  -- The exit queue changes neither the registry nor the slot, before Electra or from it.
  have same : queued.validators = state.validators ∧ queued.slot = state.slot := by
    unfold exitQueue at queue
    split at queue
    · simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq, Prod.mk.injEq] at queue
      obtain ⟨_, _, _, _, _, _, rfl, _⟩ := queue
      exact ⟨rfl, rfl⟩
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at queue
      obtain ⟨_, _, rfl, _⟩ := queue
      exact ⟨rfl, rfl⟩
  refine ⟨(setValidator_slot set).trans same.2, fun other => ?_⟩
  rw [activationEpochAt_setValidator set]
  split
  · rename_i equal
    subst other
    simp [activationEpochAt, Except.map, getValidator] at found ⊢
    simp [found]
  · simp [activationEpochAt, getValidator, same.1]

/-- The registry step of one validator used before Electra keeps the slot and activation epochs.

This holds for any fork value. -/
theorem updateRegistryEntry_activationEpochs {config : Config} {index : Nat}
    (computed : updateRegistryEntry config state index = .ok after) :
    after.slot = state.slot ∧
      ∀ other, activationEpochAt after other = activationEpochAt state other := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, queued, joined, middle, set, rest⟩ := computed
  -- Joining the queue changes eligibility, not the activation epoch.
  have kept : queued.activationEpoch = validator.activationEpoch := by
    unfold queueForActivation at joined
    split at joined
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at joined
      obtain ⟨_, _, rfl⟩ := joined
      rfl
    · cases joined
      rfl
  have first : ∀ other, activationEpochAt middle other = activationEpochAt state other := by
    intro other
    rw [activationEpochAt_setValidatorAt set]
    split
    · rename_i equal
      simp [activationEpochAt, getValidator, equal, getValidatorAt_eq_ok_iff.mp found,
        kept, Except.map]
    · rfl
  have markedSlot : middle.slot = state.slot := by
    obtain ⟨_, rfl⟩ := setValidatorAt_ok set
    rfl
  split at rest
  · simp only [bind_ok_iff, liftAccessor_ok] at rest
    obtain ⟨_, _, exited⟩ := rest
    obtain ⟨slot, epochs⟩ := initiateValidatorExit_activationEpochs exited
    exact ⟨slot.trans markedSlot, fun other => (epochs other).trans (first other)⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at rest
    subst after
    exact ⟨markedSlot, first⟩

/-- Activating one validator writes the computed epoch, and keeps the slot and the other epochs. -/
theorem activateValidator_activationEpochs {index : ValidatorIndex}
    (computed : activateValidator state index = .ok after) :
    ∃ epoch, computeActivationExitEpoch preset (getCurrentEpoch state) = .ok epoch ∧
      after.slot = state.slot ∧
      ∀ other, activationEpochAt after other =
        if other = index then .ok epoch else activationEpochAt state other := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff] at computed
  obtain ⟨_, _, epoch, calculated, set⟩ := computed
  exact ⟨epoch, calculated, setValidator_slot set, activationEpochAt_setValidator set⟩

/-- A successful activation pass writes the computed epoch at its selected indices.

With no selected index the computation need not succeed, since the pass never calls it. -/
theorem foldlM_activateValidator_activationEpochs {indices : List ValidatorIndex}
    (computed : indices.foldlM activateValidator state = .ok after) :
    after.slot = state.slot ∧
      (∀ other, other ∉ indices → activationEpochAt after other = activationEpochAt state other) ∧
      (∀ other, other ∈ indices → ∃ epoch,
        computeActivationExitEpoch preset (getCurrentEpoch state) = .ok epoch ∧
          activationEpochAt after other = .ok epoch) := by
  induction indices generalizing state with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst after
    exact ⟨rfl, fun _ _ => rfl, by simp⟩
  | cons index indices ih =>
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, step, rest⟩ := computed
    obtain ⟨epoch, calculated, slot, epochs⟩ := activateValidator_activationEpochs step
    obtain ⟨lastSlot, unchanged, selected⟩ := ih rest
    have current : getCurrentEpoch middle = getCurrentEpoch state := by
      simp [getCurrentEpoch, slot]
    refine ⟨lastSlot.trans slot, ?_, ?_⟩
    · intro other outside
      have ne : other ≠ index := fun equal => outside (by simp [equal])
      rw [unchanged other (fun member => outside (by simp [member])), epochs other,
        ite_eq_right ne]
    · intro other member
      -- A later write wins, and the unchanged slot makes its computed epoch the same.
      by_cases tail : other ∈ indices
      · obtain ⟨value, valueOk, written⟩ := selected other tail
        exact ⟨value, current ▸ valueOk, written⟩
      · have equal : other = index := (List.mem_cons.mp member).resolve_right tail
        subst other
        exact ⟨epoch, calculated, by rw [unchanged index tail, epochs index, ite_eq_left rfl]⟩

/-- Before Electra, the registry writes activation epochs only in a bounded queue prefix.

The queue and the limit are read after the first pass, as the step reads them.

The queue sorts by eligibility epoch, then by validator index.

Before Deneb the limit is the validator churn limit; from Deneb it is capped, as [EIP-7514] says.

Each selected validator had the far-future activation epoch, 2^64 - 1, before the step.

With an empty prefix, the step does not compute an activation epoch at all.

[EIP-7514]: https://eips.ethereum.org/EIPS/eip-7514#specification
-/
theorem processRegistryUpdates_activationEpochs {config : Config}
    (before : fork < .pectra)
    (computed : processRegistryUpdates config state = .ok after) :
    ∃ updated : BeaconState preset fork,
      (List.range state.validators.data.size).foldlM (updateRegistryEntry config) state =
        .ok updated ∧
      let limit := if .dencun ≤ fork then getValidatorActivationChurnLimit config updated
        else getValidatorChurnLimit config updated
      let selected := (activationQueue updated).take limit.toNat
      selected.length ≤ limit.toNat ∧
      limit ≤ getValidatorChurnLimit config updated ∧
      (.dencun ≤ fork → limit ≤ config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT) ∧
      (∀ index, index ∉ selected →
        activationEpochAt after index = activationEpochAt state index) ∧
      (∀ index, index ∈ selected → ∃ epoch,
        computeActivationExitEpoch preset (getCurrentEpoch state) = .ok epoch ∧
          activationEpochAt after index = .ok epoch) ∧
      (∀ index, index ∈ selected → activationEpochAt state index = .ok FAR_FUTURE_EPOCH) := by
  have notElectra : ¬Fork.pectra ≤ fork := Nat.not_le_of_lt before
  simp only [processRegistryUpdates, notElectra, ↓reduceIte, bind_ok_iff] at computed
  obtain ⟨updated, first, last⟩ := computed
  -- The first pass leaves every input activation epoch and the current epoch unchanged.
  have kept := foldlM_ok_invariant
    (fun next : BeaconState preset fork => next.slot = state.slot ∧
      ∀ index, activationEpochAt next index = activationEpochAt state index)
    (fun _ _ _ holds step => by
      obtain ⟨slot, epochs⟩ := updateRegistryEntry_activationEpochs step
      exact ⟨slot.trans holds.1, fun index => (epochs index).trans (holds.2 index)⟩)
    ⟨rfl, fun _ => rfl⟩ first
  obtain ⟨_, unchanged, written⟩ := foldlM_activateValidator_activationEpochs last
  refine ⟨updated, first, List.length_take_le .., ?_, ?_, ?_, ?_, ?_⟩
  · split
    · exact (getValidatorActivationChurnLimit_le).2
    · exact UInt64.le_refl _
  · intro deneb
    simp only [deneb, ↓reduceIte]
    exact (getValidatorActivationChurnLimit_le).1
  · intro index outside
    exact (unchanged index outside).trans (kept.2 index)
  · intro index member
    obtain ⟨epoch, calculated, value⟩ := written index member
    refine ⟨epoch, ?_, value⟩
    simpa only [getCurrentEpoch, kept.1] using calculated
  · intro index member
    rw [← kept.2 index]
    exact activationEpochAt_of_mem_activationQueue
      (updated.validators.bound (Nat.lt_trans before (by decide))) (List.mem_of_mem_take member)

/-- Before Electra, the limit of activations bounds each list of distinct changed indices.

That limit is read after the first pass.

A changed index is one whose activation epoch differs after the step. -/
theorem processRegistryUpdates_changedActivationCount {config : Config}
    (before : fork < .pectra)
    (computed : processRegistryUpdates config state = .ok after) :
    ∃ updated : BeaconState preset fork,
      (List.range state.validators.data.size).foldlM (updateRegistryEntry config) state =
        .ok updated ∧
      let limit := if .dencun ≤ fork then getValidatorActivationChurnLimit config updated
        else getValidatorChurnLimit config updated
      ∀ changed : List ValidatorIndex, changed.Nodup →
        (∀ index ∈ changed, activationEpochAt after index ≠ activationEpochAt state index) →
        changed.length ≤ limit.toNat := by
  obtain ⟨updated, first, bounded, _, _, unchanged, _, _⟩ :=
    processRegistryUpdates_activationEpochs before computed
  refine ⟨updated, first, fun changed distinct differ => ?_⟩
  -- An index outside the prefix keeps its activation epoch, so each changed index is in it.
  refine Nat.le_trans (distinct.length_le_of_subset fun index member => ?_) bounded
  exact Classical.byContradiction fun outside => differ index member (unchanged index outside)

/-- Before Electra, unless the computed epoch is the far future, exactly the prefix changes.

That exception guards against an epoch that reaches 2^64 - 1, not a protocol condition. -/
theorem processRegistryUpdates_changedActivationEpochs_exact {config : Config}
    (before : fork < .pectra)
    (computed : processRegistryUpdates config state = .ok after) :
    ∃ updated : BeaconState preset fork,
      (List.range state.validators.data.size).foldlM (updateRegistryEntry config) state =
        .ok updated ∧
      let limit := if .dencun ≤ fork then getValidatorActivationChurnLimit config updated
        else getValidatorChurnLimit config updated
      let selected := (activationQueue updated).take limit.toNat
      ∀ epoch, computeActivationExitEpoch preset (getCurrentEpoch state) = .ok epoch →
        epoch ≠ FAR_FUTURE_EPOCH →
        ∀ index, activationEpochAt after index ≠ activationEpochAt state index ↔
          index ∈ selected := by
  obtain ⟨updated, first, _, _, _, unchanged, written, unactivated⟩ :=
    processRegistryUpdates_activationEpochs before computed
  refine ⟨updated, first, ?_⟩
  dsimp only
  intro epoch calculated finite index
  constructor
  · intro changed
    by_cases member : index ∈ (activationQueue updated).take
        (if .dencun ≤ fork then getValidatorActivationChurnLimit config updated
          else getValidatorChurnLimit config updated).toNat
    · exact member
    · exact False.elim (changed (unchanged index member))
  · intro member
    obtain ⟨value, valueOk, atIndex⟩ := written index member
    have equal : value = epoch := Except.ok.inj (valueOk.symm.trans calculated)
    rw [atIndex, equal, unactivated index member]
    exact fun same => finite (Except.ok.inj same)

theorem sameSizes_updateRegistryEntryElectra {config : Config} {activationEpoch : Epoch}
    {index : Nat}
    (computed : updateRegistryEntryElectra config activationEpoch state index = .ok after) :
    SameSizes state after := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, set⟩ := computed
    exact sameSizes_setValidatorAt set
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, exited⟩ := computed
    exact sameSizes_initiateValidatorExit exited
  split at computed
  · rw [liftAccessor_ok] at computed
    exact sameSizes_setValidatorAt computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ SameSizes.refl _

/-- The registry updates keep the sizes. -/
theorem sameSizes_processRegistryUpdates {config : Config}
    (computed : processRegistryUpdates config state = .ok after) : SameSizes state after := by
  unfold processRegistryUpdates at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, computed⟩ := computed
    exact foldlM_ok_invariant (SameSizes state)
      (fun _ _ _ sizes step => sizes.trans (sameSizes_updateRegistryEntryElectra step))
      (SameSizes.refl state) computed
  simp only [bind_ok_iff] at computed
  obtain ⟨updated, updatedOk, activated⟩ := computed
  have first := foldlM_ok_invariant (SameSizes state)
    (fun _ _ _ sizes step => sizes.trans (sameSizes_updateRegistryEntry step))
    (SameSizes.refl state) updatedOk
  exact foldlM_ok_invariant (SameSizes state)
    (fun _ _ _ sizes step => sizes.trans (sameSizes_activateValidator step)) first activated

theorem sameSizes_applySlashingPenalty {total adjusted : Gwei} {index : Nat}
    (computed : applySlashingPenalty state total adjusted index = .ok after) :
    SameSizes state after := by
  simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, _, _, _, _, lowered⟩ := computed
      exact sameSizes_decreaseBalance lowered
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ SameSizes.refl _
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ SameSizes.refl _

theorem sameSizes_applySlashingPenaltyElectra {perIncrement : Gwei} {index : Nat}
    (computed : applySlashingPenaltyElectra state perIncrement index = .ok after) :
    SameSizes state after := by
  simp only [applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, _, _, lowered⟩ := computed
      exact sameSizes_decreaseBalance lowered
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ SameSizes.refl _
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ SameSizes.refl _

/-- The slashings keep the sizes. -/
theorem sameSizes_processSlashings (computed : processSlashings state = .ok after) :
    SameSizes state after := by
  unfold processSlashings at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact foldlM_ok_invariant (SameSizes state)
      (fun _ _ _ sizes step => sizes.trans (sameSizes_applySlashingPenaltyElectra step))
      (SameSizes.refl state) applied
  · exact foldlM_ok_invariant (SameSizes state)
      (fun _ _ _ sizes step => sizes.trans (sameSizes_applySlashingPenalty step))
      (SameSizes.refl state) computed

/-! ## Balances after the slashings -/

/-- Whether the slashing penalty of a validator is due at an epoch.

It is due for a slashed validator halfway through its time before it may withdraw. -/
def SlashingPenaltyDue (preset : Preset) (epoch : Epoch) (validator : Validator) : Prop :=
  validator.slashed ∧ epoch + preset.EPOCHS_PER_SLASHINGS_VECTOR / 2 = validator.withdrawableEpoch

instance (preset : Preset) (epoch : Epoch) (validator : Validator) :
    Decidable (SlashingPenaltyDue preset epoch validator) := by
  unfold SlashingPenaltyDue
  infer_instance

/-- A step that either lowers one balance by a due penalty, or keeps the state when none is due.

The registry and the slot stay.

The balance at its position loses the penalty if it is due, stopping at zero.

The other balances stay. -/
private theorem slashingStep_balances {last next : BeaconState preset fork} {j : Nat}
    (small : j < 2 ^ 64) {validator : Validator} {penalty : Gwei}
    (found : getValidatorAt last j = .ok validator)
    (cases : (SlashingPenaltyDue preset (getCurrentEpoch last) validator ∧
        decreaseBalance last j.toUInt64 penalty = .ok next) ∨
      (¬ SlashingPenaltyDue preset (getCurrentEpoch last) validator ∧ next = last)) :
    next.validators = last.validators ∧ next.slot = last.slot ∧
      (last.validators.data[j]? = some validator ∧
        next.balances.data[j]? = last.balances.data[j]?.map fun balance =>
          if SlashingPenaltyDue preset (getCurrentEpoch last) validator then
            saturatingSub balance penalty
          else balance) ∧
      ∀ k, k ≠ j → next.balances.data[k]? = last.balances.data[k]? := by
  have same : j.toUInt64.toNat = j := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt small]
  have registered : last.validators.data[j]? = some validator := getValidatorAt_eq_ok_iff.mp found
  rcases cases with ⟨due, lowered⟩ | ⟨notDue, kept⟩
  · obtain ⟨inside, rfl⟩ := decreaseBalance_eq_ok_iff.mp lowered
    have inside' : j < last.balances.data.size := same ▸ inside
    refine ⟨rfl, rfl, ⟨registered, ?_⟩, fun k ne => ?_⟩
    · simp [BeaconState.putBalance, same, inside', due]
    · simp [BeaconState.putBalance, same, Ne.symm ne]
  · rw [kept]
    refine ⟨rfl, rfl, ⟨registered, ?_⟩, fun _ _ => rfl⟩
    cases last.balances.data[j]? <;> simp [notDue]

/-- The due test of a step is the test of a due penalty, once the validator is slashed. -/
private theorem slashingPenaltyDue_iff {state : BeaconState preset fork} {validator : Validator}
    {due : Epoch} (slashed : validator.slashed = true)
    (computed : liftAccessor (liftArith (addChecked (getCurrentEpoch state)
      (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2))) = .ok due) :
    SlashingPenaltyDue preset (getCurrentEpoch state) validator ↔
      due = validator.withdrawableEpoch := by
  rw [liftAccessor_ok, liftArith, mapError_ok_iff] at computed
  have sum := Except.ok.inj ((addChecked_of_lt (addChecked_ok_iff.mp computed).1).symm.trans
    computed)
  simp [SlashingPenaltyDue, slashed, sum]

/-- A successful due penalty before Electra checks both products before lowering the balance.

The first multiplies the effective-balance increment count by the adjusted slashed balance.

After division by the active balance, the second multiplies by the increment. -/
theorem applySlashingPenalty_no_overflow {total adjusted : Gwei} {j : Nat}
    {validator : Validator} (found : getValidatorAt state j = .ok validator)
    (due : SlashingPenaltyDue preset (getCurrentEpoch state) validator)
    (computed : applySlashingPenalty state total adjusted j = .ok after) :
    validator.effectiveBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        adjusted.toNat < 2 ^ 64 ∧
      (validator.effectiveBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        adjusted.toNat / total.toNat) * preset.EFFECTIVE_BALANCE_INCREMENT.toNat < 2 ^ 64 := by
  simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok, found,
    Except.ok.injEq] at computed
  obtain ⟨_, rfl, computed⟩ := computed
  simp only [due.1, ↓reduceIte, bind_ok_iff] at computed
  obtain ⟨epoch, epochOk, computed⟩ := computed
  have epochEq := (slashingPenaltyDue_iff due.1 epochOk).mp due
  simp only [epochEq, ↓reduceIte, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff] at computed
  obtain ⟨numerator, product, _, scaled, _⟩ := computed
  obtain ⟨fits, exact⟩ := mulChecked_ok_iff.mp product
  have scaledFits := (mulChecked_ok_iff.mp scaled).1
  rw [UInt64.toNat_div] at fits exact
  rw [UInt64.toNat_div, exact] at scaledFits
  exact ⟨fits, scaledFits⟩

/-- A successful due penalty from Electra checks the product of the per-increment penalty. -/
theorem applySlashingPenaltyElectra_no_overflow {perIncrement : Gwei} {j : Nat}
    {validator : Validator} (found : getValidatorAt state j = .ok validator)
    (due : SlashingPenaltyDue preset (getCurrentEpoch state) validator)
    (computed : applySlashingPenaltyElectra state perIncrement j = .ok after) :
    perIncrement.toNat *
      (validator.effectiveBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) < 2 ^ 64 := by
  simp only [applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok, found,
    Except.ok.injEq] at computed
  obtain ⟨_, rfl, computed⟩ := computed
  simp only [due.1, ↓reduceIte, bind_ok_iff] at computed
  obtain ⟨epoch, epochOk, computed⟩ := computed
  have epochEq := (slashingPenaltyDue_iff due.1 epochOk).mp due
  simp only [epochEq, ↓reduceIte, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff] at computed
  obtain ⟨_, product, _⟩ := computed
  simpa only [UInt64.toNat_div] using (mulChecked_ok_iff.mp product).1

/-- The penalty step used before Electra lowers the balance of one validator when it is due.

This holds when the step succeeds at a position below `2^64`.

The registry and the slot stay.

The validator at that position exists.

Its balance loses the penalty if it is due, stopping at zero.

The penalty is its effective balance in increments, times the given adjusted slashed balance.

That product is divided by the given active balance, then counted back in increments.

The other balances stay. -/
theorem applySlashingPenalty_balances {total adjusted : Gwei} {last next : BeaconState preset fork}
    {j : Nat} (small : j < 2 ^ 64)
    (computed : applySlashingPenalty last total adjusted j = .ok next) :
    next.validators = last.validators ∧ next.slot = last.slot ∧
      (∃ validator, last.validators.data[j]? = some validator ∧
        next.balances.data[j]? = last.balances.data[j]?.map fun balance =>
          if SlashingPenaltyDue preset (getCurrentEpoch last) validator then
            saturatingSub balance (validator.effectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT *
              adjusted / total * preset.EFFECTIVE_BALANCE_INCREMENT)
          else balance) ∧
      ∀ k, k ≠ j → next.balances.data[k]? = last.balances.data[k]? := by
  simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, computed⟩ := computed
  obtain ⟨kept, slot, ⟨registered, entry⟩, others⟩ := slashingStep_balances small found <| by
    split at computed
    · rename_i slashed
      simp only [bind_ok_iff] at computed
      obtain ⟨due, dueOk, computed⟩ := computed
      have dueIff := slashingPenaltyDue_iff slashed dueOk
      split at computed
      · rename_i isDue
        simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff] at computed
        obtain ⟨numerator, product, penalty, scaled, validatorIndex, converted, lowered⟩ := computed
        have indexEq : validatorIndex = j.toUInt64 :=
          Except.ok.inj (converted.symm.trans (ofNatChecked_of_lt small))
        rw [indexEq] at lowered
        have product := Except.ok.inj
          ((mulChecked_of_lt (mulChecked_ok_iff.mp product).1).symm.trans product)
        have scaled := Except.ok.inj
          ((mulChecked_of_lt (mulChecked_ok_iff.mp scaled).1).symm.trans scaled)
        subst product scaled
        exact .inl ⟨dueIff.mpr isDue, lowered⟩
      · rename_i notDue
        simp only [pure, Except.pure, Except.ok.injEq] at computed
        exact .inr ⟨fun due => notDue (dueIff.mp due), computed.symm⟩
    · rename_i notSlashed
      simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact .inr ⟨fun due => notSlashed due.1, computed.symm⟩
  exact ⟨kept, slot, ⟨validator, registered, entry⟩, others⟩

/-- The penalty step used from Electra lowers the balance of one validator when it is due.

This holds when the step succeeds at a position below `2^64`.

The registry and the slot stay.

The validator at that position exists.

Its balance loses the penalty if it is due, stopping at zero.

The penalty is the given penalty per increment, times its effective balance in increments.

The other balances stay. -/
theorem applySlashingPenaltyElectra_balances {perIncrement : Gwei}
    {last next : BeaconState preset fork} {j : Nat} (small : j < 2 ^ 64)
    (computed : applySlashingPenaltyElectra last perIncrement j = .ok next) :
    next.validators = last.validators ∧ next.slot = last.slot ∧
      (∃ validator, last.validators.data[j]? = some validator ∧
        next.balances.data[j]? = last.balances.data[j]?.map fun balance =>
          if SlashingPenaltyDue preset (getCurrentEpoch last) validator then
            saturatingSub balance
              (perIncrement * (validator.effectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT))
          else balance) ∧
      ∀ k, k ≠ j → next.balances.data[k]? = last.balances.data[k]? := by
  simp only [applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, computed⟩ := computed
  obtain ⟨kept, slot, ⟨registered, entry⟩, others⟩ := slashingStep_balances small found <| by
    split at computed
    · rename_i slashed
      simp only [bind_ok_iff] at computed
      obtain ⟨due, dueOk, computed⟩ := computed
      have dueIff := slashingPenaltyDue_iff slashed dueOk
      split at computed
      · rename_i isDue
        simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff] at computed
        obtain ⟨penalty, product, validatorIndex, converted, lowered⟩ := computed
        have indexEq : validatorIndex = j.toUInt64 :=
          Except.ok.inj (converted.symm.trans (ofNatChecked_of_lt small))
        rw [indexEq] at lowered
        have product := Except.ok.inj
          ((mulChecked_of_lt (mulChecked_ok_iff.mp product).1).symm.trans product)
        subst product
        exact .inl ⟨dueIff.mpr isDue, lowered⟩
      · rename_i notDue
        simp only [pure, Except.pure, Except.ok.injEq] at computed
        exact .inr ⟨fun due => notDue (dueIff.mp due), computed.symm⟩
    · rename_i notSlashed
      simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact .inr ⟨fun due => notSlashed due.1, computed.symm⟩
  exact ⟨kept, slot, ⟨validator, registered, entry⟩, others⟩

/-- A fold of slashing steps over the registry lowers each balance by its penalty when it is due.

Each step lowers the balance at its position below `2^64` by the penalty of its validator, if due.

It keeps the registry, the slot and the other balances.

The validators are those of the first state.

The penalty is due at the epoch of the first state. -/
private theorem foldlM_slashingSteps_balances {ε : Type}
    {step : BeaconState preset fork → Nat → Except ε (BeaconState preset fork)}
    (penalty : Validator → Gwei) (within : state.RegistryWithinLimit)
    (stepped : ∀ {last next : BeaconState preset fork} {j : Nat}, j < 2 ^ 64 →
      step last j = .ok next → next.validators = last.validators ∧ next.slot = last.slot ∧
        (∃ validator, last.validators.data[j]? = some validator ∧
          next.balances.data[j]? = last.balances.data[j]?.map fun balance =>
            if SlashingPenaltyDue preset (getCurrentEpoch last) validator then
              saturatingSub balance (penalty validator)
            else balance) ∧
        ∀ k, k ≠ j → next.balances.data[k]? = last.balances.data[k]?)
    (computed : (List.range state.validators.data.size).foldlM step state = .ok after) (i : Nat) :
    (i < state.validators.data.size → ∃ validator, state.validators.data[i]? = some validator ∧
      after.balances.data[i]? = state.balances.data[i]?.map fun balance =>
        if SlashingPenaltyDue preset (getCurrentEpoch state) validator then
          saturatingSub balance (penalty validator)
        else balance) ∧
    (state.validators.data.size ≤ i → after.balances.data[i]? = state.balances.data[i]?) := by
  have bound : state.validators.data.size ≤ _ := within
  have limit := preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
  refine (foldlM_range_balances
    (fun last => last.validators = state.validators ∧ last.slot = state.slot)
    (fun j old new => ∃ validator, state.validators.data[j]? = some validator ∧
      new = old.map fun balance =>
        if SlashingPenaltyDue preset (getCurrentEpoch state) validator then
          saturatingSub balance (penalty validator)
        else balance)
    (fun {last next j} lt ⟨sameRegistry, sameSlot⟩ step => ?_) ⟨rfl, rfl⟩ computed).2 i
  obtain ⟨kept, slot, ⟨validator, registered, entry⟩, others⟩ := stepped (by omega) step
  have sameEpoch : getCurrentEpoch last = getCurrentEpoch state := by
    unfold getCurrentEpoch
    rw [sameSlot]
  rw [sameEpoch] at entry
  exact ⟨⟨kept.trans sameRegistry, slot.trans sameSlot⟩,
    ⟨validator, sameRegistry ▸ registered, entry⟩, others⟩

/-- Before Electra, the slashings lower the balance of each validator by its penalty when it is due.

This holds when the step succeeds.

The penalty uses the active balance and the sum of the recent slashed balances.

The sum is scaled by the multiplier of the fork, then capped by the active balance.

The penalty is the effective balance in increments, times that adjusted balance.

That product is divided by the active balance, then counted back in increments.

The balance stops at zero when the penalty is larger.

The balances past the registry stay. -/
theorem processSlashings_balances_of_lt_electra (before : fork < .pectra)
    (computed : processSlashings state = .ok after) :
    ∃ total sum, getTotalActiveBalance state = .ok total ∧ slashingsSum state = .ok sum ∧
      ∀ i, (i < state.validators.data.size → ∃ validator,
        state.validators.data[i]? = some validator ∧
        after.balances.data[i]? = state.balances.data[i]?.map fun balance =>
          if SlashingPenaltyDue preset (getCurrentEpoch state) validator then
            saturatingSub balance (validator.effectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT *
              min (sum * (parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER) total / total *
              preset.EFFECTIVE_BALANCE_INCREMENT)
          else balance) ∧
      (state.validators.data.size ≤ i → after.balances.data[i]? = state.balances.data[i]?) := by
  have notElectra : ¬ .pectra ≤ fork := Nat.not_le_of_lt before
  simp only [processSlashings, notElectra, ↓reduceIte, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff] at computed
  obtain ⟨total, totalOk, sum, sumOk, slashed, product, applied⟩ := computed
  have product := Except.ok.inj
    ((mulChecked_of_lt (mulChecked_ok_iff.mp product).1).symm.trans product)
  subst product
  -- Before Gloas the type of the registry keeps it within its limit.
  have within : state.RegistryWithinLimit :=
    state.validators.bound (Nat.lt_trans before (by decide))
  exact ⟨total, sum, totalOk, sumOk, foldlM_slashingSteps_balances _ within
    applySlashingPenalty_balances applied⟩

/-- From Electra, the slashings lower the balance of each validator by its penalty when it is due.

This holds when the step succeeds on a registry within its limit.

The penalty uses the active balance and the sum of the recent slashed balances.

The sum is scaled by the multiplier of the fork, then capped by the active balance.

The penalty per increment divides that adjusted balance by the active balance in increments.

The penalty is the penalty per increment, times the effective balance in increments.

The balance stops at zero when the penalty is larger.

The balances past the registry stay. -/
theorem processSlashings_balances_of_electra (electra : .pectra ≤ fork)
    (within : state.RegistryWithinLimit) (computed : processSlashings state = .ok after) :
    ∃ total sum, getTotalActiveBalance state = .ok total ∧ slashingsSum state = .ok sum ∧
      ∀ i, (i < state.validators.data.size → ∃ validator,
        state.validators.data[i]? = some validator ∧
        after.balances.data[i]? = state.balances.data[i]?.map fun balance =>
          if SlashingPenaltyDue preset (getCurrentEpoch state) validator then
            saturatingSub balance
              (min (sum * (parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER) total /
                (total / preset.EFFECTIVE_BALANCE_INCREMENT) *
                (validator.effectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT))
          else balance) ∧
      (state.validators.data.size ≤ i → after.balances.data[i]? = state.balances.data[i]?) := by
  simp only [processSlashings, electra, ↓reduceIte, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff] at computed
  obtain ⟨total, totalOk, sum, sumOk, slashed, product, perIncrement, ⟨increments, counted,
    divided⟩, applied⟩ := computed
  have product := Except.ok.inj
    ((mulChecked_of_lt (mulChecked_ok_iff.mp product).1).symm.trans product)
  have counted : increments = total / preset.EFFECTIVE_BALANCE_INCREMENT := by
    rw [← UInt64.toNat_inj, UInt64.toNat_div]
    exact (divChecked_ok_iff.mp counted).2
  have divided : perIncrement = min slashed total / increments := by
    rw [← UInt64.toNat_inj, UInt64.toNat_div]
    exact (divChecked_ok_iff.mp divided).2
  subst product counted divided
  exact ⟨total, sum, totalOk, sumOk, foldlM_slashingSteps_balances _ within
    applySlashingPenaltyElectra_balances applied⟩

/-- Successful slashings subtract the natural-number penalty, saturating at zero.

The scaled sum of slashings does not overflow, even when no validator has a due penalty.

The proof uses the per-step no-overflow lemmas only for due penalties.

Before Electra the increment count is multiplied by the adjusted slashed balance.

That product is divided by the active balance, then multiplied by the increment.

From Electra the adjusted slashed balance is first divided by the active balance in increments.

The registry bound keeps each position representable as a validator index. -/
theorem processSlashings_balances_toNat (within : state.RegistryWithinLimit)
    (computed : processSlashings state = .ok after) :
    ∃ total sum, getTotalActiveBalance state = .ok total ∧ slashingsSum state = .ok sum ∧
      sum.toNat * (parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER.toNat < 2 ^ 64 ∧
      ∀ i, (i < state.validators.data.size → ∃ validator,
        state.validators.data[i]? = some validator ∧
        (after.balances.data[i]?).map UInt64.toNat =
          state.balances.data[i]?.map fun balance => balance.toNat -
            if SlashingPenaltyDue preset (getCurrentEpoch state) validator then
              let increment := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
              let adjusted := min (sum.toNat *
                (parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER.toNat) total.toNat
              if .pectra ≤ fork then
                adjusted / (total.toNat / increment) *
                  (validator.effectiveBalance.toNat / increment)
              else validator.effectiveBalance.toNat / increment * adjusted / total.toNat * increment
            else 0) ∧
        (state.validators.data.size ≤ i → after.balances.data[i]? = state.balances.data[i]?) := by
  unfold processSlashings at computed
  simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff] at computed
  obtain ⟨total, totalOk, sum, sumOk, slashed, product, computed⟩ := computed
  obtain ⟨fits, exact⟩ := mulChecked_ok_iff.mp product
  -- The cap is applied after the checked scaling, not to a wrapped product.
  have adjusted : (min slashed total).toNat = min (sum.toNat *
      (parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER.toNat) total.toNat := by
    rw [UInt64.min_def]
    split
    · rename_i le
      rw [exact, Nat.min_eq_left (by simpa only [exact] using UInt64.le_iff_toNat_le.mp le)]
    · rename_i lt
      rw [Nat.min_eq_right (by
        have := UInt64.le_iff_toNat_le.mp (UInt64.le_of_lt (UInt64.not_le.mp lt))
        simpa only [exact] using this)]
  refine ⟨total, sum, totalOk, sumOk, fits, ?_⟩
  have bound : state.validators.data.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt within preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
  let penalty := fun validator : Validator =>
    if SlashingPenaltyDue preset (getCurrentEpoch state) validator then
      let increment := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      let adjusted := min (sum.toNat *
        (parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER.toNat) total.toNat
      if .pectra ≤ fork then
        adjusted / (total.toNat / increment) * (validator.effectiveBalance.toNat / increment)
      else validator.effectiveBalance.toNat / increment * adjusted / total.toNat * increment
    else 0
  split at computed
  · rename_i electra
    simp only [bind_ok_iff, liftAccessor_ok, mapError_ok_iff] at computed
    obtain ⟨perIncrement, ⟨increments, counted, divided⟩, folded⟩ := computed
    have perNat := (divChecked_ok_iff.mp divided).2
    rw [(divChecked_ok_iff.mp counted).2, adjusted] at perNat
    -- Reuse the balance fold with the same registry and epoch at every position.
    refine (foldlM_range_balances
      (fun last => last.validators = state.validators ∧ last.slot = state.slot)
      (fun i old new => ∃ validator, state.validators.data[i]? = some validator ∧
        new.map UInt64.toNat = old.map fun balance => balance.toNat - penalty validator)
      (fun {last next j} lt ⟨registry, slot⟩ step => ?_) ⟨rfl, rfl⟩ folded).2
    obtain ⟨kept, keptSlot, ⟨validator, found, entry⟩, others⟩ :=
      applySlashingPenaltyElectra_balances (by omega) step
    have epoch : getCurrentEpoch last = getCurrentEpoch state := by
      simp only [getCurrentEpoch, slot]
    refine ⟨⟨kept.trans registry, keptSlot.trans slot⟩,
      ⟨validator, registry ▸ found, ?_⟩, others⟩
    rw [entry, Option.map_map]
    congr 1
    funext balance
    by_cases due : SlashingPenaltyDue preset (getCurrentEpoch last) validator
    · have fits := applySlashingPenaltyElectra_no_overflow
        (getValidatorAt_eq_ok_iff.mpr found) due step
      rw [perNat] at fits
      -- Success removes the modular reduction only in the branch that computes the penalty.
      simp only [penalty, Function.comp_apply, due, ↓reduceIte, toNat_saturatingSub,
        UInt64.toNat_mul, UInt64.toNat_div, Nat.mod_eq_of_lt fits,
        ← epoch, electra, perNat]
    · simp only [penalty, Function.comp_apply, ← epoch, due, ↓reduceIte, Nat.sub_zero]
  · rename_i before
    refine (foldlM_range_balances
      (fun last => last.validators = state.validators ∧ last.slot = state.slot)
      (fun i old new => ∃ validator, state.validators.data[i]? = some validator ∧
        new.map UInt64.toNat = old.map fun balance => balance.toNat - penalty validator)
      (fun {last next j} lt ⟨registry, slot⟩ step => ?_) ⟨rfl, rfl⟩ computed).2
    obtain ⟨kept, keptSlot, ⟨validator, found, entry⟩, others⟩ :=
      applySlashingPenalty_balances (by omega) step
    have epoch : getCurrentEpoch last = getCurrentEpoch state := by
      simp only [getCurrentEpoch, slot]
    refine ⟨⟨kept.trans registry, keptSlot.trans slot⟩,
      ⟨validator, registry ▸ found, ?_⟩, others⟩
    rw [entry, Option.map_map]
    congr 1
    funext balance
    by_cases due : SlashingPenaltyDue preset (getCurrentEpoch last) validator
    · obtain ⟨numeratorFits, penaltyFits⟩ := applySlashingPenalty_no_overflow
        (getValidatorAt_eq_ok_iff.mpr found) due step
      rw [adjusted] at numeratorFits penaltyFits
      -- Before Electra both multiplications must be unwrapped, in calculation order.
      simp only [penalty, Function.comp_apply, due, ↓reduceIte, toNat_saturatingSub,
        UInt64.toNat_mul, UInt64.toNat_div, Nat.mod_eq_of_lt numeratorFits,
        Nat.mod_eq_of_lt penaltyFits, ← epoch, before, adjusted]
    · simp only [penalty, Function.comp_apply, ← epoch, due, ↓reduceIte, Nat.sub_zero]

/-! ## Resets and rotations -/

/-- The slashings reset clears the slashed balance of the next epoch, and nothing else. -/
theorem processSlashingsReset_eq (computed : processSlashingsReset state = .ok after) :
    ∃ (nextEpoch : Epoch) (slashings : RootedVector Gwei preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat),
      nextEpoch.toNat = (getCurrentEpoch state).toNat + 1 ∧
      writeCircularRooted state.slashings nextEpoch 0 = .ok slashings ∧
      after = { state with slashings } := by
  simp only [processSlashingsReset, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨nextEpoch, ⟨_, sum⟩, slashings, written, rfl⟩ := computed
  exact ⟨nextEpoch, slashings, by simpa using sum, written, rfl⟩

/-- The RANDAO reset copies the mix of the current epoch to the next epoch, and nothing else. -/
theorem processRandaoMixesReset_eq (computed : processRandaoMixesReset state = .ok after) :
    ∃ (nextEpoch : Epoch) (mix : Bytes32)
      (randaoMixes : RootedVector Bytes32 preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat),
      nextEpoch.toNat = (getCurrentEpoch state).toNat + 1 ∧
      getRandaoMix state (getCurrentEpoch state) = .ok mix ∧
      writeCircularRooted state.randaoMixes nextEpoch mix = .ok randaoMixes ∧
      after = { state with randaoMixes } := by
  simp only [processRandaoMixesReset, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨nextEpoch, ⟨_, sum⟩, mix, mixOk, randaoMixes, written, rfl⟩ := computed
  exact ⟨nextEpoch, mix, randaoMixes, by simpa using sum, mixOk, written, rfl⟩

/-- Before Altair, the rotation moves the pending attestations of the current epoch to the previous.

The current ones then start empty. -/
theorem processParticipationRecordUpdates_eq (before : fork < .altair) :
    ∃ after, processParticipationRecordUpdates state = .ok after ∧
      after.previousEpochAttestations before = state.currentEpochAttestations before ∧
      (after.currentEpochAttestations before).data = #[] ∧
      { after with
        previousEpochAttestations := state.previousEpochAttestations,
        currentEpochAttestations := state.currentEpochAttestations } = state := by
  have notAltair : ¬Fork.altair ≤ fork := fun le => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le before le)
  refine ⟨{ state with
    previousEpochAttestations := state.currentEpochAttestations
    currentEpochAttestations := fun _ => ⟨#[], by simp⟩ }, ?_, rfl, rfl, rfl⟩
  simp only [processParticipationRecordUpdates, notAltair, ↓reduceIte]
  try rfl

end EthLib.Consensus
