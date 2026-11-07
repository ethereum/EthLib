module

public import EthLib.Consensus.Proofs.Transition.EpochRewards
public import EthLib.Consensus.Transition.EpochUpdates

/-!
# Proofs: the other steps of the epoch transition

An updated effective balance is the old one, or the balance rounded down to an increment and capped.

The effective balances are aligned when each is a whole number of increments, at most its largest.

When each largest value is itself a whole number of increments, the update keeps them aligned.

The registry updates, the slashings and the update of the effective balances keep the sizes.

When the slashings succeed, each balance of the registry loses its penalty if it is due.

That balance stops at zero.

From Electra this holds for a registry within its limit.

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

/-- Every effective balance is a whole number of increments, and at most its largest at the fork.
-/
def EffectiveBalancesAligned (state : BeaconState preset fork) : Prop :=
  ∀ validator ∈ state.validators.data.toList,
    validator.effectiveBalance % preset.EFFECTIVE_BALANCE_INCREMENT = 0 ∧
      validator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork validator

/-- An updated effective balance is aligned when the old one and the largest are. -/
theorem updatedEffectiveBalance_aligned {largest balance effectiveBalance result : Gwei}
    (maxAligned : largest % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (old : effectiveBalance % preset.EFFECTIVE_BALANCE_INCREMENT = 0 ∧ effectiveBalance ≤ largest)
    (computed : updatedEffectiveBalance preset largest balance effectiveBalance = .ok result) :
    result % preset.EFFECTIVE_BALANCE_INCREMENT = 0 ∧ result ≤ largest := by
  rcases updatedEffectiveBalance_cases computed with rfl | rfl
  · exact old
  · rw [UInt64.min_def]
    split
    · exact ⟨sub_mod_mod_self _ _, by assumption⟩
    · exact ⟨maxAligned, UInt64.le_refl _⟩

/-- Replacing a validator by an aligned one keeps the effective balances aligned. -/
theorem effectiveBalancesAligned_setValidator {index : ValidatorIndex} {validator : Validator}
    (holds : EffectiveBalancesAligned state)
    (good : validator.effectiveBalance % preset.EFFECTIVE_BALANCE_INCREMENT = 0 ∧
      validator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork validator)
    (set : state.setValidator index validator = .ok after) :
    EffectiveBalancesAligned after := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  intro other member
  simp only [BeaconState.putValidator, RootedForkList.data_set, Array.toList_set] at member
  rcases List.mem_or_eq_of_mem_set member with old | rfl
  · exact holds other old
  · exact good

/-- The update of one effective balance keeps them aligned, when each largest is aligned. -/
theorem updateEffectiveBalance_aligned {index : Nat}
    (maxAligned : ∀ validator,
      withdrawalMaxEffectiveBalance preset fork validator % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (holds : EffectiveBalancesAligned state)
    (computed : updateEffectiveBalance state index = .ok after) :
    EffectiveBalancesAligned after := by
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, _, _, effectiveBalance, updated, set⟩ := computed
  refine effectiveBalancesAligned_setValidator holds ?_ set
  apply updatedEffectiveBalance_aligned (maxAligned validator) _ updated
  unfold getValidator at found
  split at found
  · rename_i read
    cases found
    exact holds _ (Array.mem_toList_iff.mpr (Array.mem_of_getElem? read))
  · cases found

/-- The update of the effective balances keeps them aligned.

The largest effective balance of each validator must be a whole number of increments. -/
theorem processEffectiveBalanceUpdates_aligned
    (maxAligned : ∀ validator,
      withdrawalMaxEffectiveBalance preset fork validator % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
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
  exact sameSizes_setValidator set

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
  · rw [liftAccessor_ok] at computed
    exact (sameSizes_setValidator set).trans (sameSizes_initiateValidatorExit computed)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ sameSizes_setValidator set

theorem sameSizes_activateValidator {index : ValidatorIndex}
    (computed : activateValidator state index = .ok after) : SameSizes state after := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, set⟩ := computed
  exact sameSizes_setValidator set

/-- From Deneb, an epoch activates at most the maximum, and at most the churn limit. -/
theorem getValidatorActivationChurnLimit_le {config : Config} :
    getValidatorActivationChurnLimit config state ≤ config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT ∧
      getValidatorActivationChurnLimit config state ≤ getValidatorChurnLimit config state :=
  ⟨Std.min_le_left, Std.min_le_right⟩

theorem sameSizes_updateRegistryEntryElectra {config : Config} {activationEpoch : Epoch}
    {index : Nat}
    (computed : updateRegistryEntryElectra config activationEpoch state index = .ok after) :
    SameSizes state after := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, set⟩ := computed
    exact sameSizes_setValidator set
  split at computed
  · rw [liftAccessor_ok] at computed
    exact sameSizes_initiateValidatorExit computed
  split at computed
  · rw [liftAccessor_ok] at computed
    exact sameSizes_setValidator computed
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
      obtain ⟨_, _, _, _, lowered⟩ := computed
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
      obtain ⟨_, _, lowered⟩ := computed
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
    (found : getValidator last j.toUInt64 = .ok validator)
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
  have registered : last.validators.data[j]? = some validator := by
    unfold getValidator at found
    rw [same] at found
    split at found
    · cases found
      assumption
    · cases found
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
        obtain ⟨numerator, product, penalty, scaled, lowered⟩ := computed
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
        obtain ⟨penalty, product, lowered⟩ := computed
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
