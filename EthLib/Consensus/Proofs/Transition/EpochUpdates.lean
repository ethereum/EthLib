module

public import EthLib.Consensus.Proofs.Transition.EpochRewards
public import EthLib.Consensus.Transition.EpochUpdates

/-!
# Proofs: the other steps of the epoch transition

An updated effective balance is the old one, or the balance rounded down to an increment and capped.

The effective balances are aligned when each is a whole number of increments, at most its largest.

When each largest value is itself a whole number of increments, the update keeps them aligned.

The registry updates, the slashings and the update of the effective balances keep the sizes.

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
theorem effectiveBalancesAligned_setValidator {index : Nat} {validator : Validator}
    (holds : EffectiveBalancesAligned state)
    (good : validator.effectiveBalance % preset.EFFECTIVE_BALANCE_INCREMENT = 0 ∧
      validator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork validator) :
    EffectiveBalancesAligned (state.setValidator index validator) := by
  intro other member
  simp only [BeaconState.setValidator, Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
    at member
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
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨validator, found, _, _, effectiveBalance, updated, rfl⟩ := computed
  apply effectiveBalancesAligned_setValidator holds
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
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, rfl⟩ := computed
  exact sameSizes_setValidator _ _ _

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
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · rw [liftAccessor_ok] at computed
    exact (sameSizes_setValidator _ _ _).trans (sameSizes_initiateValidatorExit computed)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ sameSizes_setValidator _ _ _

theorem sameSizes_activateValidator {index : ValidatorIndex}
    (computed : activateValidator state index = .ok after) : SameSizes state after := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  exact sameSizes_setValidator _ _ _

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
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact sameSizes_setValidator _ _ _
  split at computed
  · rw [liftAccessor_ok] at computed
    exact sameSizes_initiateValidatorExit computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ sameSizes_setValidator _ _ _
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

/-! ## Resets and rotations -/

/-- The slashings reset clears the slashed balance of the next epoch, and nothing else. -/
theorem processSlashingsReset_eq (computed : processSlashingsReset state = .ok after) :
    ∃ nextEpoch : Epoch, nextEpoch.toNat = (getCurrentEpoch state).toNat + 1 ∧
      after = { state with
        slashings :=
          state.slashings.set! (nextEpoch % preset.EPOCHS_PER_SLASHINGS_VECTOR).toNat 0 } := by
  simp only [processSlashingsReset, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨nextEpoch, ⟨_, sum⟩, rfl⟩ := computed
  exact ⟨nextEpoch, by simpa using sum, rfl⟩

/-- The RANDAO reset copies the mix of the current epoch to the next epoch, and nothing else. -/
theorem processRandaoMixesReset_eq (computed : processRandaoMixesReset state = .ok after) :
    ∃ (nextEpoch : Epoch) (mix : Bytes32), nextEpoch.toNat = (getCurrentEpoch state).toNat + 1 ∧
      getRandaoMix state (getCurrentEpoch state) = .ok mix ∧
      after = { state with
        randaoMixes :=
          state.randaoMixes.set! (nextEpoch % preset.EPOCHS_PER_HISTORICAL_VECTOR).toNat mix } := by
  simp only [processRandaoMixesReset, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨nextEpoch, ⟨_, sum⟩, mix, mixOk, rfl⟩ := computed
  exact ⟨nextEpoch, mix, by simpa using sum, mixOk, rfl⟩

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
