module

public import EthLib.Consensus.Proofs.Transition.BalanceNotRaised
public import EthLib.Consensus.Proofs.Transition.InactivityLeak
public import EthLib.Consensus.Proofs.Transition.InactivityLeakEpoch
import EthLib.Consensus.Proofs.Transition.ValidatorKeys

/-!
# Proofs: one epoch of a leak for an absent validator, in the form of the trace bound

The trace bound of an inactivity leak follows one validator from epoch to epoch.

It reads its balance and its score before each epoch transition.

It reads its effective balance there too, and its balance at the update of the effective balances.

This module derives one step of those traces from one epoch transition, from Altair.

The step is the state after the epoch: its balance, its effective balance and its score.

The blocks and slots before the next epoch are not covered here.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- The update of the effective balances reads a balance at each position of the registry.

So it succeeds only when each validator has a balance. -/
private theorem balance_of_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) {index : Nat}
    (inside : index < state.validators.data.size) :
    ∃ balance, state.balances.data[index]? = some balance := by
  unfold processEffectiveBalanceUpdates at computed
  obtain ⟨middle, next, prefixOk, atIndex, -⟩ :=
    (foldlM_ok_steps (fun _ _ => True) (fun _ => trivial) (fun _ _ => trivial)
      (fun _ _ _ _ => trivial) computed).2 index (by simpa using inside)
  simp only [List.getElem_range] at atIndex
  have balances : middle.balances = state.balances :=
    foldlM_ok_invariant (fun current : BeaconState preset fork =>
      current.balances = state.balances)
      (fun _ _ _ kept step => by
        simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at step
        obtain ⟨_, _, _, _, _, _, set⟩ := step
        obtain ⟨_, rfl⟩ := setValidatorAt_ok set
        exact kept) rfl prefixOk
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at atIndex
  obtain ⟨_, _, balance, read, -⟩ := atIndex
  rw [← balances]
  exact ⟨balance, getBalanceAt_eq_ok_iff.mp read⟩

/-- The largest effective balance of a validator depends only on its credentials. -/
theorem withdrawalMaxEffectiveBalance_of_credentials {old new : Validator}
    (same : new.withdrawalCredentials = old.withdrawalCredentials) :
    withdrawalMaxEffectiveBalance preset fork new =
      withdrawalMaxEffectiveBalance preset fork old := by
  unfold withdrawalMaxEffectiveBalance getMaxEffectiveBalance hasCompoundingWithdrawalCredential
  rw [same]

/-- One leak epoch of an absent validator, from Altair.

The epoch transition succeeds, from a state that leaks, and does not raise the finalized epoch.

The registry is within its limit.

The validator is eligible, and its flags of the previous epoch lack the timely target flag.

No pending deposit carries its key, and no pending consolidation targets it.

After the epoch its score is the old one plus the score bias.

Its balance is at most the old one less its effective balance times the new score.

That product is divided by the score bias times the penalty quotient of the fork, and rounds down.

The subtraction stops at zero.

Its new effective balance is the update of the old one from that balance.

The update uses the largest effective balance of the validator before the epoch.

It keeps its key and its withdrawal credentials. -/
theorem absentEpoch_processEpoch (altair : .altair ≤ fork)
    (computed : processEpoch config checks state = .ok after)
    (within : state.RegistryWithinLimit) (leak : isInInactivityLeak state = .ok true)
    (stalled : after.finalizedCheckpoint.epoch ≤ state.finalizedCheckpoint.epoch)
    {index : Nat} {validator : Validator} (found : state.validators.data[index]? = some validator)
    (eligible : isEligibleValidator (getPreviousEpoch state) validator = .ok true)
    (untimely : ∀ flags, (state.previousEpochParticipation altair).data[index]? = some flags →
      hasFlag flags TIMELY_TARGET_FLAG_INDEX = false)
    (unnamed : ∀ electra : .pectra ≤ fork, ∀ deposit ∈ (state.pendingDeposits electra).data,
      deposit.pubkey ≠ validator.pubkey)
    (untargeted : ∀ electra : .pectra ≤ fork,
      ∀ consolidation ∈ (state.pendingConsolidations electra).data,
        consolidation.targetIndex.toNat ≠ index) :
    ∃ balance settled score score' effective now,
      state.balances.data[index]? = some balance ∧
      after.balances.data[index]? = some settled ∧
      (state.inactivityScores altair).data[index]? = some score ∧
      (after.inactivityScores altair).data[index]? = some score' ∧
      score'.toNat = score.toNat + config.INACTIVITY_SCORE_BIAS.toNat ∧
      settled.toNat ≤ balance.toNat - validator.effectiveBalance.toNat * score'.toNat /
        (config.INACTIVITY_SCORE_BIAS.toNat *
          (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) ∧
      updatedEffectiveBalance preset (withdrawalMaxEffectiveBalance preset fork validator) settled
        validator.effectiveBalance = .ok effective ∧
      after.validators.data[index]? = some now ∧ now.effectiveBalance = effective ∧
      now.pubkey = validator.pubkey ∧
      now.withdrawalCredentials = validator.withdrawalCredentials := by
  have altairRun : processEpochAltair config checks state altair = .ok after := by
    unfold processEpoch at computed
    simpa only [altair, ↓reduceDIte] using computed
  obtain ⟨justified, scored, rewarded, settledState, updated, kept, justifiedOk, sameBalances,
    sameValidators, scoredOk, rewardedOk, raised, atKept, keptEffective, keptCredentials,
    updatedOk, afterBalances, afterValidators, scoreKept⟩ :=
    balanceNotRaised_processEpochAltair altairRun found unnamed untargeted
  -- Finality does not advance, so the state after justification leaks.
  obtain ⟨justified', justifiedOk', advanced⟩ :=
    processEpoch_finalized_lt_or_isInInactivityLeak leak computed
  have sameJustified : justified' = justified :=
    Except.ok.inj (justifiedOk'.symm.trans justifiedOk)
  rw [sameJustified] at advanced
  have leaking : isInInactivityLeak justified = .ok true :=
    advanced.resolve_left fun lt => absurd stalled (UInt64.not_le.mpr lt)
  -- The state after justification has the same slot, registry, balances and flags.
  have keeps := processJustificationAndFinalization_keeps justifiedOk
  have previousEq : getPreviousEpoch justified = getPreviousEpoch state := by
    unfold getPreviousEpoch getCurrentEpoch
    rw [processJustificationAndFinalization_slot justifiedOk]
  have withinJustified : justified.RegistryWithinLimit := by
    unfold BeaconState.RegistryWithinLimit
    rw [sameValidators]
    exact within
  have inside : index < state.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
  have insideJustified : index < justified.validators.data.size := by
    rw [sameValidators]
    exact inside
  have atJustified : justified.validators.data[index] = validator := by
    have foundJustified := found
    rw [← sameValidators] at foundJustified
    exact (Array.getElem?_eq_some_iff.mp foundJustified).2
  obtain ⟨total, source, target, -, -, targetOk, facts⟩ :=
    processRewardsAndPenalties_of_leak altair withinJustified leaking scoredOk rewardedOk
  obtain ⟨isEligible, eligibleOk, -, active⟩ := facts index insideJustified
  rw [atJustified, previousEq, eligible] at eligibleOk
  obtain ⟨base, balance, balance', score, score', -, atBalance, atBalance', atScore, atScore',
    scoreEq, balanceEq⟩ := active (Except.ok.inj eligibleOk).symm
  -- The validator is not in the target set: its previous flags lack the target flag.
  have small : index < 2 ^ 64 := by
    have limit := preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
    unfold BeaconState.RegistryWithinLimit at within
    omega
  have differ : getPreviousEpoch justified ≠ getCurrentEpoch justified := by
    have later := getCurrentEpoch_ne_genesis_of_leak leaking
    have positive : (getCurrentEpoch justified).toNat ≠ 0 := fun zero =>
      later (UInt64.toNat_inj.mp (by simpa [GENESIS_EPOCH] using zero))
    intro same
    have := getPreviousEpoch_toNat justified
    rw [same] at this
    omega
  have notTarget : index.toUInt64 ∉ target := by
    intro member
    obtain ⟨-, -, flags, atFlags, set⟩ :=
      mem_getUnslashedParticipatingIndices targetOk _ member
    simp only [differ, ↓reduceIte, keeps.2.2.2.2.2.2.2.2.1] at atFlags
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt small] at atFlags
    rw [untimely flags atFlags] at set
    exact Bool.false_ne_true set
  simp only [notTarget, ↓reduceIte] at scoreEq balanceEq
  rw [atJustified] at balanceEq
  -- The later steps raise no balance, and the update of the effective balances keeps them.
  obtain ⟨settled, owned⟩ := balance_of_processEffectiveBalanceUpdates updatedOk
    (Array.getElem?_eq_some_iff.mp atKept).1
  obtain ⟨earlier, atEarlier, lower⟩ := raised settled owned
  rw [atBalance', Option.some.injEq] at atEarlier
  subst atEarlier
  obtain ⟨effective, atUpdated, effectiveOk⟩ :=
    processEffectiveBalanceUpdates_effectiveBalance_eq updatedOk atKept owned
  rw [keptEffective, withdrawalMaxEffectiveBalance_of_credentials keptCredentials]
    at effectiveOk
  -- The key of the validator stays at its position through the epoch.
  obtain ⟨justified'', justifiedOk'', frame⟩ := processEpoch_frame computed
  have sameJustified' : justified'' = justified :=
    Except.ok.inj (justifiedOk''.symm.trans justifiedOk)
  rw [sameJustified'] at frame
  have foundJustified := found
  rw [← sameValidators] at foundJustified
  obtain ⟨current, atCurrent, currentKey⟩ :=
    validators_getElem?_of_validatorKeys_prefix frame.pubkeysPrefix foundJustified
  rw [afterValidators, atUpdated, Option.some.injEq] at atCurrent
  subst atCurrent
  refine ⟨balance, settled, score, score', effective, { kept with effectiveBalance := effective },
    ?_, ?_, ?_, ?_, scoreEq, ?_, effectiveOk, ?_, rfl, currentKey, keptCredentials⟩
  · rw [← sameBalances]
    exact atBalance
  · rw [afterBalances, processEffectiveBalanceUpdates_balances updatedOk]
    exact owned
  · have scores : justified.inactivityScores = state.inactivityScores := by
      obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok justifiedOk
      · rfl
      · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
        rw [← rest]
    rw [← scores]
    exact atScore
  · rw [scoreKept altair]
    exact atScore'
  · rw [UInt64.le_iff_toNat_le, balanceEq] at lower
    exact Nat.le_trans lower
      (Nat.sub_le_sub_left (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_left _ _)) _)
  · rw [afterValidators]
    exact atUpdated

end EthLib.Consensus
