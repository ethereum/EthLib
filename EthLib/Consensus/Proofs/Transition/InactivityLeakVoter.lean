module

public import EthLib.Consensus.Proofs.Transition.InactivityLeakTrace
import EthLib.Consensus.Proofs.Transition.Totality.EpochBeforeAltair

/-!
# Proofs: one epoch of a leak lowers no balance of a voter

In a leak the voters keep their stake, so their share can grow to two thirds of the active stake.

From Altair, an epoch lowers a balance in three ways.

The rewards and penalties charge a validator that misses the timely source or target flag.

In a leak an unslashed validator with the timely source and target flags pays nothing.

So does one that is not eligible.

The slashings charge a slashed validator.

From Electra, a pending consolidation moves the balance of its source.

The registry updates and the eth1 vote reset keep the balances.

The pending deposits and the consolidations into a validator only raise them.

The builder payments and the steps after the effective balances keep them.

So the balance of an unslashed voter that is the source of no pending consolidation does not fall.

Its effective balance then follows the update from that balance.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- The balance at a position does not fall from one state to another.

A position with no balance in the first state counts as not lowered. -/
def BalanceNotLowered (index : Nat) (state after : BeaconState preset fork) : Prop :=
  ∀ earlier, state.balances.data[index]? = some earlier →
    ∃ later, after.balances.data[index]? = some later ∧ earlier ≤ later

/-- A state lowers no balance under itself. -/
theorem BalanceNotLowered.refl (index : Nat) (state : BeaconState preset fork) :
    BalanceNotLowered index state state :=
  fun earlier found => ⟨earlier, found, UInt64.le_refl _⟩

/-- Two steps that lower no balance at a position lower none there. -/
theorem BalanceNotLowered.trans {index : Nat} {first second third : BeaconState preset fork}
    (one : BalanceNotLowered index first second) (two : BalanceNotLowered index second third) :
    BalanceNotLowered index first third := by
  intro earlier found
  obtain ⟨middle, atMiddle, low⟩ := one earlier found
  obtain ⟨later, atThird, lower⟩ := two middle atMiddle
  exact ⟨later, atThird, UInt64.le_trans low lower⟩

/-- A step that keeps the balances lowers none. -/
theorem BalanceNotLowered.of_balances (same : after.balances = state.balances) (index : Nat) :
    BalanceNotLowered index state after := by
  intro earlier found
  exact ⟨earlier, by rw [same]; exact found, UInt64.le_refl _⟩

/-- A validator with a flag of the previous epoch participates with it there.

This holds when the read of the participants succeeds.

The previous epoch must not be the current one.

The validator is active in the previous epoch and unslashed, at a position below `2^64`. -/
theorem mem_getUnslashedParticipatingIndices_of_flag {altair : .altair ≤ fork}
    {flagIndex : UInt64} {result : List ValidatorIndex}
    (computed : getUnslashedParticipatingIndices state altair flagIndex (getPreviousEpoch state) =
      .ok result)
    (differ : getPreviousEpoch state ≠ getCurrentEpoch state) {index : Nat} (small : index < 2 ^ 64)
    {validator : Validator} (found : state.validators.data[index]? = some validator)
    (active : isActiveValidator validator (getPreviousEpoch state) = true)
    (unslashed : validator.slashed = false) {flags : ParticipationFlags}
    (flagged : (state.previousEpochParticipation altair).data[index]? = some flags)
    (set : hasFlag flags flagIndex = true) :
    index.toUInt64 ∈ result := by
  have fits : index.toUInt64.toNat = index := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' small]
  unfold getUnslashedParticipatingIndices at computed
  dsimp only at computed
  rw [ite_eq_left (Or.inl rfl), ite_eq_right differ] at computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨activeIndices, checked, read, readOk, rfl⟩ := computed
  have member : index.toUInt64 ∈ activeIndices :=
    (mem_iff_of_getActiveValidatorIndicesChecked_ok checked).mpr
      ⟨validator, by rw [fits]; exact found, active⟩
  obtain ⟨entry, listed, step⟩ := exists_mem_of_mapM_ok readOk member
  have looked : getValidator state index.toUInt64 = .ok validator :=
    getValidator_eq_ok_iff.mpr (by rw [fits]; exact found)
  rw [fits, flagged] at step
  simp only [looked, bind, Except.bind, Except.ok.injEq] at step
  subst step
  simp only [List.mem_map, List.mem_filter]
  exact ⟨_, ⟨listed, by simp [set, unslashed]⟩, rfl⟩

/-- From Altair, a pending deposit keeps each validator and the consolidations.

It lowers no balance at a position that holds a validator. -/
theorem applyPendingDeposit_balanceNotLowered {deposit : PendingDeposit} (altair : .altair ≤ fork)
    (computed : applyPendingDeposit config checks state deposit = .ok after) {index : Nat}
    (inside : index < state.validators.data.size) :
    ValidatorsKept state after ∧ BalanceNotLowered index state after ∧
      after.pendingConsolidations = state.pendingConsolidations := by
  rcases applyPendingDeposit_cases computed with rfl | ⟨position, raised⟩ | ⟨-, added⟩
  · exact ⟨ValidatorsKept.refl _, BalanceNotLowered.refl index _, rfl⟩
  · refine ⟨ValidatorsKept.of_eq (increaseBalance_validators raised), fun earlier found => ?_, ?_⟩
    · obtain ⟨later, atLater, grown⟩ := balance_increaseBalance raised found
      refine ⟨later, atLater, UInt64.le_iff_toNat_le.mpr ?_⟩
      rw [grown]
      exact Nat.le_add_right _ _
    · obtain ⟨_, _, rfl⟩ := increaseBalance_eq_ok_iff.mp raised
      rfl
  · obtain ⟨kept, balance, consolidations, -⟩ := addValidatorToRegistry_kept altair added inside
    exact ⟨kept, fun earlier found => ⟨earlier, by rw [balance]; exact found, UInt64.le_refl _⟩,
      consolidations⟩

/-- A pass over pending deposits keeps each validator and the consolidations.

It lowers no balance at a position that holds a validator. -/
theorem passPendingDeposits_balanceNotLowered {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} (altair : .altair ≤ fork) {index : Nat} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      index < state.validators.data.size →
      ValidatorsKept state pass.1.state ∧ BalanceNotLowered index state pass.1.state ∧
        pass.1.state.pendingConsolidations = state.pendingConsolidations
  | [], _, _, _, _, _, computed, _ => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨ValidatorsKept.refl _, BalanceNotLowered.refl index _, rfl⟩
  | deposit :: rest, state, processed, count, postponed, pass, computed, inside => by
    -- An applied deposit keeps the validator at the position, for the rest of the pass.
    have next {middle : BeaconState preset fork}
        (credited : applyPendingDeposit config checks state deposit = .ok middle)
        {pass : PendingDepositsPass preset fork}
        (rested : index < middle.validators.data.size →
          ValidatorsKept middle pass.state ∧ BalanceNotLowered index middle pass.state ∧
            pass.state.pendingConsolidations = middle.pendingConsolidations) :
        ValidatorsKept state pass.state ∧ BalanceNotLowered index state pass.state ∧
          pass.state.pendingConsolidations = state.pendingConsolidations := by
      obtain ⟨kept, raised, consolidations⟩ :=
        applyPendingDeposit_balanceNotLowered altair credited inside
      obtain ⟨_, atMiddle, -⟩ := kept index _ (Array.getElem?_eq_getElem inside)
      obtain ⟨kept', raised', consolidations'⟩ :=
        rested (Array.getElem?_eq_some_iff.mp atMiddle).1
      exact ⟨kept.trans kept', raised.trans raised', consolidations'.trans consolidations⟩
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      exact ⟨ValidatorsKept.refl _, BalanceNotLowered.refl index _, rfl⟩
    split at computed
    · cases computed
    split at computed
    · split at computed
      · cases computed
      rename_i credited
      split at computed
      · cases computed
      cases computed
      exact next credited fun inside' =>
        passPendingDeposits_balanceNotLowered altair (deposits := rest) ‹_› inside'
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact passPendingDeposits_balanceNotLowered altair (deposits := rest) ‹_› inside
    split at computed
    · cases computed
    split at computed
    · cases computed
      exact ⟨ValidatorsKept.refl _, BalanceNotLowered.refl index _, rfl⟩
    split at computed
    · cases computed
    rename_i credited
    split at computed
    · cases computed
    cases computed
    exact next credited fun inside' =>
      passPendingDeposits_balanceNotLowered altair (deposits := rest) ‹_› inside'

/-- From Electra, the pending deposits keep each validator and the consolidations.

They lower no balance at a position that holds a validator. -/
theorem processPendingDeposits_balanceNotLowered {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) {index : Nat}
    (inside : index < state.validators.data.size) :
    ValidatorsKept state after ∧ BalanceNotLowered index state after ∧
      after.pendingConsolidations = state.pendingConsolidations := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals exact passPendingDeposits_balanceNotLowered altair ‹_› inside

/-- A pass over pending consolidations lowers no balance of a validator that is no source. -/
theorem passPendingConsolidations_balanceNotLowered {nextEpoch : Epoch} {index : Nat} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork} {result},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      (∀ consolidation ∈ consolidations, consolidation.sourceIndex.toNat ≠ index) →
      BalanceNotLowered index state result.1
  | [], _, _, computed, _ => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact BalanceNotLowered.refl index _
  | consolidation :: rest, state, result, computed, unsourced => by
    have others : ∀ c ∈ rest, c.sourceIndex.toNat ≠ index :=
      fun c member => unsourced c (List.mem_cons_of_mem _ member)
    unfold passPendingConsolidations at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
    split at computed
    · split at computed
      · cases computed
      rename_i recur
      cases computed
      exact (passPendingConsolidations_balanceNotLowered recur others :)
    split at computed
    · cases computed
      exact BalanceNotLowered.refl index _
    split at computed
    · cases computed
    split at computed
    · cases computed
    rename_i lowered loweredOk
    split at computed
    · cases computed
    rename_i raised raisedOk
    split at computed
    · cases computed
    rename_i recur
    cases computed
    -- The source differs from the position, and the target only gains.
    have step : BalanceNotLowered index state raised := by
      intro earlier found
      obtain ⟨kept, keptAt, keptEq⟩ := balance_decreaseBalance (liftAccessor_ok.mp loweredOk) found
      rw [ite_eq_right_of_eq_false _ _
        (eq_false (unsourced consolidation List.mem_cons_self))] at keptEq
      obtain ⟨grown, grownAt, grownEq⟩ :=
        balance_increaseBalance (liftAccessor_ok.mp raisedOk) keptAt
      refine ⟨grown, grownAt, UInt64.le_iff_toNat_le.mpr ?_⟩
      rw [grownEq, keptEq]
      exact Nat.le_add_right _ _
    exact step.trans (passPendingConsolidations_balanceNotLowered recur others :)

/-- From Electra, the pending consolidations lower no balance of a validator that is no source.

The consolidations are those of the queue before the step. -/
theorem processPendingConsolidations_balanceNotLowered {electra : .pectra ≤ fork}
    (computed : processPendingConsolidations state electra = .ok after) {index : Nat}
    (unsourced : ∀ consolidation ∈ (state.pendingConsolidations electra).data,
      consolidation.sourceIndex.toNat ≠ index) :
    BalanceNotLowered index state after := by
  obtain ⟨result, passed, balances, -⟩ := processPendingConsolidations_pass computed
  intro earlier found
  obtain ⟨later, atLater, low⟩ := passPendingConsolidations_balanceNotLowered passed
    (fun c member => unsourced c (by simpa using member)) earlier found
  exact ⟨later, by rw [balances]; exact atLater, low⟩

/-- One leak epoch of a voter, from Altair.

The epoch transition succeeds, from a state that leaks, and does not raise the finalized epoch.

The registry is within its limit.

The validator is unslashed, and no pending consolidation has it as its source.

If it is eligible, its flags of the previous epoch have the timely source and the timely target.

After the epoch its balance is no lower.

Its new effective balance is the update of the old one from that balance.

The update uses the largest effective balance of the validator before the epoch.

It keeps its key and its withdrawal credentials.

The epoch that advances finality is not covered. -/
theorem voterEpoch_processEpoch (altair : .altair ≤ fork)
    (computed : processEpoch config checks state = .ok after)
    (within : state.RegistryWithinLimit) (leak : isInInactivityLeak state = .ok true)
    (stalled : after.finalizedCheckpoint.epoch ≤ state.finalizedCheckpoint.epoch)
    {index : Nat} {validator : Validator} (found : state.validators.data[index]? = some validator)
    (unslashed : validator.slashed = false)
    (voted : isEligibleValidator (getPreviousEpoch state) validator = .ok true →
      ∃ flags, (state.previousEpochParticipation altair).data[index]? = some flags ∧
        hasFlag flags TIMELY_SOURCE_FLAG_INDEX = true ∧
        hasFlag flags TIMELY_TARGET_FLAG_INDEX = true)
    (unsourced : ∀ electra : .pectra ≤ fork,
      ∀ consolidation ∈ (state.pendingConsolidations electra).data,
        consolidation.sourceIndex.toNat ≠ index) :
    ∃ balance settled effective now,
      state.balances.data[index]? = some balance ∧
      after.balances.data[index]? = some settled ∧ balance ≤ settled ∧
      updatedEffectiveBalance preset (withdrawalMaxEffectiveBalance preset fork validator) settled
        validator.effectiveBalance = .ok effective ∧
      after.validators.data[index]? = some now ∧ now.effectiveBalance = effective ∧
      now.pubkey = validator.pubkey ∧
      now.withdrawalCredentials = validator.withdrawalCredentials := by
  have altairRun : processEpochAltair config checks state altair = .ok after := by
    unfold processEpoch at computed
    simpa only [altair, ↓reduceDIte] using computed
  rw [processEpochAltair_eq_run] at altairRun
  have trace := EpochTrace.run_ok_iff.mp altairRun
  change EpochTrace _ (.justification :: .inactivity :: .rewards :: .registry :: .slashings ::
    .eth1Reset :: .pendingDeposits :: .pendingConsolidations :: .payments ::
    .effectiveBalances :: [.slashingsReset, .randaoReset, .history, .participation,
      .syncCommittees, .proposerLookahead, .ptcWindow]) _ _ at trace
  obtain _ | ⟨justifiedOk, trace⟩ := trace
  obtain _ | ⟨scoredOk, trace⟩ := trace
  obtain _ | ⟨rewardedOk, trace⟩ := trace
  obtain _ | ⟨registeredOk, trace⟩ := trace
  obtain _ | ⟨slashedOk, trace⟩ := trace
  obtain _ | ⟨resetOk, trace⟩ := trace
  obtain _ | ⟨depositedOk, trace⟩ := trace
  obtain _ | ⟨consolidatedOk, trace⟩ := trace
  obtain _ | ⟨settledOk, trace⟩ := trace
  obtain _ | ⟨updatedOk, trace⟩ := trace
  rename_i justified scored rewarded registered slashed reset deposited consolidated settled
    updated
  have justifiedEq : processJustificationAndFinalization state = .ok justified :=
    EpochStage.action_cases.mp justifiedOk
  have scoredEq := EpochStage.action_cases.mp scoredOk
  simp only [EpochStage.Edge, altair, ↓reduceDIte] at scoredEq
  have rewardedEq : processRewardsAndPenalties config scored = .ok rewarded :=
    EpochStage.action_cases.mp rewardedOk
  have registeredEq : processRegistryUpdates config rewarded = .ok registered :=
    EpochStage.action_cases.mp registeredOk
  have slashedEq : processSlashings registered = .ok slashed :=
    EpochStage.action_cases.mp slashedOk
  have updatedEq : processEffectiveBalanceUpdates settled = .ok updated :=
    EpochStage.action_cases.mp updatedOk
  -- Justification keeps the balances, the registry, the consolidations and the flags.
  have justifiedSame : justified.balances = state.balances ∧
      justified.validators = state.validators ∧
      justified.pendingConsolidations = state.pendingConsolidations ∧
      justified.previousEpochParticipation = state.previousEpochParticipation := by
    obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok justifiedEq
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
      exact ⟨by rw [← rest], by rw [← rest], by rw [← rest], by rw [← rest]⟩
  -- Finality does not advance, so the state after justification leaks.
  obtain ⟨justified', justifiedOk', advanced⟩ :=
    processEpoch_finalized_lt_or_isInInactivityLeak leak computed
  have sameJustified : justified' = justified :=
    Except.ok.inj (justifiedOk'.symm.trans justifiedEq)
  rw [sameJustified] at advanced
  have leaking : isInInactivityLeak justified = .ok true :=
    advanced.resolve_left fun lt => absurd stalled (UInt64.not_le.mpr lt)
  have previousEq : getPreviousEpoch justified = getPreviousEpoch state := by
    unfold getPreviousEpoch getCurrentEpoch
    rw [processJustificationAndFinalization_slot justifiedEq]
  have withinJustified : justified.RegistryWithinLimit := by
    unfold BeaconState.RegistryWithinLimit
    rw [justifiedSame.2.1]
    exact within
  have inside : index < state.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
  have insideJustified : index < justified.validators.data.size := by
    rw [justifiedSame.2.1]
    exact inside
  have foundJustified : justified.validators.data[index]? = some validator := by
    rw [justifiedSame.2.1]
    exact found
  have atJustified : justified.validators.data[index] = validator :=
    (Array.getElem?_eq_some_iff.mp foundJustified).2
  -- The scores and the rewards keep the registry and the consolidations.
  have scoredFrame := processInactivityUpdates_frame scoredEq
  have rewardedFrame := processRewardsAndPenalties_frame rewardedEq
  have rewardedValidators : rewarded.validators = state.validators :=
    (congrArg BeaconState.validators rewardedFrame).trans
      ((congrArg BeaconState.validators scoredFrame).trans justifiedSame.2.1)
  have rewardedConsolidations : rewarded.pendingConsolidations = state.pendingConsolidations :=
    (congrArg BeaconState.pendingConsolidations rewardedFrame).trans
      ((congrArg BeaconState.pendingConsolidations scoredFrame).trans justifiedSame.2.2.1)
  -- The validator has a balance, since the rewards read one at each position.
  have later : getCurrentEpoch scored ≠ GENESIS_EPOCH := by
    have slot : scored.slot = justified.slot :=
      (congrArg BeaconState.slot scoredFrame).trans rfl
    unfold getCurrentEpoch
    rw [slot]
    exact getCurrentEpoch_ne_genesis_of_leak leaking
  obtain ⟨balance, atScored⟩ := balances_present_of_altair altair later rewardedEq index
    (by rw [congrArg BeaconState.validators scoredFrame]; exact insideJustified)
  have atBalance : state.balances.data[index]? = some balance := by
    rw [← justifiedSame.1, ← congrArg BeaconState.balances scoredFrame]
    exact atScored
  -- In a leak the rewards keep the balance of a voter, and of a validator that is not eligible.
  obtain ⟨total, source, target, -, sourceOk, targetOk, facts⟩ :=
    processRewardsAndPenalties_of_leak altair withinJustified leaking scoredEq rewardedEq
  obtain ⟨isEligible, eligibleOk, notEligible, -⟩ := facts index insideJustified
  rw [atJustified, previousEq] at eligibleOk
  have rewardedBalance : rewarded.balances.data[index]? = justified.balances.data[index]? := by
    cases isEligible with
    | false => exact (notEligible rfl).1
    | true =>
      obtain ⟨flags, flagged, sourceSet, targetSet⟩ := voted eligibleOk
      have active : isActiveValidator validator (getPreviousEpoch justified) = true := by
        rw [previousEq]
        cases isActive : isActiveValidator validator (getPreviousEpoch state)
        · simp [isEligibleValidator, isActive, unslashed, pure, Except.pure] at eligibleOk
        · rfl
      have small : index < 2 ^ 64 := by
        have limit := preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
        unfold BeaconState.RegistryWithinLimit at within
        omega
      have differ : getPreviousEpoch justified ≠ getCurrentEpoch justified := by
        have positive : (getCurrentEpoch justified).toNat ≠ 0 := fun zero =>
          getCurrentEpoch_ne_genesis_of_leak leaking
            (UInt64.toNat_inj.mp (by simpa [GENESIS_EPOCH] using zero))
        intro same
        have := getPreviousEpoch_toNat justified
        rw [same] at this
        omega
      have flaggedJustified :
          (justified.previousEpochParticipation altair).data[index]? = some flags := by
        rw [justifiedSame.2.2.2]
        exact flagged
      exact processRewardsAndPenalties_of_leak_voter altair withinJustified leaking scoredEq
        rewardedEq sourceOk targetOk insideJustified
        (mem_getUnslashedParticipatingIndices_of_flag sourceOk differ small foundJustified active
          unslashed flaggedJustified sourceSet)
        (mem_getUnslashedParticipatingIndices_of_flag targetOk differ small foundJustified active
          unslashed flaggedJustified targetSet)
  -- The registry updates keep the validator unslashed, and keep the balances.
  obtain ⟨registryKept, registryConsolidations⟩ := processRegistryUpdates_kept registeredEq
  have foundRewarded : rewarded.validators.data[index]? = some validator := by
    rw [rewardedValidators]
    exact found
  obtain ⟨atRegistered, foundRegistered, sameRegistered⟩ :=
    registryKept index validator foundRewarded
  have insideRegistered : index < registered.validators.data.size :=
    (Array.getElem?_eq_some_iff.mp foundRegistered).1
  -- The slashings charge only slashed validators.
  have slashedFrame := processSlashings_frame slashedEq
  have slashedBalance : slashed.balances.data[index]? = registered.balances.data[index]? := by
    have notDue : ∀ epoch, ¬ SlashingPenaltyDue preset epoch atRegistered := fun _ due => by
      have charged := due.1
      rw [sameRegistered.2.2.2, unslashed] at charged
      exact Bool.false_ne_true charged
    by_cases electra : .pectra ≤ fork
    · have withinRegistered : registered.RegistryWithinLimit := by
        unfold BeaconState.RegistryWithinLimit
        rw [(sameSizes_processRegistryUpdates registeredEq).1, rewardedValidators]
        exact within
      obtain ⟨_, _, _, _, each⟩ :=
        processSlashings_balances_of_electra electra withinRegistered slashedEq
      obtain ⟨charged, atCharged, balanceEq⟩ := (each index).1 insideRegistered
      rw [foundRegistered, Option.some.injEq] at atCharged
      subst atCharged
      rw [balanceEq]
      simp [notDue]
    · obtain ⟨_, _, _, _, each⟩ :=
        processSlashings_balances_of_lt_electra (Nat.lt_of_not_le electra) slashedEq
      obtain ⟨charged, atCharged, balanceEq⟩ := (each index).1 insideRegistered
      rw [foundRegistered, Option.some.injEq] at atCharged
      subst atCharged
      rw [balanceEq]
      simp [notDue]
  -- The reset of the votes keeps the registry, the balances and the consolidations.
  have resetSame : reset.validators = slashed.validators ∧ reset.balances = slashed.balances ∧
      reset.pendingConsolidations = slashed.pendingConsolidations := by
    have edge := EpochStage.action_cases.mp resetOk
    simp only [EpochStage.Edge] at edge
    split at edge
    · have frame := processEth1DataReset_frame edge
      exact ⟨by rw [frame], by rw [frame], by rw [frame]⟩
    · subst edge
      exact ⟨rfl, rfl, rfl⟩
  -- The deposits only raise balances.
  have insideReset : index < reset.validators.data.size := by
    rw [resetSame.1, congrArg BeaconState.validators slashedFrame]
    exact insideRegistered
  have depositedStep : ValidatorsKept reset deposited ∧ BalanceNotLowered index reset deposited ∧
      deposited.pendingConsolidations = reset.pendingConsolidations := by
    have edge := EpochStage.action_cases.mp depositedOk
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact processPendingDeposits_balanceNotLowered edge insideReset
    · subst edge
      exact ⟨ValidatorsKept.refl _, BalanceNotLowered.refl index _, rfl⟩
  -- The consolidations lower only their sources.
  have consolidatedStep : consolidated.validators = deposited.validators ∧
      BalanceNotLowered index deposited consolidated := by
    have edge := EpochStage.action_cases.mp consolidatedOk
    simp only [EpochStage.Edge] at edge
    split at edge
    · rename_i electra
      refine ⟨(processPendingConsolidations_kept edge).1,
        processPendingConsolidations_balanceNotLowered edge ?_⟩
      rw [depositedStep.2.2, resetSame.2.2, congrArg BeaconState.pendingConsolidations slashedFrame,
        registryConsolidations, rewardedConsolidations]
      exact unsourced electra
    · subst edge
      exact ⟨rfl, BalanceNotLowered.refl index _⟩
  -- The builder payments keep the balances and the registry.
  have settledSame : settled.validators = consolidated.validators ∧
      settled.balances = consolidated.balances := by
    have edge := EpochStage.action_cases.mp settledOk
    simp only [EpochStage.Edge] at edge
    split at edge
    · have frame := processBuilderPendingPayments_eq edge
      exact ⟨by rw [frame], by rw [frame]⟩
    · subst edge
      exact ⟨rfl, rfl⟩
  have toRewarded : BalanceNotLowered index state rewarded := fun earlier atEarlier =>
    ⟨earlier, by rw [rewardedBalance, justifiedSame.1]; exact atEarlier, UInt64.le_refl _⟩
  have toSlashed : BalanceNotLowered index registered slashed := fun earlier atEarlier =>
    ⟨earlier, by rw [slashedBalance]; exact atEarlier, UInt64.le_refl _⟩
  have notLowered : BalanceNotLowered index state settled :=
    toRewarded.trans <| (BalanceNotLowered.of_balances
      (processRegistryUpdates_balances registeredEq) index).trans <| toSlashed.trans <|
      (BalanceNotLowered.of_balances resetSame.2.1 index).trans <| depositedStep.2.1.trans <|
      consolidatedStep.2.trans (BalanceNotLowered.of_balances settledSame.2 index)
  obtain ⟨settledBalance, owned, low⟩ := notLowered balance atBalance
  -- The validator keeps its effective balance and its credentials until the update.
  have keptAll : ValidatorsKept rewarded settled :=
    registryKept.trans <|
      (ValidatorsKept.of_eq (congrArg BeaconState.validators slashedFrame)).trans <|
      (ValidatorsKept.of_eq resetSame.1).trans <| depositedStep.1.trans <|
      ValidatorsKept.of_eq (settledSame.1.trans consolidatedStep.1)
  obtain ⟨kept, atKept, sameKept⟩ := keptAll index validator foundRewarded
  obtain ⟨effective, atUpdated, effectiveOk⟩ :=
    processEffectiveBalanceUpdates_effectiveBalance_eq updatedEq atKept owned
  rw [sameKept.2.1, withdrawalMaxEffectiveBalance_of_credentials sameKept.2.2.1] at effectiveOk
  have tail := sameBalancesRegistryScores_tail altair trace
  refine ⟨balance, settledBalance, effective, { kept with effectiveBalance := effective },
    atBalance, ?_, low, effectiveOk, ?_, rfl, sameKept.1, sameKept.2.2.1⟩
  · rw [tail.1, processEffectiveBalanceUpdates_balances updatedEq]
    exact owned
  · rw [tail.2.1]
    exact atUpdated

/-- The slot that ends an epoch of a leak, for one voter, from Altair.

The slot after the state is the first of an epoch, so this slot runs the epoch transition.

The conclusions of one leak epoch of a voter then hold across the slot. -/
theorem voterEpoch_advanceSlot (altair : .altair ≤ fork)
    (computed : advanceSlot config checks state = .ok after)
    (ends : (state.slot + 1) % preset.SLOTS_PER_EPOCH = 0)
    (within : state.RegistryWithinLimit) (leak : isInInactivityLeak state = .ok true)
    (stalled : after.finalizedCheckpoint.epoch ≤ state.finalizedCheckpoint.epoch)
    {index : Nat} {validator : Validator} (found : state.validators.data[index]? = some validator)
    (unslashed : validator.slashed = false)
    (voted : isEligibleValidator (getPreviousEpoch state) validator = .ok true →
      ∃ flags, (state.previousEpochParticipation altair).data[index]? = some flags ∧
        hasFlag flags TIMELY_SOURCE_FLAG_INDEX = true ∧
        hasFlag flags TIMELY_TARGET_FLAG_INDEX = true)
    (unsourced : ∀ electra : .pectra ≤ fork,
      ∀ consolidation ∈ (state.pendingConsolidations electra).data,
        consolidation.sourceIndex.toNat ≠ index) :
    ∃ balance settled effective now,
      state.balances.data[index]? = some balance ∧
      after.balances.data[index]? = some settled ∧ balance ≤ settled ∧
      updatedEffectiveBalance preset (withdrawalMaxEffectiveBalance preset fork validator) settled
        validator.effectiveBalance = .ok effective ∧
      after.validators.data[index]? = some now ∧ now.effectiveBalance = effective ∧
      now.pubkey = validator.pubkey ∧
      now.withdrawalCredentials = validator.withdrawalCredentials := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have same : next = state.slot + 1 := by
    apply UInt64.toNat_inj.mp
    have bound := next.toNat_lt_size
    rw [sum, UInt64.toNat_add, UInt64.toNat_one]
    simp only [UInt64.size] at bound
    omega
  unfold epochIfLast at epochedOk
  simp only [same, ends, ↓reduceIte] at epochedOk
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  exact voterEpoch_processEpoch altair epochedOk within leak stalled found unslashed voted unsourced

end EthLib.Consensus
