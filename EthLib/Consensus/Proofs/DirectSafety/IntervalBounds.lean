module

public import EthLib.Consensus.Proofs.DirectSafety.DepartureQueue
public import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
import EthLib.Consensus.Proofs.DirectSafety.FundingBlock
import EthLib.Consensus.Proofs.DirectSafety.FundingSlot
import EthLib.Consensus.Proofs.Transition.ValidatorCaps

/-!
# Departure charges over a funded window

The departure charges of a run are bounded by a window of queue capacity.

That bound reads a cap on the consolidation churn at each step of the run.

Here the cap is derived: the churn of a step is a rate of the active stake where it starts.

The active stake of every state of the run is at most the funded stake of the window.

The funded stake counts the stake at the first state and the funding that the run replays.

It does not depend on the endpoint of the run, so it bounds every state inside the run.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Classical

noncomputable section

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- With a withdrawal delay of two epochs, active stake fits the funded window. -/
private theorem active_stake_le_window {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .glamsterdam)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    Models.stake (effectiveWeight y.state) (activeKeys y.state) ≤
      activeStakeWindow (config := config) x high events := by
  have ⟨_, _, _, initialized⟩ := genesis
  apply funding_window_of_steps tail early delay
    ((validatorKeys_prefix_and_distinct_of_genesis_chainSteps initialized
      (shared.append tail).chainSteps).2) high endEpoch events replayed
  intro a b pre step before added addedOk
  have reachable := shared.append pre
  have holds := reachable.invariant_of_genesis genesis
  cases step with
  | slot ok =>
    exact funding_slot before delay holds.balancesMatch holds.exitsOrdered
      (reachable.activationExitOrder genesis)
      (fun witness => reachable.pendingConsolidation_invariant genesis
        (Nat.lt_of_le_of_lt (Step.slot ok).chainStep.fork_le before) witness (by omega))
      ok added addedOk
  | block engine signed due ok =>
    have processed := (applySignedBlock_ok ok).2.1
    have bound := funding_block before holds.balancesMatch engine signed.message
      processed added (Step.balanceEvents_block before addedOk)
    have slot := (frame_processBlock processed).slot
    simpa only [getCurrentEpoch, slot, Nat.sub_self, Nat.zero_mul, Nat.add_zero] using bound

private theorem registry_fold_bound {fork : Fork} {α : Type}
    {action : BeaconState preset fork → α → Except TransitionError (BeaconState preset fork)}
    (bound : ∀ s a t, action s a = .ok t →
      t.validators.data.size ≤ s.validators.data.size + 1)
    {items : List α} {s t : BeaconState preset fork}
    (ok : items.foldlM action s = .ok t) :
    t.validators.data.size ≤ s.validators.data.size + items.length := by
  induction items generalizing s with
  | nil => cases ok; simp
  | cons a rest ih =>
    simp only [List.foldlM_cons, bind_ok_iff] at ok
    obtain ⟨middle, first, last⟩ := ok
    have one := bound s a middle first
    have remaining := ih last
    simp only [List.length_cons]
    omega

private theorem registry_pending_bound {fork : Fork} {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork}
    (ok : processPendingDeposits config checks s electra = .ok t) :
    t.validators.data.size ≤ s.validators.data.size +
      preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  -- Applied deposits form a sublist of the bounded prefix read by this pass.
  obtain ⟨read, rest, applied, postponed, next, pending, carried,
    _, _, cap, subset, _, _, folded, rfl⟩ := processPendingDeposits_applied ok
  have growth := registry_fold_bound
    (fun _ _ _ h => (applyPendingDeposit_validators_size_le_and_mem h).1) folded
  have count := subset.length_le
  dsimp only
  omega

private theorem registry_deposit_bound {fork : Fork} {s t : BeaconState preset fork}
    {before : fork < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) :
    t.validators.data.size ≤ s.validators.data.size + 1 := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok ok
  rcases applyDeposit_cases applied with rfl | ⟨_, _, _, rfl | added, rfl⟩ | ⟨_, applied⟩
  · exact Nat.le_succ _
  · exact Nat.le_succ _
  · rw [show _ = _ from addValidatorToRegistry_validators_eq_push added]
    simp
  · exact (applyPendingDeposit_validators_size_le_and_mem applied).1

private theorem registry_fold_size {fork : Fork} {α : Type}
    {action : BeaconState preset fork → α → Except TransitionError (BeaconState preset fork)}
    (keeps : ∀ s a t, action s a = .ok t → t.validators.data.size = s.validators.data.size)
    {items : List α} {s t : BeaconState preset fork}
    (ok : items.foldlM action s = .ok t) : t.validators.data.size = s.validators.data.size :=
  foldlM_ok_invariant (fun t => t.validators.data.size = s.validators.data.size)
    (fun _ _ _ prior ok => (keeps _ _ _ ok).trans prior) rfl ok

private theorem registry_operations_bound {fork : Fork} {s t : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {parentSlot : Slot} (early : fork < .glamsterdam)
    (ok : processOperations config checks s body parentSlot = .ok t) :
    t.validators.data.size ≤ s.validators.data.size + preset.MAX_DEPOSITS.toNat := by
  have notGloas : ¬ Fork.glamsterdam ≤ fork := fun h => Nat.not_le.mpr early h
  simp only [processOperations, notGloas, ↓reduceDIte,
    bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, _, _, _, a, proposers, b, attesters, c, attestations, d, deposits,
    e, exits, f, changes, requests⟩ := ok
  have sa := registry_fold_size (fun _ _ _ h => (sameSizes_processProposerSlashing h).1) proposers
  have sb := registry_fold_size (fun _ _ _ h => (sameSizes_processAttesterSlashing h).1) attesters
  have sc := registry_fold_size (fun _ _ _ h => (sameSizes_processAttestation h).1) attestations
  have sd := registry_fold_bound (fun _ _ _ h => registry_deposit_bound h) deposits
  have se := registry_fold_size (fun _ _ _ h => (sameSizes_processVoluntaryExit h).1) exits
  have sf : f.validators.data.size = e.validators.data.size := by
    unfold processBlsToExecutionChanges at changes
    split at changes
    · rw [← Array.foldlM_toList] at changes
      exact registry_fold_size (fun _ _ _ h => (sameSizes_processBlsToExecutionChange h).1) changes
    · cases changes; rfl
  have st : t.validators.data.size = f.validators.data.size := by
    split at requests
    · exact (sameSizes_processExecutionRequests requests).1
    · cases requests; rfl
  have cap := (body.deposits (Nat.lt_trans early (by decide))).bound early
  simp only [Array.length_toList] at sd
  omega

/-- A block adds at most its deposits to the registry.

The steps before the operations and the sync aggregate keep the validators before Gloas. -/
private theorem registry_block_bound {fork : Fork} {s t : BeaconState preset fork}
    {block : BeaconBlock preset fork} {engine : ExecutionEngine preset fork}
    (early : fork < .glamsterdam)
    (ok : processBlock config checks engine s block = .ok t) :
    t.validators.data.size ≤ s.validators.data.size + preset.MAX_DEPOSITS.toNat := by
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput ok
  have head := OperationsInput.validators_eq early started
  have tail : t.validators.data.size = last.validators.data.size := by
    split at synced
    · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
      rfl
    · cases synced
      rfl
  have bound := registry_operations_bound early operated
  rw [head] at bound
  omega

/-- An epoch adds at most one epoch of pending deposits to the registry.

The epoch is cut at its pending deposits: every other stage keeps the size of the registry. -/
private theorem registry_epoch_bound {fork : Fork} {s t : BeaconState preset fork}
    (ok : processEpoch config checks s = .ok t) :
    t.validators.data.size ≤ s.validators.data.size +
      preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  have trace := processEpoch_trace ok
  change EpochTrace _ ([.justification, .inactivity, .rewards, .registry, .slashings,
    .eth1Reset] ++ (.pendingDeposits :: .pendingConsolidations :: EpochStage.middleStages ++
      EpochStage.tailStages)) _ _ at trace
  obtain ⟨reset, head, rest⟩ := EpochTrace.append_iff.mp trace
  cases rest
  rename_i deposited depositedOk rest
  -- Every stage other than the pending deposits keeps the size of the registry.
  have same {ks : List EpochStage} {a b : BeaconState preset fork}
      (trace : EpochTrace (EpochStage.action config checks) ks a b)
      (without : EpochStage.pendingDeposits ∉ ks) :
      b.validators.data.size = a.validators.data.size := by
    refine trace.transport
      (fun a b : BeaconState preset fork => b.validators.data.size = a.validators.data.size)
      (fun _ => rfl) (fun one two => two.trans one) ?_
    intro k member a b computed
    have edge := EpochStage.action_cases.mp computed
    cases k
    case registry => exact (sameSizes_processRegistryUpdates edge).1
    case effectiveBalances => exact (sameSizes_processEffectiveBalanceUpdates edge).1
    case pendingDeposits => exact absurd member without
    all_goals exact congrArg (·.data.size) (edge.validators_eq ⟨nofun, nofun, nofun⟩)
  have before := same head (by simp)
  have after := same rest (by simp [EpochStage.middleStages, EpochStage.tailStages])
  have edge := EpochStage.action_cases.mp depositedOk
  have middle : deposited.validators.data.size ≤ reset.validators.data.size +
      preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
    simp only [EpochStage.Edge] at edge
    split at edge
    · exact registry_pending_bound edge
    · subst edge
      omega
  omega

private theorem registry_upgrade_size {s : ForkedBeaconState preset}
    {t : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (ok : upgradeNext config checks s = .ok t) :
    t.val.state.validators.data.size = s.state.validators.data.size := by
  obtain ⟨fork, state⟩ := s
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact congrArg Array.size (upgradeToAltair_spec upgraded).1
  · subst ok; rfl
  · subst ok; rfl
  · subst ok; rfl
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact (upgradeToElectra_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact congrArg Array.size (upgradeToFulu_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact congrArg Array.size (upgradeToGloas_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    rfl

private theorem registry_upgrades_size {s t : ForkedBeaconState preset}
    (ok : processUpgrades config checks s = .ok t) :
    t.state.validators.data.size = s.state.validators.data.size :=
  processUpgrades_induction
    (property := fun t => t.state.validators.data.size = s.state.validators.data.size)
    (fun prior ok => (registry_upgrade_size ok).trans prior) rfl ok

private theorem registry_slot_bound {s t : ForkedBeaconState preset}
    (early : t.fork < .glamsterdam)
    (ok : advanceSlotAcross config checks s = .ok t) :
    t.state.slot.toNat = s.state.slot.toNat + 1 ∧
      t.state.validators.data.size ≤ s.state.validators.data.size +
        ((getCurrentEpoch t.state).toNat - (getCurrentEpoch s.state).toNat) *
          preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  simp only [advanceSlotAcross, bind_ok_iff] at ok
  obtain ⟨advanced, slot, upgrades⟩ := ok
  have size := registry_upgrades_size upgrades
  have slotEq := processUpgrades_slot upgrades
  have forward := processUpgrades_fork_le upgrades
  have oldEarly : s.fork < .glamsterdam := Nat.lt_of_le_of_lt forward early
  obtain ⟨next, cached, epoched, nextOk, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok slot
  obtain ⟨_, _, _, _, cacheEq⟩ := processSlot_ok cachedOk
  have cacheSize : cached.validators.data.size = s.state.validators.data.size := by rw [cacheEq]
  have cacheSlot := processSlot_slot cachedOk
  have nextSlot : t.state.slot.toNat = s.state.slot.toNat + 1 := by
    rw [slotEq]
    exact nextOk
  refine ⟨nextSlot, ?_⟩
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    -- Charge the pending-deposit cap only when this slot crosses an epoch boundary.
    have epochs := nextSlot_epoch_of_boundary nextOk boundary
    have growth := registry_epoch_bound epochedOk
    have diff : (getCurrentEpoch t.state).toNat - (getCurrentEpoch s.state).toNat = 1 := by
      rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, slotEq]
      dsimp only
      omega
    rw [diff, one_mul, size]
    dsimp only
    omega
  · cases epochedOk
    rw [size]
    dsimp only
    omega

/-- A block makes its own header the latest one, at the slot of the state. -/
private theorem registry_block_header {fork : Fork} {s t : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    (early : fork < .glamsterdam)
    (ok : processBlock config checks engine s block = .ok t) :
    t.latestBlockHeader.slot = s.slot ∧ s.latestBlockHeader.slot < s.slot := by
  obtain ⟨headed, headerOk⟩ := processBlock_header_of_lt_gloas early ok
  have checked := processBlockHeader_checks headerOk
  refine ⟨?_, checked.1 ▸ checked.2.1⟩
  obtain ⟨_, _, header⟩ := latestBlockHeader_processBlock ok
  rw [header]
  exact checked.1

private def registry_block_allowance (s : ForkedBeaconState preset) : Nat :=
  if s.state.latestBlockHeader.slot < s.state.slot then preset.MAX_DEPOSITS.toNat else 0

private theorem registry_run_bound {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) :
    x.state.slot.toNat ≤ y.state.slot.toNat ∧
      y.state.validators.data.size + registry_block_allowance y ≤
        x.state.validators.data.size +
          (y.state.slot.toNat + 1 - x.state.slot.toNat) * preset.MAX_DEPOSITS.toNat +
          ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) *
            preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  induction tail with
  | nil =>
    constructor
    · exact Nat.le_refl _
    · simp only [Nat.add_sub_cancel_left, Nat.sub_self, Nat.zero_mul, Nat.add_zero, one_mul]
      unfold registry_block_allowance
      split <;> omega
  | @snoc middle last pre step ih =>
    have beforeEarly : middle.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt step.chainStep.fork_le early
    obtain ⟨slotsBefore, bound⟩ := ih beforeEarly
    have epochsBefore : (getCurrentEpoch x.state).toNat ≤
        (getCurrentEpoch middle.state).toNat := by
      rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
      exact Nat.div_le_div_right slotsBefore
    cases step with
    | slot ok =>
      obtain ⟨slot, growth⟩ := registry_slot_bound early ok
      have epochsAfter : (getCurrentEpoch middle.state).toNat ≤
          (getCurrentEpoch last.state).toNat := by
        rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
        exact Nat.div_le_div_right (by omega)
      have epochAdd : (getCurrentEpoch last.state).toNat - (getCurrentEpoch x.state).toNat =
          ((getCurrentEpoch middle.state).toNat - (getCurrentEpoch x.state).toNat) +
          ((getCurrentEpoch last.state).toNat - (getCurrentEpoch middle.state).toNat) := by omega
      have slotAdd : last.state.slot.toNat + 1 - x.state.slot.toNat =
          (middle.state.slot.toNat + 1 - x.state.slot.toNat) + 1 := by omega
      -- Advancing a slot supplies at most one fresh block allowance, even across upgrades.
      have allowance : registry_block_allowance last ≤ preset.MAX_DEPOSITS.toNat := by
        unfold registry_block_allowance
        split <;> omega
      constructor
      · omega
      · rw [slotAdd, epochAdd, Nat.add_mul, Nat.add_mul, one_mul]
        omega
    | @block fork before after engine signed due ok =>
      have processed := (applySignedBlock_ok ok).2.1
      have slot := (frame_processBlock processed).slot
      have header := registry_block_header early processed
      have growth := registry_block_bound early processed
      -- A successful block consumes the allowance and forbids another block at this slot.
      have used : ¬ after.latestBlockHeader.slot < after.slot := by
        rw [header.1, slot]
        exact UInt64.lt_irrefl _
      have oldAllowance : registry_block_allowance ⟨fork, before⟩ =
          preset.MAX_DEPOSITS.toNat := by simp only [registry_block_allowance, header.2, ↓reduceIte]
      have newAllowance : registry_block_allowance ⟨fork, after⟩ = 0 := by
        simp only [registry_block_allowance, used, ↓reduceIte]
      have epoch : getCurrentEpoch after = getCurrentEpoch before := by
        simp only [getCurrentEpoch, slot]
      simp only [oldAllowance] at bound
      simp only [newAllowance, Nat.add_zero, slot, epoch]
      exact ⟨slotsBefore, by omega⟩

/-- The registry envelope is independent of the endpoint, including a mid-epoch start. -/
private theorem registry_le_window {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) :
    y.state.validators.data.size ≤ registryWindow x high := by
  obtain ⟨slots, bound⟩ := registry_run_bound tail early
  have epochs : (getCurrentEpoch x.state).toNat ≤ (getCurrentEpoch y.state).toNat := by
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
    exact Nat.div_le_div_right slots
  have epochCount : (getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat ≤
      driftHorizon x high := by unfold driftHorizon; omega
  have lastSlot : y.state.slot.toNat < (high + 2) * preset.SLOTS_PER_EPOCH.toNat := by
    rw [getCurrentEpoch_toNat] at endEpoch
    apply (Nat.div_lt_iff_lt_mul positive).mp
    omega
  have firstSlot : (getCurrentEpoch x.state).toNat * preset.SLOTS_PER_EPOCH.toNat ≤
      x.state.slot.toNat := by
    rw [getCurrentEpoch_toNat]
    exact Nat.div_mul_le_self _ _
  -- Include the initial slot: the run can start before that slot's block has arrived.
  have slotCount : y.state.slot.toNat + 1 - x.state.slot.toNat ≤
      driftHorizon x high * preset.SLOTS_PER_EPOCH.toNat := by
    unfold driftHorizon
    rw [Nat.sub_mul]
    omega
  have deposits := Nat.mul_le_mul_right preset.MAX_DEPOSITS.toNat slotCount
  have pending := Nat.mul_le_mul_right preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat epochCount
  unfold registryWindow
  rw [Nat.mul_add, ← Nat.mul_assoc]
  omega

/-- The consolidation churn before Gloas is the consolidation rate of the total active balance. -/
private theorem consolidation_rate_le {fork : Fork}
    {s : BeaconState preset fork} (early : fork < .glamsterdam)
    {total churn : Gwei} (read : getTotalActiveBalance s = .ok total)
    (computed : getConsolidationChurnLimit config s = .ok churn)
    {stake : Nat} (bounded : total.toNat ≤ max preset.EFFECTIVE_BALANCE_INCREMENT.toNat stake) :
    churn.toNat ≤ consolidationRate (preset := preset) (config := config) stake := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [getConsolidationChurnLimit, notGloas, ↓reduceIte,
    getActivationExitChurnLimit, getBalanceChurnLimit, read,
    bind, Except.bind, pure, Except.pure, Except.ok.injEq] at computed
  subst churn
  have rounded : ∀ amount : Gwei, (roundToIncrement preset amount).toNat ≤ amount.toNat := by
    intro amount
    have remainder : amount % preset.EFFECTIVE_BALANCE_INCREMENT ≤ amount := by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
      exact Nat.mod_le _ _
    simp only [roundToIncrement, UInt64.toNat_sub_of_le _ _ remainder]
    exact Nat.sub_le _ _
  have subtract : min config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT
      (roundToIncrement preset (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
        (total / config.CHURN_LIMIT_QUOTIENT))) ≤
      roundToIncrement preset (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
        (total / config.CHURN_LIMIT_QUOTIENT)) := by
    rw [UInt64.le_iff_toNat_le, Uint64.toNat_min]
    exact Nat.min_le_right _ _
  rw [UInt64.toNat_sub_of_le _ _ subtract, Uint64.toNat_min]
  have upper := rounded (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
    (total / config.CHURN_LIMIT_QUOTIENT))
  rw [Uint64.toNat_max, UInt64.toNat_div] at upper
  have rate := max_le_max_left config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
    (Nat.div_le_div_right bounded (c := config.CHURN_LIMIT_QUOTIENT.toNat))
  unfold consolidationRate
  omega

/-- Every state inside a run has active stake within the funded window of the whole run.

The window reads the replay of the whole run, and the registry allowance of its epochs. -/
private theorem active_stake_le_window_of_prefix {g x a y : ForkedBeaconState preset}
    (shared : Run config checks g x) (pre : Run config checks x a)
    (rest : Run config checks a y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (slots : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (events : List (BalanceEvent preset))
    (replayed : (pre.append rest).balanceEvents high = .ok events) :
    Models.stake (effectiveWeight a.state) (activeKeys a.state) ≤
      activeStakeWindow (config := config) x high events := by
  have ⟨_, _, _, initialized⟩ := genesis
  have earlyA := Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) early
  have epochA : (getCurrentEpoch a.state).toNat ≤ high + 1 := by
    have ordered := currentEpoch_le_of_chainSteps rest.chainSteps
    rw [UInt64.le_iff_toNat_le] at ordered
    omega
  by_cases funded : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  · obtain ⟨prior, priorOk, initial⟩ := pre.balanceEvents_prefix rest high events replayed
    have bound := active_stake_le_window shared pre genesis earlyA funded high epochA prior
      priorOk
    have credits : (prior.map fundingCredit).sum ≤ (events.map fundingCredit).sum := by
      obtain ⟨remaining, rfl⟩ := initial
      simp only [List.map_append, List.sum_append]
      omega
    simp only [activeStakeWindow, funded, ↓reduceIte] at bound ⊢
    omega
  -- With a shorter delay every registry entry counts with the largest effective balance.
  · have unique := (validatorKeys_prefix_and_distinct_of_genesis_chainSteps initialized
      (shared.append pre).chainSteps).2
    have capped := (shared.append pre).effectiveBalance_capped genesis caps.activation
      caps.compounding earlyA
    have inside (i : ValidatorIndex)
        (member : i ∈ getActiveValidatorIndices a.state (getCurrentEpoch a.state)) :
        i.toNat < a.state.validators.data.size := by
      obtain ⟨v, found, _⟩ :=
        (mem_getActiveValidatorIndices (a.state.validators.bound earlyA)).mp member
      exact (Array.getElem?_eq_some_iff.mp found).1
    have cap (v : Validator) (member : v ∈ a.state.validators.data) :
        v.effectiveBalance.toNat ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := by
      have bound := capped v member
      have activation := UInt64.le_iff_toNat_le.mp caps.activation
      have compounding := UInt64.le_iff_toNat_le.mp caps.compounding
      rw [UInt64.le_iff_toNat_le] at bound
      unfold withdrawalMaxEffectiveBalance getMaxEffectiveBalance at bound
      split at bound
      · split at bound <;> omega
      · omega
    have weight : Models.stake (effectiveWeight a.state) (activeKeys a.state) ≤
        a.state.validators.data.size * preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := by
      rw [activeKeys, keys_weight _ _ unique inside]
      calc
        _ ≤ ∑ _i ∈ Finset.range a.state.validators.data.size,
            preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := by
          apply Finset.sum_le_sum_of_injOn (fun i => i.toNat)
          · intro i _ j _ equal
            exact UInt64.toNat_inj.mp equal
          · intro i member
            obtain ⟨j, chosen, rfl⟩ := Finset.mem_image.mp member
            exact Finset.mem_range.mpr (inside j (List.mem_toFinset.mp chosen))
          · intro i member
            obtain ⟨v, found, _⟩ :=
              (mem_getActiveValidatorIndices (a.state.validators.bound earlyA)).mp
                (List.mem_toFinset.mp member)
            simpa only [found, Option.map_some, Option.getD_some] using
              cap v (Array.mem_of_getElem? found)
          · intro _ _ _
            exact Nat.zero_le _
        _ = _ := by simp
    have size := (registryGrows_of_chainSteps rest.chainSteps).trans
      (registry_le_window (pre.append rest) early high endEpoch slots)
    exact weight.trans (by
      simpa only [activeStakeWindow, funded, ↓reduceIte] using
        Nat.mul_le_mul_right preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat size)

/-- Before Gloas, the departure charges of a run fit a window of funded queue capacity.

The run starts at a state `x` reached from genesis and ends at a state `y` before Gloas.

The bound covers the charges whose exit epoch is at most `high + 1`, and `y` is in the window.

It is the queue carry at `x` plus `H` times the per-epoch caps, where `H = high + 2 - e`.

Here `e` is the current epoch of `x`.

Before Electra at `x`, the caps add the count churn of the registry window at its largest balance.

The caps add `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT` and the consolidation rate of the window.

They add these Electra caps only if the window reaches the Electra fork epoch.

The consolidation rate is computed from the active stake that the funded window allows.

With a withdrawal delay below two epochs, that stake is the registry window at the Electra maximum.

The window reads the balance events that the run replays up to `high`. -/
theorem departure_charges_le_funded_window {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (slots : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    ((tail.departureCharges.filter fun c => c.epoch ≤ high + 1).map (·.amount)).sum ≤
      queueCarry x high + driftHorizon x high *
        ((if x.fork < .pectra then max 1 (cohortCap config (registryWindow x high)) *
          preset.MAX_EFFECTIVE_BALANCE.toNat else 0) +
        (if config.ELECTRA_FORK_EPOCH.toNat ≤ high + 1 then
          config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
          consolidationRate (preset := preset) (config := config)
            (activeStakeWindow (config := config) x high events) else 0)) := by
  have ⟨_, _, _, initialized⟩ := genesis
  have registry := registry_le_window tail early high endEpoch slots
  by_cases preFork : high + 1 < config.ELECTRA_FORK_EPOCH.toNat
  · -- A window before the fork has no Electra state, so it is charged only the count churn.
    have before : x.fork < .pectra := by
      apply Nat.lt_of_not_le
      intro electra
      have started := reachable_electra_epoch shared genesis electra
      have ordered := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tail.chainSteps)
      omega
    have charges := departure_charges_le_window_before_fork shared tail genesis caps early high
      (registryWindow x high) registry before preFork
    have notAfter : ¬ config.ELECTRA_FORK_EPOCH.toNat ≤ high + 1 := Nat.not_le_of_lt preFork
    have notElectra : ¬ .pectra ≤ x.fork := Nat.not_le_of_lt before
    simp only [queueCarry, notElectra, ↓reduceDIte, notAfter, before, ↓reduceIte, Nat.add_zero,
      Nat.zero_add]
    exact charges
  -- Each step starts at a state of the run, whose active stake the funded window bounds.
  have rates {u w : ForkedBeaconState preset} (step : Step config checks u w)
      (contained : tail.Contains step) (_ : .pectra ≤ u.fork) (rate : Gwei)
      (computed : getConsolidationChurnLimit config u.state = .ok rate) :
      rate.toNat ≤ consolidationRate (preset := preset) (config := config)
        (activeStakeWindow (config := config) x high events) := by
    obtain ⟨pre, post, same⟩ := tail.contains_split step contained
    let rest := (Run.nil.snoc step).append post
    have joined : pre.append rest = tail := by
      rw [same, Run.append_assoc]
      rfl
    have earlyU := Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) early
    have notGloas : ¬ .glamsterdam ≤ u.fork := Nat.not_le_of_lt earlyU
    have unique := (validatorKeys_prefix_and_distinct_of_genesis_chainSteps initialized
      (shared.append pre).chainSteps).2
    have bounded := active_stake_le_window_of_prefix shared pre rest genesis caps early high
      endEpoch slots events (joined ▸ replayed)
    cases read : getTotalActiveBalance u.state with
    | error error =>
      simp only [getConsolidationChurnLimit, notGloas, ↓reduceIte,
        getBalanceChurnLimit, read, bind, Except.bind] at computed
      cases computed
    | ok total =>
      obtain ⟨inside, _, totalEq⟩ :=
        getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok read)
      have active := keys_weight u.state _ unique inside
      apply consolidation_rate_le earlyU read computed
      rw [totalEq]
      apply max_le_max_left
      unfold activeKeys at bounded
      rw [active] at bounded
      simpa only [Models.stake, balanceAt] using bounded
  have charges := departure_charges_le_window shared tail genesis caps early high
    (registryWindow x high)
    (consolidationRate (preset := preset) (config := config)
      (activeStakeWindow (config := config) x high events)) registry
    (fun step contained electra rate computed => rates step contained electra rate computed)
  have after : config.ELECTRA_FORK_EPOCH.toNat ≤ high + 1 := Nat.le_of_not_lt preFork
  simp only [after, ↓reduceIte,
    ← Nat.add_assoc (_ : Nat) config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat]
  exact charges

end

end EthLib.Consensus.DirectSafety
