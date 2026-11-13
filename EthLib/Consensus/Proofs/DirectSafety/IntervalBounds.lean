module

public import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
public import EthLib.Consensus.Proofs.DirectSafety.FundingBlock
public import EthLib.Consensus.Proofs.DirectSafety.FundingSlot
import EthLib.Consensus.Proofs.DirectSafety.DepartureQueue
import EthLib.Consensus.Proofs.Transition.SlashedPersistence
import EthLib.Consensus.Proofs.Transition.ValidatorCaps

/-!
# Source bounds over a selected execution interval

The bounds use the concrete balance replay and funding lemmas from IntervalFunding.

No caller supplies the amount of a source or an accounting cap.

The source bounds retain the initial queues, scores and balances needed by arbitrary intervals.

The reference sets are unslashed.

A key slashed at the reference is not in the reference loss.

A key recent at a later state is unslashed there, so it was unslashed at the reference.

That step reads forward persistence: a slashed flag stays set.

The gain bounds are inequalities over these filtered sets, read through one index envelope.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Classical

noncomputable section

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The effective-balance gains of reference-active keys that are recent at the later state. -/
private noncomputable def gaining (x y : ForkedBeaconState preset) : Nat :=
  ∑ k ∈ activeKeys x.state ∩ recentKeys y.state,
    (effectiveWeight y.state k - effectiveWeight x.state k)

/-- The boundary correction is a maximum single-epoch cohort, not cumulative exits. -/
noncomputable def boundaryWindow {x : ForkedBeaconState preset} (high : Nat) :
    {y : ForkedBeaconState preset} → Run config checks x y → Nat
  | _, .nil => boundaryStake x
  | y, .snoc pre _ =>
    if (getCurrentEpoch y.state).toNat ≤ high + 1 then
      max (boundaryWindow high pre) (boundaryStake y)
    else boundaryWindow high pre

private theorem funding_assemble {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events)
    (blockBound : ∀ {fork : Fork} {s t : BeaconState preset fork},
      .pectra ≤ fork → ∀ early : fork < .glamsterdam,
      BalancesMatch s → ∀ (engine : ExecutionEngine preset fork) (block : BeaconBlock preset fork),
      processBlock config checks engine s block = .ok t →
      ∀ events : List (BalanceEvent preset),
      blockBalanceReplay (config := config) (checks := checks) early engine s block =
        .ok (t, events) →
      fundedStake ⟨fork, t⟩ + funding_carry ⟨fork, t⟩ ≤
        fundedStake ⟨fork, s⟩ + funding_carry ⟨fork, s⟩ + (events.map fundingCredit).sum)
    (slotBound : ∀ {a b : ForkedBeaconState preset},
      .pectra ≤ a.fork → b.fork < .glamsterdam →
      2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat →
      BalancesMatch a.state → ExitsOrdered a.state → ActivationExitOrder a.state →
      PendingConsolidationInvariant config a.state →
      ∀ (ok : advanceSlotAcross config checks a = .ok b) (events : List (BalanceEvent preset)),
      (Step.slot ok).balanceEvents = .ok events →
      fundedStake b + funding_carry b ≤ fundedStake a + funding_carry a +
        ((getCurrentEpoch b.state).toNat - (getCurrentEpoch a.state).toNat) *
          config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat + (events.map fundingCredit).sum) :
    Models.stake (effectiveWeight y.state) (activeKeys y.state) ≤
      activeStakeWindow (config := config) x high events := by
  have invariant {z : ForkedBeaconState preset} (run : Run config checks g z) :
      Invariant z.state := by
    induction run with
    | nil =>
      obtain ⟨_, _, _, ok⟩ := genesis
      exact (initializeBeaconStateFromEth1_invariant ok).2
    | snoc pre step ih =>
      cases step with
      | slot ok => exact (advanceSlotAcross_invariant ih ok).1
      | block engine signed due ok =>
        exact (frame_processBlock (applySignedBlock_ok ok).2.1).invariant ih
  apply funding_window_of_steps tail electra early delay
    ((shared.append tail).unique (genesis_unique genesis)) high endEpoch events replayed
  intro a b pre step before added addedOk
  have reachable := shared.append pre
  have holds := invariant reachable
  have forkOrder : x.fork ≤ a.fork := by
    have monotone {u v : ForkedBeaconState preset} (run : Run config checks u v) :
        u.fork ≤ v.fork := by
      induction run with
      | nil => exact Nat.le_refl _
      | snoc run next ih => exact Nat.le_trans ih next.chainStep.fork_le
    exact monotone pre
  have startElectra : .pectra ≤ a.fork := Nat.le_trans electra forkOrder
  cases step with
  | slot ok =>
    exact slotBound startElectra before delay holds.balancesMatch holds.exitsOrdered
      (reachable.activationExitOrder genesis)
      (fun witness => reachable.pendingConsolidation_invariant genesis
        (Nat.lt_of_le_of_lt (Step.slot ok).chainStep.fork_le before) witness (by omega))
      ok added addedOk
  | block engine signed due ok =>
    have processed := (applySignedBlock_ok ok).2.1
    obtain ⟨blockEvents, blockReplay⟩ :=
      blockBalanceReplay_result _ _ before engine signed.message processed
    simp only [Step.balanceEvents, before, ↓reduceDIte, blockReplay,
      bind, Except.bind, pure, Except.pure, Except.ok.injEq] at addedOk
    subst added
    have bound := blockBound startElectra before holds.balancesMatch engine signed.message
      processed blockEvents blockReplay
    have slot := (frame_processBlock processed).slot
    simpa only [getCurrentEpoch, slot, Nat.sub_self, Nat.zero_mul, Nat.add_zero] using bound

/-- The post-Electra funding envelope bounds active stake without a registry-wide effective cap.

The bound retains withdrawn-source credits rather than assuming pending-source chronology. -/
private theorem active_stake_le_window {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (withdrawalDelay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    Models.stake (effectiveWeight y.state) (activeKeys y.state) ≤
      activeStakeWindow (config := config) x high events := by
  exact funding_assemble shared tail genesis electra early withdrawalDelay
    high endEpoch events replayed funding_block funding_slot

def exitWindow (x : ForkedBeaconState preset) (high : Nat)
    (events : List (BalanceEvent preset)) : Nat :=
  scheduledExitCarry x high + queueCarry x high +
    driftHorizon x high *
      ((if x.fork < .pectra then max 1 (cohortCap config (registryWindow x high)) *
        preset.MAX_EFFECTIVE_BALANCE.toNat else 0) +
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        consolidationRate (preset := preset) (config := config)
          (activeStakeWindow (config := config) x high events))

/-- Before Electra activations spend count churn; afterwards funding spends deposit churn.

Already funded inactive validators remain a carry-in because Electra activation has no count cap. -/
def activationWindow (x : ForkedBeaconState preset) (high : Nat) : Nat :=
  activationCarry x + depositWindow (config := config) x high +
    (if x.fork < .pectra then driftHorizon x high * cohortCap config (registryWindow x high) *
      preset.MAX_EFFECTIVE_BALANCE.toNat else 0)

/-- Electra deposits use depositWindow; pre-Electra active top-ups remain here.

Across Electra, pre-upgrade funding can bypass later deposit churn, so retain all such credits. -/
def residualCredit (x : ForkedBeaconState preset) (high : Nat)
    (event : BalanceEvent preset) : Nat :=
  match event.source with
  | .deposits => if .pectra ≤ event.before.fork then 0 else
      if high + 1 < config.ELECTRA_FORK_EPOCH.toNat then
        ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
          actualBalanceAt event.after i.toNat - actualBalanceAt event.before i.toNat).sum
      else event.creditLimit
  | _ => event.creditLimit

/-- Per-reference-key non-slashing debits count while the key remains in the recent support. -/
def referenceDebit (i : Nat) (event : BalanceEvent preset) : Nat :=
  if event.source == .slashings then 0 else
    match event.before.state.validators.data[i]? with
    | none => 0
    | some v => if isActiveValidator v (getCurrentEpoch event.before.state) ||
        isActiveValidator v (getPreviousEpoch event.before.state) then
        actualBalanceAt event.before i - actualBalanceAt event.after i
      else 0

/-- Rounding is charged only to a key with initial slack or an actual non-slashing debit.

An aligned effective balance cannot fall below its starting value without such a deficit. -/
def lossCorrection (x : ForkedBeaconState preset) (events : List (BalanceEvent preset)) : Nat :=
  ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
    match x.state.validators.data[i.toNat]? with
    | none => 0
    | some v => if v.slashed then 0 else
      let deficit := effectiveAt x i.toNat - actualBalanceAt x i.toNat +
        (events.map (referenceDebit i.toNat)).sum
      if deficit = 0 then 0 else deficit + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1).sum

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
  unfold applyDeposit at applied
  split at applied
  · unfold applyDepositElectra at applied
    split at applied
    · simp only [bind_ok_iff] at applied
      obtain ⟨_, _, applied⟩ := applied
      split at applied
      · simp only [bind_ok_iff, liftAccessor_ok] at applied
        obtain ⟨_, added, pushed⟩ := applied
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
        rw [addValidatorToRegistry_validators_eq_push added]
        simp
      · cases applied; exact Nat.le_succ _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp applied)
      exact Nat.le_succ _
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

-- An unused block slot retains its allowance until a successful header consumes it.
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

private structure intervalLoss_SiteStep (a b : ForkedBeaconState preset) : Prop where
  lifecycle : RegistryLifecycle a.state b.state
  epoch : getCurrentEpoch a.state = getCurrentEpoch b.state
  matched : BalancesMatch a.state → BalancesMatch b.state
  ordered : ExitsOrdered a.state → ExitsOrdered b.state
  fork_le : a.fork ≤ b.fork
  slashed : SlashedPersistence a.state b.state

private theorem intervalLoss_SiteStep.refl (a : ForkedBeaconState preset) :
    intervalLoss_SiteStep a a := ⟨.refl _, rfl, id, id, Nat.le_refl _, .refl _⟩

private theorem intervalLoss_SiteStep.trans {a b c : ForkedBeaconState preset}
    (ab : intervalLoss_SiteStep a b) (bc : intervalLoss_SiteStep b c) :
    intervalLoss_SiteStep a c :=
  ⟨ab.lifecycle.trans bc.lifecycle, ab.epoch.trans bc.epoch,
    bc.matched ∘ ab.matched, bc.ordered ∘ ab.ordered, Nat.le_trans ab.fork_le bc.fork_le,
    ab.slashed.trans bc.slashed⟩

private theorem intervalLoss_SiteStep.of_frame {fork : Fork}
    {a b : BeaconState preset fork} (life : RegistryLifecycle a b) (frame : Frame a b) :
    intervalLoss_SiteStep ⟨fork, a⟩ ⟨fork, b⟩ := by
  refine ⟨life, ?_, frame.balancesMatch, frame.exitsOrdered, Nat.le_refl _,
    .of_frame frame⟩
  simp [getCurrentEpoch, frame.slot]

private inductive intervalLoss_SlashingSite (config : Config) (checks : SignatureChecks) :
    ForkedBeaconState preset → ForkedBeaconState preset → Prop where
  | delayed {fork : Fork} {s t : BeaconState preset fork}
      (ok : processSlashings s = .ok t) :
      intervalLoss_SlashingSite config checks ⟨fork, s⟩ ⟨fork, t⟩
  | proposer {fork : Fork} {s t : BeaconState preset fork} {sl : ProposerSlashing}
      (ok : processProposerSlashing config checks s sl = .ok t) :
      intervalLoss_SlashingSite config checks ⟨fork, s⟩ ⟨fork, t⟩
  | attester {fork : Fork} {s t : BeaconState preset fork} {sl : AttesterSlashing preset fork}
      (ok : processAttesterSlashing config checks s sl = .ok t) :
      intervalLoss_SlashingSite config checks ⟨fork, s⟩ ⟨fork, t⟩

private def intervalLoss_ReplaySites {config : Config} {checks : SignatureChecks}
    (start : ForkedBeaconState preset)
    {fork : Fork} (pre : BalanceReplay preset fork) : Prop :=
  intervalLoss_SiteStep start ⟨fork, pre.1⟩ ∧
    ∀ e ∈ pre.2, intervalLoss_SiteStep start e.before ∧
      intervalLoss_SiteStep e.before e.after ∧ intervalLoss_SiteStep e.after ⟨fork, pre.1⟩ ∧
      (e.source = .slashings → intervalLoss_SlashingSite config checks e.before e.after)

private theorem intervalLoss_sites_record {fork : Fork}
    {start : ForkedBeaconState preset} {source : BalanceSource}
    {limits : BeaconState preset fork → Except TransitionError (Nat × Nat)}
    {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
    (preserves : ∀ s t, action s = .ok t → intervalLoss_SiteStep ⟨fork, s⟩ ⟨fork, t⟩)
    {pre post : BalanceReplay preset fork}
    (prior : intervalLoss_ReplaySites (config := config) (checks := checks) start pre)
    (classified : ∀ s t, action s = .ok t → source = .slashings →
      intervalLoss_SlashingSite config checks ⟨fork, s⟩ ⟨fork, t⟩)
    (ok : recordBalance source limits action pre = .ok post) :
    intervalLoss_ReplaySites (config := config) (checks := checks) start post := by
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨⟨credit, debit⟩, _, after, computed, rfl⟩ := ok
  have kept := preserves pre.1 after computed
  refine ⟨prior.1.trans kept, ?_⟩
  intro e member
  rcases List.mem_append.mp member with old | added
  · obtain ⟨first, middle, last, source⟩ := prior.2 e old
    exact ⟨first, middle, last.trans kept, source⟩
  · have same := List.mem_singleton.mp added
    subst e
    exact ⟨prior.1, kept, .refl _, classified _ _ computed⟩

private theorem intervalLoss_sites_carry {fork : Fork}
    {start : ForkedBeaconState preset}
    {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
    (preserves : ∀ s t, action s = .ok t → intervalLoss_SiteStep ⟨fork, s⟩ ⟨fork, t⟩)
    {pre post : BalanceReplay preset fork}
    (prior : intervalLoss_ReplaySites (config := config) (checks := checks) start pre)
    (ok : carryBalance action pre = .ok post) :
    intervalLoss_ReplaySites (config := config) (checks := checks) start post := by
  simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨after, computed, rfl⟩ := ok
  have kept := preserves pre.1 after computed
  refine ⟨prior.1.trans kept, ?_⟩
  intro e member
  obtain ⟨first, middle, last, source⟩ := prior.2 e member
  exact ⟨first, middle, last.trans kept, source⟩

private theorem intervalLoss_sites_fold {fork : Fork} {α : Type}
    (action : BeaconState preset fork → α → Except TransitionError (BeaconState preset fork))
    (preserves : ∀ s item t, action s item = .ok t →
      intervalLoss_SiteStep ⟨fork, s⟩ ⟨fork, t⟩)
    (items : List α) {s t : BeaconState preset fork}
    (ok : items.foldlM action s = .ok t) :
    intervalLoss_SiteStep ⟨fork, s⟩ ⟨fork, t⟩ := by
  exact foldlM_ok_invariant (fun t => intervalLoss_SiteStep ⟨fork, s⟩ ⟨fork, t⟩)
    (fun _ item _ prior ok => prior.trans (preserves _ item _ ok)) (.refl _) ok

private theorem intervalLoss_sites_deltas {fork : Fork}
    {start : ForkedBeaconState preset} (source : BalanceSource)
    (notSlashing : source ≠ .slashings)
    (deltas : Array Gwei × Array Gwei) {pre post : BalanceReplay preset fork}
    (initial : intervalLoss_ReplaySites (config := config) (checks := checks) start pre)
    (ok : replayDeltas source deltas pre = .ok post) :
    intervalLoss_ReplaySites (config := config) (checks := checks) start post := by
  apply foldlM_ok_invariant
    (intervalLoss_ReplaySites (config := config) (checks := checks) start) _ initial ok
  intro pre i post prior ok
  simp only [bind_ok_iff] at ok
  obtain ⟨index, _, rewarded, rewardOk, penaltyOk⟩ := ok
  have raised := intervalLoss_sites_record (fun s t computed => by
    have computed := liftAccessor_ok.mp computed
    apply intervalLoss_SiteStep.of_frame _ (frame_increaseBalance computed).toFrame
    obtain ⟨_, set⟩ := increaseBalance_ok computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact .of_data rfl) prior (fun _ _ _ h => by cases h) rewardOk
  apply intervalLoss_sites_record (fun s t computed => ?_) raised
    (fun _ _ _ h => False.elim (notSlashing h)) penaltyOk
  have computed := liftAccessor_ok.mp computed
  apply intervalLoss_SiteStep.of_frame _ (frame_decreaseBalance computed).toFrame
  obtain ⟨_, set⟩ := decreaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact .of_data rfl

private theorem intervalLoss_sites_rewards {fork : Fork}
    {start : ForkedBeaconState preset} {pre post : BalanceReplay preset fork}
    (initial : intervalLoss_ReplaySites (config := config) (checks := checks) start pre)
    (ok : replayRewards (config := config) pre = .ok post) :
    intervalLoss_ReplaySites (config := config) (checks := checks) start post := by
  unfold replayRewards at ok
  split at ok
  · cases ok; exact initial
  · simp only [bind_ok_iff] at ok
    obtain ⟨ordinary, _, inactivity, _, ok⟩ := ok
    split at ok
    · obtain ⟨middle, folded, last⟩ := bind_ok_iff.mp ok
      exact intervalLoss_sites_deltas _ (by decide) _
        (foldlM_ok_invariant (intervalLoss_ReplaySites (config := config) (checks := checks) start)
          (fun _ _ _ h ok => intervalLoss_sites_deltas _ (by decide) _ h ok) initial folded) last
    · simp only [bind_ok_iff] at ok
      obtain ⟨rewards, _, rewarded, rewardOk, middle, folded, last⟩ := ok
      exact intervalLoss_sites_deltas _ (by decide) _
        (foldlM_ok_invariant (intervalLoss_ReplaySites (config := config) (checks := checks) start)
          (fun _ _ _ h ok => intervalLoss_sites_deltas _ (by decide) _ h ok)
          (intervalLoss_sites_deltas _ (by decide) _ initial rewardOk) folded) last

private theorem intervalLoss_sites_justification {fork : Fork}
    {s t : BeaconState preset fork}
    (ok : processJustificationAndFinalization s = .ok t) :
    intervalLoss_SiteStep ⟨fork, s⟩ ⟨fork, t⟩ := by
  obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok ok
  · exact .refl _
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    rw [← rest]
    exact ⟨.of_data rfl, rfl, id, id, Nat.le_refl _, .of_data rfl⟩

/-- The replay of an epoch keeps its sites, one replay stage at a time. -/
private theorem intervalLoss_sites_epoch {fork : Fork} {s : BeaconState preset fork}
    {post : BalanceReplay preset fork}
    (ok : epochBalanceReplay (config := config) (checks := checks) s = .ok post) :
    intervalLoss_ReplaySites (config := config) (checks := checks) ⟨fork, s⟩ post := by
  refine (epochBalanceReplay_trace ok).transport
    (fun a b => intervalLoss_ReplaySites (config := config) (checks := checks) ⟨fork, s⟩ a →
      intervalLoss_ReplaySites (config := config) (checks := checks) ⟨fork, s⟩ b)
    (fun _ => id) (fun one two held => two (one held)) ?_ ⟨.refl _, by simp⟩
  intro k member pre after step held
  -- A stage that keeps the validators and forms a frame is a site step.
  have kept {k : EpochStage} {a b : BeaconState preset fork}
      (edge : EpochStage.Edge config checks k a b)
      (other : k ≠ .registry ∧ k ≠ .pendingDeposits ∧ k ≠ .effectiveBalances)
      (frame : Frame a b) : intervalLoss_SiteStep ⟨fork, a⟩ ⟨fork, b⟩ :=
    .of_frame (.of_data (congrArg (·.data) (edge.validators_eq other))) frame
  -- A pending stage appends one event between its input and its output.
  have appended {a b : BeaconState preset fork} {events : List (BalanceEvent preset)}
      (prior : intervalLoss_ReplaySites (config := config) (checks := checks) ⟨fork, s⟩
        (a, events))
      (stepped : intervalLoss_SiteStep ⟨fork, a⟩ ⟨fork, b⟩) (event : BalanceEvent preset)
      (before : event.before = ⟨fork, a⟩) (endpoint : event.after = ⟨fork, b⟩)
      (source : event.source ≠ .slashings) :
      intervalLoss_ReplaySites (config := config) (checks := checks) ⟨fork, s⟩
        (b, events ++ [event]) := by
    refine ⟨prior.1.trans stepped, ?_⟩
    intro e member
    rcases List.mem_append.mp member with old | added
    · obtain ⟨first, middle, last, kind⟩ := prior.2 e old
      exact ⟨first, middle, last.trans stepped, kind⟩
    · obtain rfl := List.mem_singleton.mp added
      rw [before, endpoint]
      exact ⟨prior.1, stepped, .refl _, fun h => False.elim (source h)⟩
  cases k <;> simp only [epochReplayAction] at step
  case justification =>
    exact intervalLoss_sites_carry (fun _ _ ok => intervalLoss_sites_justification ok) held step
  case inactivity =>
    split at step
    · rename_i altair
      exact intervalLoss_sites_carry (fun _ _ ok => kept (k := .inactivity)
        (by simp only [EpochStage.Edge, altair, ↓reduceDIte]; exact ok) ⟨nofun, nofun, nofun⟩
        (frame_processInactivityUpdates ok).toFrame) held step
    · cases step; exact held
  case rewards => exact intervalLoss_sites_rewards held step
  case registry =>
    exact intervalLoss_sites_carry (fun _ _ ok => .of_frame
      (registryLifecycle_processRegistryUpdates ok) (frame_processRegistryUpdates ok).toFrame)
      held step
  case slashings =>
    exact intervalLoss_sites_record (fun _ _ ok => kept (k := .slashings) ok
      ⟨nofun, nofun, nofun⟩ (frame_processSlashings ok).toFrame) held
      (fun _ _ ok _ => .delayed ok) step
  case eth1Reset =>
    split at step
    · rename_i before
      exact intervalLoss_sites_carry (fun _ _ ok => kept (k := .eth1Reset)
        (by simp only [EpochStage.Edge, before, ↓reduceDIte]; exact ok) ⟨nofun, nofun, nofun⟩
        (frame_processEth1DataReset ok).toFrame) held step
    · cases step; exact held
  case pendingDeposits =>
    split at step
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
      obtain ⟨deposited, depositOk, rfl⟩ := step
      exact appended held (.of_frame (registryLifecycle_processPendingDeposits depositOk)
        (frame_processPendingDeposits depositOk).toFrame) _ rfl rfl nofun
    · cases step; exact held
  case pendingConsolidations =>
    split at step
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
      obtain ⟨consolidated, consolidationOk, rfl⟩ := step
      exact appended held (.of_frame
        (RegistryLifecycle.of_data (by rw [(processPendingConsolidations_kept consolidationOk).1]))
        (frame_processPendingConsolidations consolidationOk).toFrame) _ rfl rfl nofun
    · cases step; exact held
  all_goals simp [EpochStage.prefixStages] at member

private theorem intervalLoss_sites_block {fork : Fork} {s : BeaconState preset fork}
    (early : fork < .glamsterdam) (engine : ExecutionEngine preset fork)
    (block : BeaconBlock preset fork) {post : BalanceReplay preset fork}
    (ok : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok post) :
    intervalLoss_ReplaySites (config := config) (checks := checks) ⟨fork, s⟩ post := by
  unfold blockBalanceReplay at ok
  obtain ⟨headed, headerOk, ok⟩ := bind_ok_iff.mp ok
  have initial : intervalLoss_ReplaySites (config := config) (checks := checks) ⟨fork, s⟩ (s, []) :=
    ⟨.refl _, by simp⟩
  have headedSites := intervalLoss_sites_carry (fun _ _ ok => .of_frame
    (registryLifecycle_processBlockHeader ok) (frame_processBlockHeader ok).toFrame)
    initial headerOk
  by_cases bellatrix : .bellatrix ≤ fork
  case' pos =>
    simp only [bellatrix, ↓reduceDIte] at ok
    obtain ⟨executed, executionOk, rest⟩ := bind_ok_iff.mp ok
    have executedSites := intervalLoss_sites_record (fun _ _ ok => .of_frame
      (.of_data (congrArg (·.data) (processBlockExecution_validators ok)))
      (frame_processBlockExecution ok).toFrame)
      headedSites (fun _ _ _ h => by cases h) executionOk
  case' neg =>
    simp only [bellatrix, ↓reduceDIte, pure, Except.pure, bind_ok_iff,
      Except.ok.injEq, exists_eq_left'] at ok
    have rest := ok
    have executedSites := headedSites
  all_goals
    try simp only [bind_ok_iff] at rest
    obtain ⟨randao, randaoOk, voted, votedOk, expected, _, _, _,
      proposed, proposedOk, attested, attestedOk, rewarded, rewardedOk, deposited, depositOk,
      exited, exitOk, changed, changedOk, rest⟩ := rest
    have randaoSites := intervalLoss_sites_carry (fun _ _ ok => .of_frame
      (registryLifecycle_processRandao ok) (frame_processRandao ok).toFrame) executedSites randaoOk
    have votedSites := intervalLoss_sites_carry (fun _ _ ok => .of_frame
      (registryLifecycle_processEth1Data ok) (frame_processEth1Data ok).toFrame) randaoSites votedOk
    have proposedSites := foldlM_ok_invariant
      (intervalLoss_ReplaySites (config := config) (checks := checks) ⟨fork, s⟩)
      (fun _ _ _ h ok => intervalLoss_sites_record (fun _ _ ok => .of_frame
        (registryLifecycle_processProposerSlashing ok) (frame_processProposerSlashing ok).toFrame)
        h (fun _ _ ok _ => .proposer ok) ok) votedSites proposedOk
    have attestedSites := foldlM_ok_invariant
      (intervalLoss_ReplaySites (config := config) (checks := checks) ⟨fork, s⟩)
      (fun _ _ _ h ok => intervalLoss_sites_record (fun _ _ ok => .of_frame
        (registryLifecycle_processAttesterSlashing ok) (frame_processAttesterSlashing ok).toFrame)
        h (fun _ _ ok _ => .attester ok) ok) proposedSites attestedOk
    have rewardedSites := foldlM_ok_invariant
      (intervalLoss_ReplaySites (config := config) (checks := checks) ⟨fork, s⟩)
      (fun _ _ _ h ok => intervalLoss_sites_record (fun _ _ ok => .of_frame
        (registryLifecycle_processAttestation ok) (frame_processAttestation ok))
        h (fun _ _ _ h => by cases h) ok) attestedSites rewardedOk
    have depositedSites := foldlM_ok_invariant
      (intervalLoss_ReplaySites (config := config) (checks := checks) ⟨fork, s⟩)
      (fun _ _ _ h ok => intervalLoss_sites_record (fun _ _ ok => .of_frame
        (registryLifecycle_processDeposit ok) (frame_processDeposit ok).toFrame)
        h (fun _ _ _ h => by cases h) ok) rewardedSites depositOk
    have exitedSites := intervalLoss_sites_carry (fun _ _ ok =>
      intervalLoss_sites_fold _ (fun _ _ _ ok => .of_frame
        (registryLifecycle_processVoluntaryExit ok) (frame_processVoluntaryExit ok).toFrame)
        _ (by simpa only [← Array.foldlM_toList] using ok)) depositedSites exitOk
    have changedSites := intervalLoss_sites_carry (fun _ _ ok => by
      unfold processBlsToExecutionChanges at ok
      split at ok
      · exact intervalLoss_sites_fold _ (fun _ _ _ ok => .of_frame
          (registryLifecycle_processBlsToExecutionChange ok)
          (frame_processBlsToExecutionChange ok).toFrame)
          _ (by simpa only [← Array.foldlM_toList] using ok)
      · cases ok; exact .refl _) exitedSites changedOk
    by_cases electra : .pectra ≤ fork
    case' pos =>
      simp only [electra, ↓reduceDIte, bind_ok_iff] at rest
      obtain ⟨deposits, depositRequestOk, withdrawals, withdrawalOk,
        requested, consolidations, rest⟩ := rest
      have depositsSites := intervalLoss_sites_carry (fun _ _ ok =>
        intervalLoss_sites_fold _ (fun _ _ _ ok => .of_frame
          (registryLifecycle_processDepositRequest ok) (frame_processDepositRequest ok).toFrame)
          _ (by simpa only [← Array.foldlM_toList] using ok)) changedSites depositRequestOk
      have withdrawalsSites := intervalLoss_sites_carry (fun _ _ ok =>
        intervalLoss_sites_fold _ (fun _ _ _ ok => .of_frame
          (registryLifecycle_processWithdrawalRequest ok)
          (frame_processWithdrawalRequest ok).toFrame)
          _ (by simpa only [← Array.foldlM_toList] using ok)) depositsSites withdrawalOk
      have requestedSites := foldlM_ok_invariant
        (intervalLoss_ReplaySites (config := config) (checks := checks) ⟨fork, s⟩)
        (fun _ _ _ h ok => intervalLoss_sites_record (fun _ _ ok => .of_frame
          (registryLifecycle_processConsolidationRequest ok)
          (frame_processConsolidationRequest ok).toFrame)
          h (fun _ _ _ h => by cases h) ok) withdrawalsSites consolidations
    case' neg =>
      simp only [electra, ↓reduceDIte, pure, Except.pure, bind_ok_iff,
        Except.ok.injEq, exists_eq_left'] at rest
      have requestedSites := changedSites
    all_goals
      split at rest
      · exact intervalLoss_sites_record (fun _ _ ok => .of_frame
          (by obtain ⟨_, rfl⟩ := processSyncAggregate_eq ok; exact .of_data rfl)
          (frame_processSyncAggregate ok).toFrame)
          requestedSites (fun _ _ _ h => by cases h) rest
      · cases rest; exact requestedSites

private theorem intervalLoss_sites_upgradeNext {s : ForkedBeaconState preset}
    {t : { t : ForkedBeaconState preset // s.fork < t.fork }}
    (ok : upgradeNext config checks s = .ok t) : intervalLoss_SiteStep s t.val := by
  have frame := upgradeFrame_upgradeNext ok
  refine ⟨registryLifecycle_upgradeNext ok, ?_, frame.balancesMatch, frame.exitsOrdered,
    Nat.le_of_lt t.property, .of_upgradeFrame frame⟩
  simp [getCurrentEpoch, frame.slot]

private theorem intervalLoss_sites_upgrades {s t : ForkedBeaconState preset}
    (ok : processUpgrades config checks s = .ok t) :
    ∃ events, upgradeBalanceReplay (config := config) (checks := checks) s = .ok events ∧
      intervalLoss_SiteStep s t ∧ ∀ e ∈ events, intervalLoss_SiteStep s e.before ∧
        intervalLoss_SiteStep e.before e.after ∧ intervalLoss_SiteStep e.after t ∧
        e.source ≠ .slashings := by
  fun_induction processUpgrades config checks s generalizing t with
  | case1 s due ih =>
    obtain ⟨next, nextOk, restOk⟩ := bind_ok_iff.mp ok
    obtain ⟨events, replay, last, sites⟩ := ih next restOk
    have first := intervalLoss_sites_upgradeNext nextOk
    rw [upgradeBalanceReplay]
    simp only [due, ↓reduceIte, nextOk, bind, Except.bind, replay]
    split
    · split
      · refine ⟨_, rfl, first.trans last, ?_⟩
        intro e member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨.refl _, first, last, fun h => by cases h⟩
        · obtain ⟨a, b, c, source⟩ := sites e member
          exact ⟨first.trans a, b, c, source⟩
      · refine ⟨_, rfl, first.trans last, ?_⟩
        intro e member
        obtain ⟨a, b, c, source⟩ := sites e member
        exact ⟨first.trans a, b, c, source⟩
    · refine ⟨_, rfl, first.trans last, ?_⟩
      intro e member
      obtain ⟨a, b, c, source⟩ := sites e member
      exact ⟨first.trans a, b, c, source⟩
  | case2 s due =>
    cases ok
    refine ⟨[], ?_, .refl _, by simp⟩
    rw [upgradeBalanceReplay]
    simp [due, pure, Except.pure]

private def intervalLoss_EventBetween {config : Config} {checks : SignatureChecks}
    (x y : ForkedBeaconState preset)
    (e : BalanceEvent preset) : Prop :=
  RegistryLifecycle x.state e.before.state ∧
    RegistryLifecycle e.before.state e.after.state ∧
    RegistryLifecycle e.after.state y.state ∧ ExitsOrdered e.before.state ∧
    BalancesMatch e.after.state ∧
    (getCurrentEpoch x.state).toNat ≤ (getCurrentEpoch e.before.state).toNat ∧
    (getCurrentEpoch e.before.state).toNat ≤ (getCurrentEpoch y.state).toNat ∧
    e.before.fork < .glamsterdam ∧
    SlashedPersistence e.before.state e.after.state ∧ SlashedPersistence e.after.state y.state ∧
    (e.source = .slashings → intervalLoss_SlashingSite config checks e.before e.after) ∧
    e.before.fork ≤ y.fork

private theorem intervalLoss_sites_between {x y : ForkedBeaconState preset}
    {e : BalanceEvent preset} (first : intervalLoss_SiteStep x e.before)
    (middle : intervalLoss_SiteStep e.before e.after)
    (last : intervalLoss_SiteStep e.after y) (matched : BalancesMatch x.state)
    (ordered : ExitsOrdered x.state) (early : y.fork < .glamsterdam)
    (source : e.source = .slashings → intervalLoss_SlashingSite config checks e.before e.after) :
    intervalLoss_EventBetween (config := config) (checks := checks) x y e := by
  have afterEarly := Nat.lt_of_le_of_lt last.fork_le early
  refine ⟨first.lifecycle, middle.lifecycle, last.lifecycle, first.ordered ordered,
    middle.matched (first.matched matched), ?_, ?_,
    Nat.lt_of_le_of_lt middle.fork_le afterEarly, middle.slashed,
    last.slashed, source, Nat.le_trans middle.fork_le last.fork_le⟩
  · rw [first.epoch]
  · rw [middle.epoch, last.epoch]

private theorem intervalLoss_step_sites {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (early : y.fork < .glamsterdam)
    (holds : Invariant x.state)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events) :
    ∀ e ∈ events, intervalLoss_EventBetween (config := config) (checks := checks) x y e := by
  have matched := holds.balancesMatch
  have ordered := holds.exitsOrdered
  have before : x.fork < .glamsterdam := Nat.lt_of_le_of_lt step.chainStep.fork_le early
  cases step with
  | block engine signed due ok =>
    obtain ⟨recorded, replay⟩ := blockBalanceReplay_result _ _ before engine signed.message
      (applySignedBlock_ok ok).2.1
    have sites := intervalLoss_sites_block before engine signed.message replay
    simp only [Step.balanceEvents, before, ↓reduceDIte, replay, bind, Except.bind,
      pure, Except.pure, Except.ok.injEq] at replayed
    subst events
    intro e member
    obtain ⟨first, middle, last, source⟩ := sites.2 e member
    exact intervalLoss_sites_between first middle last matched ordered early source
  | slot ok =>
    obtain ⟨advanced, advanceOk, upgrades⟩ := bind_ok_iff.mp ok
    obtain ⟨crossings, crossingOk, crossingStep, crossingSites⟩ :=
      intervalLoss_sites_upgrades upgrades
    have advanceCopy := advanceOk
    simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at advanceCopy
    obtain ⟨next, nextOk, cached, cachedOk, epoched, epochOk, afterEq⟩ := advanceCopy
    obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
    have cachedStep : intervalLoss_SiteStep x ⟨x.fork, cached⟩ := by
      rw [cachedEq]
      exact ⟨.of_data rfl, rfl, id, id, Nat.le_refl _, .of_data rfl⟩
    have advanceLife := registryLifecycle_advanceSlot advanceOk
    have advanceEpoch := coverage_step_epoch (Step.slot ok)
    have advancedHolds := (advanceSlot_invariant holds advanceOk).1
    have crossingBound : ∀ e ∈ crossings,
        intervalLoss_EventBetween (config := config) (checks := checks) x y e := by
      intro e member
      obtain ⟨first, middle, last, source⟩ := crossingSites e member
      have afterEarly := Nat.lt_of_le_of_lt last.fork_le early
      refine ⟨advanceLife.trans first.lifecycle, middle.lifecycle, last.lifecycle,
        ?_, ?_, ?_, ?_, Nat.lt_of_le_of_lt middle.fork_le afterEarly,
        middle.slashed, last.slashed, (fun h => False.elim (source h)),
        Nat.le_trans middle.fork_le last.fork_le⟩
      · exact first.ordered advancedHolds.exitsOrdered
      · exact middle.matched (first.matched advancedHolds.balancesMatch)
      · rw [middle.epoch, last.epoch]
        exact advanceEpoch
      · rw [middle.epoch, last.epoch]
    by_cases lastSlot : next % preset.SLOTS_PER_EPOCH = 0
    · simp only [epochIfLast, lastSlot, ↓reduceIte] at epochOk
      obtain ⟨middle, updated, recorded, recordOk, updatedOk, validators, balances⟩ :=
        epochBalanceReplay_result cached epoched before epochOk
      have sites := intervalLoss_sites_epoch recordOk
      have finishLife : RegistryLifecycle middle advanced :=
        (registryLifecycle_processEffectiveBalanceUpdates updatedOk).trans
          (.of_data (by rw [← afterEq]; exact congrArg (·.data) validators.symm))
      have finishSlashed : SlashedPersistence middle advanced :=
        (SlashedPersistence.of_frame (frame_processEffectiveBalanceUpdates updatedOk).toFrame).trans
          (.of_data (by rw [← afterEq]; exact congrArg (·.data) validators.symm))
      have eventEq := Except.ok.inj (replayed.symm.trans
        (Step.balanceEvents_epoch_slot ok cachedOk nextOk lastSlot recordOk advanceOk crossingOk))
      rw [eventEq]
      intro e member
      rcases List.mem_append.mp member with member | member
      · obtain ⟨first, during, last, source⟩ := sites.2 e member
        have initial := cachedStep.trans first
        refine ⟨initial.lifecycle, during.lifecycle,
          (last.lifecycle.trans finishLife).trans crossingStep.lifecycle,
          initial.ordered ordered, during.matched (initial.matched matched), ?_, ?_,
          Nat.lt_of_le_of_lt (Nat.le_trans during.fork_le last.fork_le) before,
          during.slashed, (last.slashed.trans finishSlashed).trans crossingStep.slashed, source,
          Nat.le_trans (Nat.le_trans during.fork_le last.fork_le) crossingStep.fork_le⟩
        · rw [initial.epoch]
        · rw [← initial.epoch]; exact advanceEpoch
      · exact crossingBound e member
    · have eventEq : events = crossings := by
        simpa [Step.balanceEvents, cachedOk, nextOk, lastSlot, advanceOk, crossingOk,
          pure, Except.pure, bind, Except.bind] using replayed.symm
      rw [eventEq]
      exact crossingBound

private theorem intervalLoss_run_invariant {g y : ForkedBeaconState preset}
    (run : Run config checks g y) (genesis : Genesis (config := config) (checks := checks) g) :
    Invariant y.state := by
  induction run with
  | nil =>
    obtain ⟨_, _, _, ok⟩ := genesis
    exact (initializeBeaconStateFromEth1_invariant ok).2
  | snoc pre step ih =>
    cases step with
    | slot ok => exact (advanceSlotAcross_invariant ih ok).1
    | block engine signed due ok =>
      exact (frame_processBlock (applySignedBlock_ok ok).2.1).invariant ih

private theorem replay_event_provenance {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events)
    (event : BalanceEvent preset) (member : event ∈ events) :
    RegistryLifecycle x.state event.before.state ∧
      RegistryLifecycle event.before.state event.after.state ∧
      RegistryLifecycle event.after.state y.state ∧ ExitsOrdered event.before.state ∧
      BalancesMatch event.after.state ∧
      (getCurrentEpoch x.state).toNat ≤ (getCurrentEpoch event.before.state).toNat ∧
      (getCurrentEpoch event.before.state).toNat ≤ (getCurrentEpoch y.state).toNat := by
  have runEpoch {a b : ForkedBeaconState preset} (run : Run config checks a b) :
      (getCurrentEpoch a.state).toNat ≤ (getCurrentEpoch b.state).toNat := by
    induction run with
    | nil => exact Nat.le_refl _
    | snoc pre step ih => exact ih.trans (coverage_step_epoch step)
  induction tail generalizing events with
  | nil => cases replayed; simp at member
  | @snoc middle last pre step ih =>
    have selected := (coverage_step_epoch step).trans endEpoch
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    simp only [selected, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
    obtain ⟨added, addedOk, rfl⟩ := rest
    rcases List.mem_append.mp member with old | added
    · obtain ⟨first, during, final, ordered, matched, lo, hi⟩ :=
        ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early) selected prior priorOk old
      exact ⟨first, during, final.trans (RegistryLifecycle.chainStep step.chainStep),
        ordered, matched, lo, hi.trans (coverage_step_epoch step)⟩
    · obtain ⟨first, during, final, ordered, matched, lo, hi, _⟩ :=
        intervalLoss_step_sites step early (intervalLoss_run_invariant (shared.append pre) genesis)
          addedOk event added
      exact ⟨pre.registryLifecycle.trans first, during, final, ordered, matched,
        (runEpoch pre).trans lo, hi⟩

private theorem intervalLoss_event_slashed {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events)
    (event : BalanceEvent preset) (member : event ∈ events) :
    event.before.fork < .glamsterdam ∧
      SlashedPersistence event.before.state event.after.state ∧
      SlashedPersistence event.after.state y.state ∧
      (event.source = .slashings →
        intervalLoss_SlashingSite config checks event.before event.after) := by
  induction tail generalizing events with
  | nil => cases replayed; simp at member
  | @snoc middle last pre step ih =>
    have selected := (coverage_step_epoch step).trans endEpoch
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    simp only [selected, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
    obtain ⟨added, addedOk, rfl⟩ := rest
    rcases List.mem_append.mp member with old | added
    · obtain ⟨before, during, final, source⟩ :=
        ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early) selected prior priorOk old
      exact ⟨before, during, final.trans step.slashedPersistence, source⟩
    · obtain ⟨_, _, _, _, _, _, _, before, during, final, source, _⟩ :=
        intervalLoss_step_sites step early (intervalLoss_run_invariant (shared.append pre) genesis)
          addedOk event added
      exact ⟨before, during, final, source⟩

private theorem replay_event_fork_le {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events)
    (event : BalanceEvent preset) (member : event ∈ events) : event.before.fork ≤ y.fork := by
  induction tail generalizing events with
  | nil => cases replayed; simp at member
  | @snoc middle last pre step ih =>
    have selected := (coverage_step_epoch step).trans endEpoch
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    simp only [selected, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
    obtain ⟨added, addedOk, rfl⟩ := rest
    rcases List.mem_append.mp member with old | added
    · exact Nat.le_trans
        (ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early) selected prior priorOk old)
        step.chainStep.fork_le
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, bound⟩ :=
        intervalLoss_step_sites step early (intervalLoss_run_invariant (shared.append pre) genesis)
          addedOk event added
      exact bound

private theorem intervalLoss_zero_credit (e : BalanceEvent preset)
    (bound : e.credits ≤ e.creditLimit) (zero : e.creditLimit = 0) :
    ∀ i, actualBalanceAt e.after i ≤ actualBalanceAt e.before i := by
  intro i
  have point : actualBalanceAt e.after i - actualBalanceAt e.before i ≤ e.credits := by
    by_cases within : i < e.after.state.balances.data.size
    · exact Finset.single_le_sum (f := fun j =>
        actualBalanceAt e.after j - actualBalanceAt e.before j)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr within)
    · simp [actualBalanceAt, Array.getElem?_eq_none (Nat.le_of_not_lt within)]
  omega

private theorem intervalLoss_upgrade_sources {s : ForkedBeaconState preset}
    {events : List (BalanceEvent preset)}
    (ok : upgradeBalanceReplay (config := config) (checks := checks) s = .ok events) :
    ∀ e ∈ events, e.source = .crossing := by
  fun_induction upgradeBalanceReplay (config := config) (checks := checks) s
      generalizing events with
  | case1 s due ih =>
    obtain ⟨next, _, rest⟩ := bind_ok_iff.mp ok
    obtain ⟨prior, priorOk, last⟩ := bind_ok_iff.mp rest
    have sources := ih next priorOk
    repeat' split at last
    all_goals cases last; simpa using sources
  | case2 => cases ok; simp

private theorem intervalLoss_step_deposit_epoch {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (early : y.fork < .glamsterdam)
    (holds : Invariant x.state) {events : List (BalanceEvent preset)}
    (replayed : step.balanceEvents = .ok events)
    (e : BalanceEvent preset) (member : e ∈ events) (deposit : e.source = .deposits)
    (electra : .pectra ≤ e.before.fork) :
    (∀ i, actualBalanceAt e.after i ≤ actualBalanceAt e.before i) ∨
      (getCurrentEpoch e.before.state).toNat < (getCurrentEpoch y.state).toNat := by
  have before : x.fork < .glamsterdam := Nat.lt_of_le_of_lt step.chainStep.fork_le early
  cases step with
  | block engine signed due ok =>
    obtain ⟨recorded, replay⟩ := blockBalanceReplay_result _ _ before engine signed.message
      (applySignedBlock_ok ok).2.1
    simp only [Step.balanceEvents, before, ↓reduceDIte, replay, bind, Except.bind,
      pure, Except.pure, Except.ok.injEq] at replayed
    subst events
    exact Or.inl (intervalLoss_zero_credit e
      (blockBalanceReplay_bounded before engine signed.message
        holds.balancesMatch replay e member).1
      (funding_block_events before engine signed.message replay e member deposit electra))
  | slot ok =>
    obtain ⟨advanced, advanceOk, upgrades⟩ := bind_ok_iff.mp ok
    obtain ⟨crossings, crossingOk, _⟩ := intervalLoss_sites_upgrades upgrades
    have sources := intervalLoss_upgrade_sources crossingOk
    have advanceCopy := advanceOk
    simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at advanceCopy
    obtain ⟨next, nextOk, cached, cachedOk, epoched, epochOk, afterEq⟩ := advanceCopy
    by_cases boundary : next % preset.SLOTS_PER_EPOCH = 0
    · simp only [epochIfLast, boundary, ↓reduceIte] at epochOk
      obtain ⟨middle, updated, recorded, recordOk, _⟩ :=
        epochBalanceReplay_result cached epoched before epochOk
      have eventEq := Except.ok.inj (replayed.symm.trans
        (Step.balanceEvents_epoch_slot ok cachedOk nextOk boundary recordOk advanceOk crossingOk))
      rw [eventEq] at member
      rcases List.mem_append.mp member with member | member
      · have sites := intervalLoss_sites_epoch recordOk
        have epochEq := (sites.2 e member).1.epoch
        have sum := (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp
          (liftAccessor_ok.mp nextOk))).2
        have epochs := nextSlot_epoch_of_boundary sum boundary
        have cachedSlot := (frame_processSlot cachedOk).slot
        apply Or.inr
        rw [← epochEq, getCurrentEpoch_toNat, cachedSlot,
          getCurrentEpoch_toNat, processUpgrades_slot upgrades, ← afterEq]
        dsimp only
        omega
      · have := sources e member
        simp_all
    · have eventEq : events = crossings := by
        simpa [Step.balanceEvents, cachedOk, nextOk, boundary, advanceOk, crossingOk,
          pure, Except.pure, bind, Except.bind] using replayed.symm
      have := sources e (eventEq ▸ member)
      simp_all

private theorem replay_electra_deposit_epoch {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events)
    (event : BalanceEvent preset) (member : event ∈ events)
    (deposit : event.source = .deposits) (electra : .pectra ≤ event.before.fork) :
    (∀ i, actualBalanceAt event.after i ≤ actualBalanceAt event.before i) ∨
      (getCurrentEpoch event.before.state).toNat < (getCurrentEpoch y.state).toNat := by
  induction tail generalizing events with
  | nil => cases replayed; simp at member
  | @snoc middle last pre step ih =>
    have selected := (coverage_step_epoch step).trans endEpoch
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    simp only [selected, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
    obtain ⟨added, addedOk, rfl⟩ := rest
    rcases List.mem_append.mp member with old | added
    · rcases ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early) selected prior priorOk old with
        zero | strict
      · exact Or.inl zero
      · exact Or.inr (strict.trans_le (coverage_step_epoch step))
    · exact intervalLoss_step_deposit_epoch step early
        (intervalLoss_run_invariant (shared.append pre) genesis) addedOk event added deposit electra

private theorem intervalLoss_charge_site {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (charge : DepartureCharge)
    (member : charge ∈ tail.departureCharges) :
    ∃ a b, ∃ pre : Run config checks x a, ∃ step : Step config checks a b,
      ∃ post : Run config checks b y, (pre.snoc step).append post = tail ∧
        ∃ v w, a.state.validators.data[charge.index]? = some v ∧
          b.state.validators.data[charge.index]? = some w ∧
          v.exitEpoch = FAR_FUTURE_EPOCH ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
          charge.amount = v.effectiveBalance.toNat ∧ charge.epoch = w.exitEpoch.toNat := by
  induction tail with
  | nil => simp [Run.departureCharges] at member
  | @snoc a b pre step ih =>
    rcases List.mem_append.mp member with old | added
    · obtain ⟨first, last, initial, call, remaining, equal, witness⟩ := ih old
      refine ⟨first, last, initial, call, remaining.snoc step, ?_, witness⟩
      simp only [Run.append, equal]
    · obtain ⟨⟨v, i⟩, found, charged⟩ := List.mem_filterMap.mp added
      have found : a.state.validators.data[i]? = some v := by
        simpa only [List.mem_zipIdx_iff_getElem?, Array.getElem?_toList] using found
      dsimp only at charged
      split at charged
      · cases charged
      · rename_i w located
        split at charged
        · rename_i assigned
          cases Option.some.inj charged
          simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at assigned
          exact ⟨a, b, pre, step, .nil, rfl, v, w, found, located,
            assigned.1, assigned.2, rfl, rfl⟩
        · cases charged

private theorem intervalLoss_keys_sum {fork : Fork} (s : BeaconState preset fork)
    (indices : List ValidatorIndex) (unique : PubkeysDistinct s) (distinct : indices.Nodup)
    (inside : ∀ i ∈ indices, i.toNat < s.validators.data.size)
    (weight : Cryptography.Bls.BLSPubkey → Nat) :
    (∑ k ∈ keysAt s indices, weight k) =
      (indices.map fun i => ((s.validators.data[i.toNat]?).map
        (fun v => weight v.pubkey)).getD 0).sum := by
  let key (i : ValidatorIndex) (hi : i ∈ indices.toFinset) :=
    (s.validators.data[i.toNat]'(inside i (List.mem_toFinset.mp hi))).pubkey
  rw [← List.sum_toFinset _ distinct]
  symm
  apply Finset.sum_bij key
  · intro i hi
    simp only [keysAt, List.mem_toFinset, List.mem_filterMap]
    exact ⟨i, List.mem_toFinset.mp hi, by simp [key, inside i (List.mem_toFinset.mp hi)]⟩
  · intro i hi j hj same
    apply UInt64.toNat_inj.mp
    apply unique.eq_of_getElem_eq
      (by simpa [validatorKeys] using inside i (List.mem_toFinset.mp hi))
      (by simpa [validatorKeys] using inside j (List.mem_toFinset.mp hj))
    simpa [validatorKeys, key] using same
  · intro k hk
    simp only [keysAt, List.mem_toFinset, List.mem_filterMap] at hk
    obtain ⟨i, hi, found⟩ := hk
    exact ⟨i, List.mem_toFinset.mpr hi, by
      simpa [key, Array.getElem?_eq_getElem, inside i hi] using found⟩
  · intro i hi
    simp [key, inside i (List.mem_toFinset.mp hi)]

/-- The reference loss as a sum over the active indices of the reference state.

An index whose validator is slashed at the reference or at the later state contributes nothing. -/
private theorem intervalLoss_reference_indices {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : x.fork < .glamsterdam) :
    referenceLoss x y =
      ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
        match x.state.validators.data[i.toNat]? with
        | none => 0
        | some v => if v.slashed = true ∨ ∃ w ∈ y.state.validators.data.toList,
            w.pubkey = v.pubkey ∧ w.slashed = true then 0 else
          effectiveWeight x.state v.pubkey -
            Models.supported (recentKeys y.state) (effectiveWeight y.state) v.pubkey).sum := by
  classical
  have within := x.state.validators.bound early
  have unique := shared.unique (genesis_unique genesis)
  have distinct : (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).Nodup := by
    simpa [List.Nodup] using (getActiveValidatorIndices_sorted within _).imp UInt64.ne_of_lt
  unfold referenceLoss unslashedKeys
  rw [Finset.filter_filter, Finset.sum_filter, activeKeys,
    intervalLoss_keys_sum x.state _ unique distinct (fun i member => by
      obtain ⟨v, found, _⟩ := (mem_getActiveValidatorIndices within).mp member
      exact (Array.getElem?_eq_some_iff.mp found).1)]
  congr 1
  apply List.map_congr_left
  intro i member
  cases found : x.state.validators.data[i.toNat]? with
  | none => rfl
  | some v =>
    -- With distinct keys, the key of the validator at the index is slashed when it is.
    have present : v ∈ x.state.validators.data.toList := by
      simpa using Array.mem_of_getElem? found
    have slashedX : SlashedAt x.state v.pubkey ↔ v.slashed = true :=
      ⟨fun ⟨u, inside, key, flag⟩ => List.inj_on_of_nodup_map unique inside present key ▸ flag,
        fun flag => ⟨v, present, rfl, flag⟩⟩
    simp only [Option.map_some, Option.getD_some]
    by_cases flag : v.slashed = true <;>
      by_cases later : SlashedAt y.state v.pubkey <;>
      simp_all [SlashedAt]

private theorem effectiveWeight_at {fork : Fork} (s : BeaconState preset fork)
    (unique : PubkeysDistinct s) (i : Nat) (v : Validator)
    (found : s.validators.data[i]? = some v) :
    effectiveWeight s v.pubkey = effectiveAt ⟨fork, s⟩ i := by
  have lookup (vs : List Validator) (distinct : (vs.map (·.pubkey)).Nodup)
      (v : Validator) (member : v ∈ vs) :
      vs.find? (fun w => w.pubkey == v.pubkey) = some v := by
    induction vs with
    | nil => simp at member
    | cons w ws ih =>
      simp only [List.map_cons, List.nodup_cons] at distinct
      rcases List.mem_cons.mp member with rfl | member
      · simp
      · have different : w.pubkey ≠ v.pubkey := by
          intro same
          exact distinct.1 (List.mem_map.mpr ⟨v, member, same.symm⟩)
        simp [different, ih distinct.2 member]
  have member : v ∈ s.validators.data.toList := by
    simpa using Array.mem_of_getElem? found
  simp [effectiveWeight, effectiveAt, found, lookup _ unique v member]

private theorem intervalLoss_recent_supported (y : ForkedBeaconState preset)
    (early : y.fork < .glamsterdam) (unique : PubkeysDistinct y.state)
    (i : ValidatorIndex) (w : Validator) (found : y.state.validators.data[i.toNat]? = some w)
    (recent : isActiveValidator w (getCurrentEpoch y.state) = true ∨
      isActiveValidator w (getPreviousEpoch y.state) = true)
    (unslashed : ¬ SlashedAt y.state w.pubkey) :
    Models.supported (recentKeys y.state) (effectiveWeight y.state) w.pubkey =
      effectiveAt y i.toNat := by
  have selected (epoch : Epoch) (active : isActiveValidator w epoch = true) :
      w.pubkey ∈ keysAt y.state (getActiveValidatorIndices y.state epoch) := by
    simp only [keysAt, List.mem_toFinset, List.mem_filterMap]
    refine ⟨i, (mem_getActiveValidatorIndices (y.state.validators.bound early)).mpr
      ⟨w, found, active⟩, ?_⟩
    simp [found]
  have member : w.pubkey ∈ recentKeys y.state := by
    unfold recentKeys
    refine Finset.mem_filter.mpr ⟨?_, unslashed⟩
    rcases recent with current | previous
    · exact Finset.mem_union_left _ (selected _ current)
    · exact Finset.mem_union_right _ (selected _ previous)
  rw [Models.supported, ite_eq_left member]
  exact effectiveWeight_at y.state unique i.toNat w found

private theorem intervalLoss_sum_bound {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : x.fork < .glamsterdam) (events : List (BalanceEvent preset))
    (departure : ValidatorIndex → Nat)
    (pointwise : ∀ i ∈ getActiveValidatorIndices x.state (getCurrentEpoch x.state),
      ∀ v, x.state.validators.data[i.toNat]? = some v →
      (¬ ∃ w ∈ y.state.validators.data.toList, w.pubkey = v.pubkey ∧ w.slashed = true) →
      v.slashed = false ∧
      effectiveWeight x.state v.pubkey -
          Models.supported (recentKeys y.state) (effectiveWeight y.state) v.pubkey ≤
        departure i +
          (let deficit := effectiveAt x i.toNat - actualBalanceAt x i.toNat +
            (events.map (referenceDebit i.toNat)).sum
           if deficit = 0 then 0 else deficit + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1)) :
    referenceLoss x y ≤
      ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map departure).sum +
        lossCorrection x events := by
  rw [intervalLoss_reference_indices shared genesis early]
  unfold lossCorrection
  rw [← List.sum_map_add]
  apply List.sum_le_sum
  intro i member
  obtain ⟨v, found, _⟩ := (mem_getActiveValidatorIndices (x.state.validators.bound early)).mp member
  simp only [found]
  split
  · exact Nat.zero_le _
  · rename_i unslashed
    obtain ⟨flag, bound⟩ := pointwise i member v found (fun later => unslashed (.inr later))
    simpa only [flag, Bool.false_eq_true, ↓reduceIte] using bound

private theorem intervalLoss_charge_sum (charges : List DepartureCharge) (indices : Finset Nat)
    (high : Nat) :
    (∑ i ∈ indices, match charges.find? (fun c => c.index == i) with
      | some c => if c.epoch ≤ high + 1 then c.amount else 0
      | none => 0) ≤ ((charges.filter fun c => c.epoch ≤ high + 1).map (·.amount)).sum := by
  induction charges with
  | nil => simp
  | cons charge rest ih =>
    have pointwise (i : Nat) :
        (match (charge :: rest).find? (fun c => c.index == i) with
        | some c => if c.epoch ≤ high + 1 then c.amount else 0
        | none => 0) ≤
        (if i = charge.index then if charge.epoch ≤ high + 1 then charge.amount else 0 else 0) +
        (match rest.find? (fun c => c.index == i) with
        | some c => if c.epoch ≤ high + 1 then c.amount else 0
        | none => 0) := by
      by_cases same : charge.index = i
      · subst i
        simp only [List.find?_cons, beq_self_eq_true, ↓reduceIte]
        omega
      · simp [same, Ne.symm same]
    have bound := Finset.sum_le_sum (fun i (_ : i ∈ indices) => pointwise i)
    rw [Finset.sum_add_distrib] at bound
    have single : (∑ i ∈ indices,
        if i = charge.index then if charge.epoch ≤ high + 1 then charge.amount else 0 else 0) ≤
        (if charge.epoch ≤ high + 1 then charge.amount else 0) := by
      by_cases present : charge.index ∈ indices
      · rw [Finset.sum_eq_single charge.index
          (fun i _ different => by simp [different]) (by simp [present])]
        simp
      · have zero : (∑ i ∈ indices,
            if i = charge.index then
              if charge.epoch ≤ high + 1 then charge.amount else 0 else 0) = 0 :=
          Finset.sum_eq_zero fun i member => by
            have different : i ≠ charge.index := fun same => present (same ▸ member)
            simp [different]
        rw [zero]
        exact Nat.zero_le _
    by_cases same : charge.epoch ≤ high + 1
    · simp only [List.filter_cons, decide_eq_true_eq, same, ↓reduceIte,
        List.map_cons, List.sum_cons]
      simp only [same, ↓reduceIte] at single bound
      omega
    · simp only [List.filter_cons, decide_eq_true_eq, same, ↓reduceIte]
      simp only [same, ↓reduceIte] at single bound
      omega

private theorem intervalLoss_charge_active_sum (x : ForkedBeaconState preset)
    (early : x.fork < .glamsterdam) (charges : List DepartureCharge) (high : Nat) :
    ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
      match charges.find? (fun c => c.index == i.toNat) with
      | some c => if c.epoch ≤ high + 1 then c.amount else 0
      | none => 0).sum ≤
        ((charges.filter fun c => c.epoch ≤ high + 1).map (·.amount)).sum := by
  have distinct : (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).Nodup := by
    simpa [List.Nodup] using
      (getActiveValidatorIndices_sorted (x.state.validators.bound early) _).imp UInt64.ne_of_lt
  have injective : Function.Injective UInt64.toNat := fun _ _ h => UInt64.toNat_inj.mp h
  have natDistinct := distinct.map injective
  have bound := intervalLoss_charge_sum charges
    ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map UInt64.toNat).toFinset high
  rw [List.sum_toFinset _ natDistinct, List.map_map] at bound
  exact bound

private theorem intervalLoss_scheduled_sum (x : ForkedBeaconState preset)
    (early : x.fork < .glamsterdam) (high : Nat) :
    ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
      (x.state.validators.data[i.toNat]?.map fun v =>
        if v.exitEpoch != FAR_FUTURE_EPOCH && v.exitEpoch.toNat ≤ high + 1 then
          v.effectiveBalance.toNat else 0).getD 0).sum = scheduledExitCarry x high := by
  let selected (v : Validator) : Bool :=
    v.exitEpoch != FAR_FUTURE_EPOCH && v.exitEpoch.toNat ≤ high + 1
  let weight (v : Validator) := if selected v then v.effectiveBalance.toNat else 0
  have filtered {α β : Type} (items : List α) (f : α → Option β) (g : β → Nat) :
      ((items.filterMap f).map g).sum =
        (items.map fun a => ((f a).map g).getD 0).sum := by
    induction items with
    | nil => rfl
    | cons a rest ih => cases h : f a <;> simp [h, ih]
  unfold getActiveValidatorIndices
  rw [filtered]
  have same : (x.state.validators.data.toList.zipIdx.map fun p =>
      ((if isActiveValidator p.1 (getCurrentEpoch x.state) then some p.2.toUInt64 else none).map
        fun i => (x.state.validators.data[i.toNat]?.map weight).getD 0).getD 0) =
      x.state.validators.data.toList.map fun v =>
        if isActiveValidator v (getCurrentEpoch x.state) then weight v else 0 := by
    conv_rhs => rw [← List.zipIdx_map_fst 0 x.state.validators.data.toList, List.map_map]
    apply List.map_congr_left
    rintro ⟨v, i⟩ member
    have found := List.mem_zipIdx_iff_getElem?.mp member
    have inside := (List.getElem?_eq_some_iff.mp found).1
    have bounded : i < 2 ^ 64 :=
      (lt_of_lt_of_le inside (x.state.validators.bound early)).trans (UInt64.toNat_lt _)
    have found' : x.state.validators.data[i]? = some v := by simpa using found
    cases active : isActiveValidator v (getCurrentEpoch x.state) <;>
      simp [active, Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' bounded, found']
  change (x.state.validators.data.toList.zipIdx.map _).sum = _
  rw [same]
  have sumFiltered (vs : List Validator) :
      (vs.map fun v => if isActiveValidator v (getCurrentEpoch x.state) then weight v else 0).sum =
        ((vs.filter fun v => isActiveValidator v (getCurrentEpoch x.state) && selected v).map
          (·.effectiveBalance.toNat)).sum := by
    induction vs with
    | nil => rfl
    | cons v rest ih =>
      cases active : isActiveValidator v (getCurrentEpoch x.state) <;>
        cases chosen : selected v <;> simp [active, chosen, weight, ih]
  rw [sumFiltered]
  unfold scheduledExitCarry
  simp only [selected, Bool.and_assoc]
  rw [List.sum_eq_foldl, List.foldl_map]

private theorem intervalLoss_sum_departures {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : x.fork < .glamsterdam)
    (high : Nat) (events : List (BalanceEvent preset))
    (pointwise : ∀ i ∈ getActiveValidatorIndices x.state (getCurrentEpoch x.state),
      ∀ v, x.state.validators.data[i.toNat]? = some v →
      (¬ ∃ w ∈ y.state.validators.data.toList, w.pubkey = v.pubkey ∧ w.slashed = true) →
      v.slashed = false ∧
      effectiveWeight x.state v.pubkey -
          Models.supported (recentKeys y.state) (effectiveWeight y.state) v.pubkey ≤
        (if v.exitEpoch != FAR_FUTURE_EPOCH && v.exitEpoch.toNat ≤ high + 1 then
          v.effectiveBalance.toNat else 0) +
        (match tail.departureCharges.find? (fun c => c.index == i.toNat) with
        | some c => if c.epoch ≤ high + 1 then c.amount else 0
        | none => 0) +
        (let deficit := effectiveAt x i.toNat - actualBalanceAt x i.toNat +
          (events.map (referenceDebit i.toNat)).sum
         if deficit = 0 then 0 else deficit + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1)) :
    referenceLoss x y ≤ scheduledExitCarry x high +
      ((tail.departureCharges.filter fun c => c.epoch ≤ high + 1).map (·.amount)).sum +
      lossCorrection x events := by
  let inherited (i : ValidatorIndex) :=
    (x.state.validators.data[i.toNat]?.map fun v =>
      if v.exitEpoch != FAR_FUTURE_EPOCH && v.exitEpoch.toNat ≤ high + 1 then
        v.effectiveBalance.toNat else 0).getD 0
  let charged (i : ValidatorIndex) :=
    match tail.departureCharges.find? (fun c => c.index == i.toNat) with
    | some c => if c.epoch ≤ high + 1 then c.amount else 0
    | none => 0
  have bounded := intervalLoss_sum_bound shared genesis early events
    (fun i => inherited i + charged i) (fun i member v found unslashed => by
      simpa [inherited, found, charged] using pointwise i member v found unslashed)
  rw [List.sum_map_add] at bounded
  have initial := intervalLoss_scheduled_sum x early high
  have added := intervalLoss_charge_active_sum x early tail.departureCharges high
  change _ = scheduledExitCarry x high at initial
  change ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map charged).sum ≤ _
    at added
  change ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map inherited).sum = _
    at initial
  omega

private theorem intervalLoss_referenceDebit_of_recent (event : BalanceEvent preset)
    (i : Nat) (v : Validator) (found : event.before.state.validators.data[i]? = some v)
    (recent : isActiveValidator v (getCurrentEpoch event.before.state) = true ∨
      isActiveValidator v (getPreviousEpoch event.before.state) = true)
    (unslashed : event.source ≠ .slashings) :
    referenceDebit i event = actualBalanceAt event.before i - actualBalanceAt event.after i := by
  rcases recent with current | previous
  · simp [referenceDebit, unslashed, found, current]
  · simp [referenceDebit, unslashed, found, previous]

private theorem intervalLoss_recent_between {f h j : Fork}
    (s : BeaconState preset f) (middle : BeaconState preset h) (t : BeaconState preset j)
    (v w z : Validator) (first : ValidatorLifecycle v w) (last : ValidatorLifecycle w z)
    (epochsBefore : (getCurrentEpoch s).toNat ≤ (getCurrentEpoch middle).toNat)
    (epochsAfter : (getCurrentEpoch middle).toNat ≤ (getCurrentEpoch t).toNat)
    (active : isActiveValidator v (getCurrentEpoch s) = true)
    (recent : isActiveValidator z (getCurrentEpoch t) = true ∨
      isActiveValidator z (getPreviousEpoch t) = true) :
    isActiveValidator w (getCurrentEpoch middle) = true ∨
      isActiveValidator w (getPreviousEpoch middle) = true := by
  have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := by decide
  have activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
      UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at active
    have bound := v.exitEpoch.toNat_lt
    intro unset
    rw [unset, far] at active
    omega
  have activation := first.activationEpoch activated
  have finalActivation := last.activationEpoch (activation ▸ activated)
  by_cases assigned : w.exitEpoch = FAR_FUTURE_EPOCH
  · have bound := v.exitEpoch.toNat_lt
    have epoch := (getCurrentEpoch middle).toNat_lt
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
      UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, getPreviousEpoch_toNat] at active ⊢
    rw [activation, assigned]
    rw [far]
    omega
  · have exit := last.exitEpoch assigned
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
      UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, getPreviousEpoch_toNat] at active recent ⊢
    rw [activation]
    rw [exit, finalActivation, activation] at recent
    rcases recent with current | previous <;> omega

private theorem intervalLoss_recent_unassigned {f h : Fork}
    (s : BeaconState preset f) (t : BeaconState preset h) (v w : Validator)
    (life : ValidatorLifecycle v w)
    (epochs : (getCurrentEpoch s).toNat ≤ (getCurrentEpoch t).toNat)
    (active : isActiveValidator v (getCurrentEpoch s) = true)
    (unset : w.exitEpoch = FAR_FUTURE_EPOCH) :
    isActiveValidator w (getCurrentEpoch t) = true ∨
      isActiveValidator w (getPreviousEpoch t) = true := by
  have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := by decide
  have bound := v.exitEpoch.toNat_lt
  have epochBound := (getCurrentEpoch t).toNat_lt
  have activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
      UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at active
    intro equal
    rw [equal, far] at active
    omega
  have activation := life.activationEpoch activated
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
    UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, getPreviousEpoch_toNat] at active ⊢
  rw [activation, unset, far]
  omega

private theorem intervalLoss_exit_of_not_recent {f h : Fork}
    (s : BeaconState preset f) (t : BeaconState preset h) (v w : Validator)
    (life : ValidatorLifecycle v w)
    (epochs : (getCurrentEpoch s).toNat ≤ (getCurrentEpoch t).toNat)
    (active : isActiveValidator v (getCurrentEpoch s) = true)
    (notRecent : ¬ (isActiveValidator w (getCurrentEpoch t) = true ∨
      isActiveValidator w (getPreviousEpoch t) = true)) :
    w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧ w.exitEpoch.toNat ≤ (getCurrentEpoch t).toNat := by
  have assigned : w.exitEpoch ≠ FAR_FUTURE_EPOCH := fun unset =>
    notRecent (intervalLoss_recent_unassigned s t v w life epochs active unset)
  refine ⟨assigned, ?_⟩
  have activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    have bound := v.exitEpoch.toNat_lt
    have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := by decide
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
      UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at active
    intro unset
    rw [unset, far] at active
    omega
  have activation := life.activationEpoch activated
  have notActive : ¬ isActiveValidator w (getCurrentEpoch t) = true :=
    fun h => notRecent (Or.inl h)
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
    UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at active notActive
  rw [activation] at notActive
  omega

private theorem intervalLoss_supported_events {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events)
    (i : Nat) (v z : Validator) (found : x.state.validators.data[i]? = some v)
    (located : y.state.validators.data[i]? = some z)
    (active : isActiveValidator v (getCurrentEpoch x.state) = true)
    (recent : isActiveValidator z (getCurrentEpoch y.state) = true ∨
      isActiveValidator z (getPreviousEpoch y.state) = true) :
    ∀ event ∈ events, ∃ w, event.before.state.validators.data[i]? = some w ∧
      (isActiveValidator w (getCurrentEpoch event.before.state) = true ∨
        isActiveValidator w (getPreviousEpoch event.before.state) = true) := by
  intro event member
  obtain ⟨first, during, last, _, _, lo, hi⟩ :=
    replay_event_provenance shared tail genesis early high endEpoch
      events replayed event member
  obtain ⟨w, middle, firstLife⟩ := first.validators i v found
  obtain ⟨final, finalFound, lastLife⟩ := (during.trans last).validators i w middle
  have same := Option.some.inj (finalFound.symm.trans located)
  subst final
  exact ⟨w, middle, intervalLoss_recent_between x.state event.before.state y.state
    v w z firstLife lastLife lo hi active recent⟩

private theorem intervalLoss_filtered_coverage {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events)
    (i : Nat)
    (supported : ∀ event ∈ events, ∃ v, event.before.state.validators.data[i]? = some v ∧
      (isActiveValidator v (getCurrentEpoch event.before.state) = true ∨
        isActiveValidator v (getPreviousEpoch event.before.state) = true))
    (slashings : ∀ event ∈ events, event.source = .slashings →
      actualBalanceAt event.before i ≤ actualBalanceAt event.after i) :
    pathDebits i tail.balancePath ≤ (events.map (referenceDebit i)).sum := by
  apply (coverage_run tail early high endEpoch replayed true i).trans
  apply List.sum_le_sum
  intro event member
  change actualBalanceAt event.before i - actualBalanceAt event.after i ≤ referenceDebit i event
  by_cases slashed : event.source = .slashings
  · rw [Nat.sub_eq_zero_of_le (slashings event member slashed)]
    exact Nat.zero_le _
  · obtain ⟨v, found, recent⟩ := supported event member
    rw [intervalLoss_referenceDebit_of_recent event i v found recent slashed]

private theorem intervalLoss_delayed_slashing {fork : Fork} {s t : BeaconState preset fork}
    (early : fork < .glamsterdam) (ok : processSlashings s = .ok t)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v)
    (unslashed : v.slashed = false) :
    actualBalanceAt ⟨fork, t⟩ i = actualBalanceAt ⟨fork, s⟩ i := by
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have notDue : ¬ SlashingPenaltyDue preset (getCurrentEpoch s) v := by
    simp [SlashingPenaltyDue, unslashed]
  by_cases electra : .pectra ≤ fork
  · obtain ⟨_, _, _, _, entries⟩ :=
      processSlashings_balances_of_electra electra (s.validators.bound early) ok
    obtain ⟨w, located, balance⟩ := (entries i).1 inside
    have same : w = v := Option.some.inj (located.symm.trans found)
    subst w
    simp only [notDue, ↓reduceIte] at balance
    simp [actualBalanceAt, balance]
  · obtain ⟨_, _, _, _, entries⟩ :=
      processSlashings_balances_of_lt_electra (Nat.lt_of_not_ge electra) ok
    obtain ⟨w, located, balance⟩ := (entries i).1 inside
    have same : w = v := Option.some.inj (located.symm.trans found)
    subst w
    simp only [notDue, ↓reduceIte] at balance
    simp [actualBalanceAt, balance]

private theorem intervalLoss_increase {fork : Fork} {s t : BeaconState preset fork}
    {index : ValidatorIndex} {amount : Gwei} (ok : increaseBalance s index amount = .ok t)
    (i : Nat) : actualBalanceAt ⟨fork, s⟩ i ≤ actualBalanceAt ⟨fork, t⟩ i := by
  cases found : s.balances.data[i]? with
  | none => simp [actualBalanceAt, found]
  | some balance =>
    obtain ⟨raised, located, value⟩ := balance_increaseBalance ok found
    simp only [actualBalanceAt, found, located, Option.map_some, Option.getD_some]
    omega

private theorem intervalLoss_initial_slashing {fork : Fork} {s t : BeaconState preset fork}
    {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (early : fork < .glamsterdam) (ok : slashValidator config s index whistleblower = .ok t)
    (i : Nat) (different : index.toNat ≠ i) :
    actualBalanceAt ⟨fork, s⟩ i ≤ actualBalanceAt ⟨fork, t⟩ i := by
  obtain ⟨exited, validator, withdrawable, marked, slashed, total, slashings, lowered,
    proposer, reward, raised, last, exitedOk, _, _, markedOk, _, _, _, lower, _, _,
    raise, pay, final⟩ := slashValidator_ok ok
  have first : marked.balances = s.balances := by
    obtain ⟨_, rfl⟩ := setValidator_ok markedOk
    simpa only [BeaconState.putValidator] using coverage_exit exitedOk
  have debit : actualBalanceAt ⟨fork, lowered⟩ i = actualBalanceAt ⟨fork, s⟩ i := by
    obtain ⟨inside, rfl⟩ := decreaseBalance_eq_ok_iff.mp lower
    simp [actualBalanceAt, BeaconState.putBalance, different, first]
  have one := intervalLoss_increase raise i
  have two := intervalLoss_increase pay i
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  simp only [notGloas, ↓reduceDIte] at final
  subst t
  omega

private theorem intervalLoss_unslashed_slashing {fork : Fork} {s t : BeaconState preset fork}
    {index other : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (early : fork < .glamsterdam) (ok : slashValidator config s index whistleblower = .ok t)
    (unslashed : slashedFlag t other = .ok false) :
    actualBalanceAt ⟨fork, s⟩ other.toNat ≤ actualBalanceAt ⟨fork, t⟩ other.toNat := by
  apply intervalLoss_initial_slashing early ok
  intro equal
  have same : index = other := UInt64.toNat_inj.mp equal
  have marked := (slashValidator_slashedFlag ok).1
  rw [same, unslashed] at marked
  cases marked

private theorem intervalLoss_attester_slashing {fork : Fork} {s t : BeaconState preset fork}
    (early : fork < .glamsterdam) (other : ValidatorIndex)
    (indices : List ValidatorIndex) (flag finalFlag : Bool)
    (ok : indices.foldlM (slashIfSlashable config) (s, flag) = .ok (t, finalFlag))
    (unslashed : slashedFlag t other = .ok false) :
    actualBalanceAt ⟨fork, s⟩ other.toNat ≤ actualBalanceAt ⟨fork, t⟩ other.toNat := by
  induction indices generalizing s flag with
  | nil => cases ok; exact Nat.le_refl _
  | cons index rest ih =>
    obtain ⟨⟨middle, nextFlag⟩, first, tail⟩ := bind_ok_iff.mp ok
    have beforeFalse : slashedFlag middle other = .ok false := by
      have flags := (foldlM_slashIfSlashable rest tail).2.1
      cases before : slashedFlag middle other with
      | error error =>
        have sizes := (foldlM_slashIfSlashable rest tail).1.1
        cases found : middle.validators.data[other.toNat]? with
        | some v => simp [slashedFlag, getValidator, found, Except.map] at before
        | none =>
          have outside := Array.getElem?_eq_none_iff.mp found
          have afterOutside : t.validators.data[other.toNat]? = none :=
            Array.getElem?_eq_none_iff.mpr (by simpa only [sizes] using outside)
          simp [slashedFlag, getValidator, afterOutside, Except.map] at unslashed
      | ok value =>
        cases value with
        | false => rfl
        | true => have marked := flags other before; rw [unslashed] at marked; cases marked
    have restBound := ih nextFlag tail
    have firstBound : actualBalanceAt ⟨fork, s⟩ other.toNat ≤
        actualBalanceAt ⟨fork, middle⟩ other.toNat := by
      simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at first
      obtain ⟨v, _, first⟩ := first
      split at first
      · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq,
          Prod.mk.injEq] at first
        obtain ⟨next, slashed, rfl, rfl⟩ := first
        exact intervalLoss_unslashed_slashing early slashed beforeFalse
      · cases first; exact Nat.le_refl _
    exact firstBound.trans restBound

private theorem intervalLoss_proposer_nondebit {fork : Fork} {s t : BeaconState preset fork}
    (early : fork < .glamsterdam) (sl : ProposerSlashing)
    (ok : processProposerSlashing config checks s sl = .ok t) (i : ValidatorIndex)
    (unslashed : slashedFlag t i = .ok false) :
    actualBalanceAt ⟨fork, s⟩ i.toNat ≤ actualBalanceAt ⟨fork, t⟩ i.toNat := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact intervalLoss_unslashed_slashing early slashed unslashed

private theorem intervalLoss_attester_nondebit {fork : Fork} {s t : BeaconState preset fork}
    (early : fork < .glamsterdam) (sl : AttesterSlashing preset fork)
    (ok : processAttesterSlashing config checks s sl = .ok t) (i : ValidatorIndex)
    (unslashed : slashedFlag t i = .ok false) :
    actualBalanceAt ⟨fork, s⟩ i.toNat ≤ actualBalanceAt ⟨fork, t⟩ i.toNat := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨u, flag⟩, folded, _, _, rfl⟩ := ok
  exact intervalLoss_attester_slashing early i _ false flag folded unslashed

private theorem intervalLoss_SlashingSite.nondebit {a b : ForkedBeaconState preset}
    (site : intervalLoss_SlashingSite config checks a b) (early : a.fork < .glamsterdam)
    (i : ValidatorIndex) (v w : Validator)
    (before : a.state.validators.data[i.toNat]? = some v)
    (after : b.state.validators.data[i.toNat]? = some w)
    (first : v.slashed = false) (last : w.slashed = false) :
    actualBalanceAt a i.toNat ≤ actualBalanceAt b i.toNat := by
  cases site with
  | delayed ok =>
    exact le_of_eq (intervalLoss_delayed_slashing early ok i.toNat v before first).symm
  | proposer ok =>
    exact intervalLoss_proposer_nondebit early _ ok i
      (by simp [slashedFlag, getValidator, after, last, Except.map])
  | attester ok =>
    exact intervalLoss_attester_nondebit early _ ok i
      (by simp [slashedFlag, getValidator, after, last, Except.map])

private theorem intervalLoss_event_nondebit {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events)
    (i : ValidatorIndex) (v w : Validator)
    (found : x.state.validators.data[i.toNat]? = some v)
    (located : y.state.validators.data[i.toNat]? = some w) (unslashed : w.slashed = false)
    (event : BalanceEvent preset) (member : event ∈ events) (source : event.source = .slashings) :
    actualBalanceAt event.before i.toNat ≤ actualBalanceAt event.after i.toNat := by
  obtain ⟨first, during, _, _⟩ := replay_event_provenance shared tail genesis
    early high endEpoch events replayed event member
  obtain ⟨before, beforeFound, _⟩ := first.validators i.toNat v found
  obtain ⟨after, afterFound, _⟩ := during.validators i.toNat before beforeFound
  obtain ⟨eventEarly, eventKeeps, finalKeeps, site⟩ :=
    intervalLoss_event_slashed shared tail genesis early high endEpoch events replayed event member
  have notSlashed {f : Fork} {s : BeaconState preset f} (keeps : SlashedPersistence s y.state)
      (v : Validator) (found : s.validators.data[i.toNat]? = some v) : v.slashed = false := by
    cases flag : v.slashed with
    | false => rfl
    | true =>
      obtain ⟨last, lastFound, slashed⟩ := keeps i.toNat v found flag
      have same := Option.some.inj (lastFound.symm.trans located)
      subst last
      simp [unslashed] at slashed
  exact (site source).nondebit eventEarly i before after beforeFound afterFound
    (notSlashed (eventKeeps.trans finalKeeps) before beforeFound)
    (notSlashed finalKeeps after afterFound)

private theorem intervalLoss_rounding (before after deficit increment : Nat)
    (positive : 0 < increment) (alignedBefore : before % increment = 0)
    (alignedAfter : after % increment = 0)
    (bound : before - after ≤ deficit + (increment - 1)) :
    before - after ≤ if deficit = 0 then 0 else deficit + increment - 1 := by
  split
  · rename_i zero
    have divides : increment ∣ before - after :=
      Nat.dvd_sub (Nat.dvd_of_mod_eq_zero alignedBefore) (Nat.dvd_of_mod_eq_zero alignedAfter)
    by_cases loss : 0 < before - after
    · have least := Nat.le_of_dvd loss divides
      omega
    · omega
  · omega

private theorem intervalLoss_effective_loss {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (aligned : MaxEffectiveBalancesAligned preset)
    (early : y.fork < .glamsterdam)
    (i : Nat) (v : Validator) (found : x.state.validators.data[i]? = some v)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (events : List (BalanceEvent preset))
    (covered : pathDebits i tail.balancePath ≤ (events.map (referenceDebit i)).sum) :
    let deficit := effectiveAt x i - actualBalanceAt x i + (events.map (referenceDebit i)).sum
    effectiveAt x i - effectiveAt y i ≤
      if deficit = 0 then 0 else deficit + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1 := by
  intro deficit
  have first := reachable_effective_alignment shared genesis aligned v
    (by simpa using Array.mem_of_getElem? found)
  obtain ⟨w, located, _⟩ := tail.registryLifecycle.validators i v found
  have last := reachable_effective_alignment (shared.append tail) genesis aligned w
    (by simpa using Array.mem_of_getElem? located)
  rcases Nat.eq_zero_or_pos preset.EFFECTIVE_BALANCE_INCREMENT.toNat with zero | increment
  · -- With a zero increment, aligned effective balances are zero, so nothing is lost.
    rw [zero, Nat.mod_zero] at first
    have nothing : effectiveAt x i = 0 := by simp [effectiveAt, found, first]
    rw [nothing, Nat.zero_sub]
    exact Nat.zero_le _
  have bound := effective_loss_from_balance shared tail genesis caps increment early i v found
    activated
  apply intervalLoss_rounding _ _ _ _ increment
  · simpa [effectiveAt, found] using first
  · simpa [effectiveAt, located] using last
  · omega

private theorem intervalLoss_effective_loss_prefix {g x a y : ForkedBeaconState preset}
    (shared : Run config checks g x) (pre : Run config checks x a)
    (post : Run config checks a y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (aligned : MaxEffectiveBalancesAligned preset)
    (early : y.fork < .glamsterdam) (high : Nat)
    (i : Nat) (v : Validator) (found : x.state.validators.data[i]? = some v)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (events : List (BalanceEvent preset))
    (replayed : (pre.append post).balanceEvents high = .ok events)
    (covered : ∀ prior, pre.balanceEvents high = .ok prior →
      pathDebits i pre.balancePath ≤ (prior.map (referenceDebit i)).sum) :
    let deficit := effectiveAt x i - actualBalanceAt x i + (events.map (referenceDebit i)).sum
    effectiveAt x i - effectiveAt a i ≤
      if deficit = 0 then 0 else deficit + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1 := by
  obtain ⟨prior, priorOk, initialEvents⟩ := pre.balanceEvents_prefix post high events replayed
  have bounded := intervalLoss_effective_loss shared pre genesis caps aligned
    (Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early)
    i v found activated prior (covered prior priorOk)
  obtain ⟨rest, rfl⟩ := initialEvents
  simp only [List.map_append, List.sum_append]
  dsimp only at bounded
  split <;> split at bounded <;> omega

private theorem intervalLoss_retained {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (early : y.fork < .glamsterdam)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events)
    (i : ValidatorIndex) (v w : Validator)
    (found : x.state.validators.data[i.toNat]? = some v)
    (located : y.state.validators.data[i.toNat]? = some w)
    (active : isActiveValidator v (getCurrentEpoch x.state) = true)
    (recent : isActiveValidator w (getCurrentEpoch y.state) = true ∨
      isActiveValidator w (getPreviousEpoch y.state) = true)
    (slashings : ∀ event ∈ events, event.source = .slashings →
      actualBalanceAt event.before i.toNat ≤ actualBalanceAt event.after i.toNat)
    (unslashed : ¬ SlashedAt y.state v.pubkey) :
    let deficit := effectiveAt x i.toNat - actualBalanceAt x i.toNat +
      (events.map (referenceDebit i.toNat)).sum
    effectiveWeight x.state v.pubkey -
        Models.supported (recentKeys y.state) (effectiveWeight y.state) v.pubkey ≤
      if deficit = 0 then 0 else deficit + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1 := by
  have supported := intervalLoss_supported_events shared tail genesis early high
    endEpoch events replayed i.toNat v w found located active recent
  have covered := intervalLoss_filtered_coverage tail early high endEpoch events replayed
    i.toNat supported slashings
  have activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    have bound := v.exitEpoch.toNat_lt
    have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := by decide
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
      UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at active
    intro unset
    rw [unset, far] at active
    omega
  obtain ⟨last, lastFound, key⟩ := tail.key_preserved i.toNat v found
  have same := Option.some.inj (lastFound.symm.trans located)
  subst last
  have unique := genesis_unique genesis
  rw [effectiveWeight_at x.state (shared.unique unique) i.toNat v found,
    ← key, intervalLoss_recent_supported y early ((shared.append tail).unique unique)
      i w located recent (by rw [key]; exact unslashed)]
  exact intervalLoss_effective_loss shared tail genesis caps aligned
    early i.toNat v found activated events covered

private theorem intervalLoss_departing {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (early : y.fork < .glamsterdam)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events)
    (i : ValidatorIndex) (v : Validator) (found : x.state.validators.data[i.toNat]? = some v)
    (active : isActiveValidator v (getCurrentEpoch x.state) = true)
    (charge : DepartureCharge) (member : charge ∈ tail.departureCharges)
    (index : charge.index = i.toNat)
    (slashings : ∀ a, ∀ pre : Run config checks x a, ∀ post : Run config checks a y,
      pre.append post = tail → ∀ prior, pre.balanceEvents high = .ok prior →
      ∀ event ∈ prior, event.source = .slashings →
        actualBalanceAt event.before i.toNat ≤ actualBalanceAt event.after i.toNat) :
    let deficit := effectiveAt x i.toNat - actualBalanceAt x i.toNat +
      (events.map (referenceDebit i.toNat)).sum
    effectiveWeight x.state v.pubkey ≤ charge.amount +
      (if deficit = 0 then 0 else deficit + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) := by
  obtain ⟨a, b, pre, step, post, equal, first, last, before, after, unset,
    assigned, amount, epoch⟩ := intervalLoss_charge_site tail charge member
  rw [index] at before after
  have decomposed : pre.append ((Run.nil.snoc step).append post) = tail := by
    have assoc : pre.append ((Run.nil.snoc step).append post) =
        (pre.snoc step).append post := by
      clear tail early endEpoch replayed member slashings equal
      induction post with
      | nil => rfl
      | snoc post next ih => exact congrArg (fun r => r.snoc next) ih
    exact assoc.trans equal
  let rest := (Run.nil.snoc step).append post
  have earlyA := Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) early
  have epochs (p q : ForkedBeaconState preset) (run : Run config checks p q) :
      (getCurrentEpoch p.state).toNat ≤ (getCurrentEpoch q.state).toNat := by
    induction run with
    | nil => exact le_rfl
    | snoc pre step ih => exact ih.trans (coverage_step_epoch step)
  have lastEpoch := (epochs a y rest).trans endEpoch
  obtain ⟨w, located, life⟩ := pre.registryLifecycle.validators i.toNat v found
  have same := Option.some.inj (located.symm.trans before)
  subst w
  have recent := intervalLoss_recent_unassigned x.state a.state v first life
    (epochs x a pre) active unset
  have activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    have bound := v.exitEpoch.toNat_lt
    have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := by decide
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
      UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at active
    intro unset
    rw [unset, far] at active
    omega
  have bound := intervalLoss_effective_loss_prefix shared pre rest genesis caps aligned
    early high i.toNat v found activated events
    (decomposed ▸ replayed) (fun prior priorOk =>
      intervalLoss_filtered_coverage pre earlyA high lastEpoch prior priorOk i.toNat
        (intervalLoss_supported_events shared pre genesis earlyA high lastEpoch
          prior priorOk i.toNat v first found before active recent)
        (slashings a pre rest decomposed prior priorOk))
  rw [effectiveWeight_at x.state (shared.unique (genesis_unique genesis)) i.toNat v found]
  have baseline : effectiveAt a i.toNat = charge.amount := by
    simp [effectiveAt, before, amount]
  rw [baseline] at bound
  change effectiveAt x i.toNat ≤ _
  dsimp only at bound ⊢
  omega

private theorem intervalLoss_pointwise {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (early : y.fork < .glamsterdam)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events)
    (i : ValidatorIndex) (v : Validator) (found : x.state.validators.data[i.toNat]? = some v)
    (active : isActiveValidator v (getCurrentEpoch x.state) = true)
    (slashings : ∀ a, ∀ pre : Run config checks x a, ∀ post : Run config checks a y,
      pre.append post = tail → ∀ prior, pre.balanceEvents high = .ok prior →
      ∀ event ∈ prior, event.source = .slashings →
        actualBalanceAt event.before i.toNat ≤ actualBalanceAt event.after i.toNat)
    (unslashed : ¬ SlashedAt y.state v.pubkey) :
    let deficit := effectiveAt x i.toNat - actualBalanceAt x i.toNat +
      (events.map (referenceDebit i.toNat)).sum
    effectiveWeight x.state v.pubkey -
        Models.supported (recentKeys y.state) (effectiveWeight y.state) v.pubkey ≤
      (if v.exitEpoch != FAR_FUTURE_EPOCH && v.exitEpoch.toNat ≤ high + 1 then
        v.effectiveBalance.toNat else 0) +
      (match tail.departureCharges.find? (fun c => c.index == i.toNat) with
      | some c => if c.epoch ≤ high + 1 then c.amount else 0
      | none => 0) +
      (if deficit = 0 then 0 else deficit + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) := by
  obtain ⟨w, located, life⟩ := tail.registryLifecycle.validators i.toNat v found
  by_cases recent : isActiveValidator w (getCurrentEpoch y.state) = true ∨
      isActiveValidator w (getPreviousEpoch y.state) = true
  · have bound := intervalLoss_retained shared tail genesis caps aligned early high
      endEpoch events replayed i v w found located active recent
      (slashings y tail .nil rfl events replayed) unslashed
    dsimp only at bound ⊢
    omega
  · have epochs : (getCurrentEpoch x.state).toNat ≤ (getCurrentEpoch y.state).toNat := by
      clear early endEpoch replayed slashings located recent unslashed
      induction tail with
      | nil => exact le_rfl
      | snoc pre step ih => exact ih.trans (coverage_step_epoch step)
    obtain ⟨assigned, exited⟩ :=
      intervalLoss_exit_of_not_recent x.state y.state v w life epochs active recent
    have baseline := tail.departure_baseline i.toNat (Array.getElem?_eq_some_iff.mp found).1 w
      located assigned
    cases chosen : tail.departureCharges.find? (fun c => c.index == i.toNat) with
    | some charge =>
      rw [chosen] at baseline
      obtain ⟨index, epoch⟩ := baseline
      have bound := intervalLoss_departing shared tail genesis caps aligned early high
        endEpoch events replayed i v found active charge (List.mem_of_find?_eq_some chosen)
        index slashings
      have within : charge.epoch ≤ high + 1 := by omega
      simp only [within, ↓reduceIte]
      dsimp only at bound ⊢
      omega
    | none =>
      rw [chosen] at baseline
      obtain ⟨old, before, exit⟩ := baseline
      have same := Option.some.inj (before.symm.trans found)
      subst old
      have initialAssigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH := by simpa [exit] using assigned
      have within : v.exitEpoch.toNat ≤ high + 1 := by rw [exit]; omega
      have selected : (v.exitEpoch != FAR_FUTURE_EPOCH && v.exitEpoch.toNat ≤ high + 1) = true :=
        by simp [initialAssigned, within]
      simp only [selected, ↓reduceIte]
      have weight := effectiveWeight_at x.state (shared.unique (genesis_unique genesis))
        i.toNat v found
      have value : effectiveWeight x.state v.pubkey = v.effectiveBalance.toNat := by
        simpa [effectiveAt, found] using weight
      rw [value]
      omega

private theorem intervalLoss_departure_bound {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (early : y.fork < .glamsterdam)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    referenceLoss x y ≤ scheduledExitCarry x high +
      ((tail.departureCharges.filter fun c => c.epoch ≤ high + 1).map (·.amount)).sum +
      lossCorrection x events := by
  have earlyX := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  apply intervalLoss_sum_departures shared tail genesis earlyX high events
  intro i member v found unslashed
  obtain ⟨w, located, key⟩ := tail.key_preserved i.toNat v found
  have finalFlag : w.slashed = false := by
    cases flag : w.slashed with
    | false => rfl
    | true => exact False.elim (unslashed ⟨w, by simpa using Array.mem_of_getElem? located,
        key, flag⟩)
  have initialFlag : v.slashed = false := by
    cases flag : v.slashed with
    | false => rfl
    | true =>
      obtain ⟨last, lastFound, slashed⟩ := tail.slashedPersistence i.toNat v found flag
      have same := Option.some.inj (lastFound.symm.trans located)
      subst last
      simp [finalFlag] at slashed
  refine ⟨initialFlag, ?_⟩
  obtain ⟨old, oldFound, active⟩ :=
    (mem_getActiveValidatorIndices (x.state.validators.bound earlyX)).mp member
  have same := Option.some.inj (oldFound.symm.trans found)
  subst old
  refine intervalLoss_pointwise shared tail genesis caps aligned early high endEpoch
    events replayed i v found active ?_ unslashed
  intro a pre post equal prior priorOk event eventMember source
  have earlyA := Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early
  have epochBound : (getCurrentEpoch a.state).toNat ≤ high + 1 := by
    have monotone : (getCurrentEpoch a.state).toNat ≤ (getCurrentEpoch y.state).toNat := by
      clear tail early endEpoch replayed unslashed located key finalFlag equal
      induction post with
      | nil => exact le_rfl
      | snoc pre step ih => exact ih.trans (coverage_step_epoch step)
    omega
  obtain ⟨middle, middleFound, _⟩ := pre.registryLifecycle.validators i.toNat v found
  have middleFlag : middle.slashed = false := by
    cases flag : middle.slashed with
    | false => rfl
    | true =>
      obtain ⟨last, lastFound, slashed⟩ :=
        post.slashedPersistence i.toNat middle middleFound flag
      have same := Option.some.inj (lastFound.symm.trans located)
      subst last
      simp [finalFlag] at slashed
  exact intervalLoss_event_nondebit shared pre genesis earlyA high epochBound
    prior priorOk i v middle found middleFound middleFlag event eventMember source

private theorem intervalLoss_consolidation_rate {fork : Fork}
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

/-- Bound exits and retained-key losses, omitting keys with slashing evidence.

The source envelope can charge a pre-exit deficit as well as the later departure.

The exact referenceLoss does not double-count that key. -/
private theorem nonaccountable_losses_over_interval {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    referenceLoss x y ≤
      exitWindow (config := config) x high events + lossCorrection x events := by
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by
    have slots := parameters.slots
    omega
  have registry := registry_le_window tail early high endEpoch positive
  -- Every reachable prefix uses the full interval's funding credits or registry allowance.
  have prefixBound {a b : ForkedBeaconState preset} (pre : Run config checks x a)
      (step : Step config checks a b) (post : Run config checks b y)
      (same : (pre.snoc step).append post = tail) :
      Models.stake (effectiveWeight a.state) (activeKeys a.state) ≤
        activeStakeWindow (config := config) x high events := by
    let rest := (Run.nil.snoc step).append post
    have joined : pre.append rest = tail := by
      have reassociated {z : ForkedBeaconState preset} (post : Run config checks b z) :
          pre.append ((Run.nil.snoc step).append post) = (pre.snoc step).append post := by
        induction post with
        | nil => rfl
        | snoc post next ih => exact congrArg (fun run => run.snoc next) ih
      exact (reassociated post).trans same
    have earlyA := Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) early
    have epochA : (getCurrentEpoch a.state).toNat ≤ high + 1 := by
      have ordered := currentEpoch_le_of_chainSteps rest.chainSteps
      rw [UInt64.le_iff_toNat_le] at ordered
      omega
    by_cases funded : .pectra ≤ x.fork ∧
        2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
    · obtain ⟨prior, priorOk, initial⟩ := pre.balanceEvents_prefix rest high events
        (joined ▸ replayed)
      have bound := active_stake_le_window shared pre genesis
        funded.1 earlyA funded.2 high epochA prior priorOk
      have credits : (prior.map fundingCredit).sum ≤ (events.map fundingCredit).sum := by
        obtain ⟨remaining, rfl⟩ := initial
        simp only [List.map_append, List.sum_append]
        omega
      simp only [activeStakeWindow, funded.1, funded.2, and_self, ↓reduceIte] at bound ⊢
      omega
    -- The fallback also covers intervals that cross Electra and small withdrawal delays.
    · have unique := (shared.append pre).unique (genesis_unique genesis)
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
      have size := (registryGrows_of_chainSteps rest.chainSteps).trans registry
      exact weight.trans (by
        simpa only [activeStakeWindow, funded, ↓reduceIte] using
          Nat.mul_le_mul_right preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat size)
  -- A reachable block input bounds the active weight at each internal call site.
  have rates : ∀ site ∈ tail.consolidationSites,
      .pectra ≤ site.fork → ∀ (rate : Gwei),
        getConsolidationChurnLimit config site.state = .ok rate →
          rate.toNat ≤ consolidationRate (preset := preset) (config := config)
            (activeStakeWindow (config := config) x high events) := by
    intro site member _ rate computed
    obtain ⟨a, b, pre, step, post, same, fork, _, unique, weight⟩ :=
      consolidationSites_provenance shared tail genesis early site member
    have earlySite : site.fork < .glamsterdam := by
      rw [fork]
      exact Nat.lt_of_le_of_lt
        (Nat.le_trans step.chainStep.fork_le (fork_le_of_chainSteps post.chainSteps)) early
    have notGloas : ¬ .glamsterdam ≤ site.fork := Nat.not_le_of_lt earlySite
    cases read : getTotalActiveBalance site.state with
    | error error =>
      simp only [getConsolidationChurnLimit, notGloas, ↓reduceIte,
        getBalanceChurnLimit, read, bind, Except.bind] at computed
      cases computed
    | ok total =>
      obtain ⟨inside, _, totalEq⟩ :=
        getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok read)
      have active := keys_weight site.state _ unique inside
      have bounded := weight.trans (prefixBound pre step post same)
      apply intervalLoss_consolidation_rate earlySite read computed
      rw [totalEq]
      apply max_le_max_left
      unfold activeKeys at bounded
      rw [active] at bounded
      simpa only [Models.stake, balanceAt] using bounded
  -- Add scheduled exits and retained-key corrections to the queue window.
  have charges := departure_charges_le_window shared tail genesis caps early high
    (registryWindow x high)
    (consolidationRate (preset := preset) (config := config)
      (activeStakeWindow (config := config) x high events)) registry rates
  have losses := intervalLoss_departure_bound shared tail genesis caps aligned
    early high endEpoch events replayed
  change _ ≤ queueCarry x high + driftHorizon x high * _ at charges
  unfold exitWindow
  omega

private theorem intervalGain_existing_funding {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (i : Nat) (present : i < x.state.validators.data.size) :
    effectiveAt y i ≤ max (effectiveAt x i) (actualBalanceAt x i) +
      pathCredits i tail.balancePath := by
  -- Effective stake above actual balance is retained until a later update lowers it.
  have gain := effective_gain_from_balance tail early i present
  omega

private theorem intervalGain_no_reentry {x y : ForkedBeaconState preset}
    (kept : RegistryLifecycle x.state y.state) (i : Nat) (v w : Validator)
    (before : x.state.validators.data[i]? = some v)
    (after : y.state.validators.data[i]? = some w)
    (assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH)
    (exited : v.exitEpoch.toNat ≤ (getPreviousEpoch y.state).toNat) :
    isActiveValidator w (getCurrentEpoch y.state) = false ∧
      isActiveValidator w (getPreviousEpoch y.state) = false := by
  obtain ⟨last, found, lifecycle⟩ := kept.validators i v before
  have same : last = w := Option.some.inj (found.symm.trans after)
  have exit := same ▸ lifecycle.exitEpoch assigned
  have previous : (getPreviousEpoch y.state).toNat ≤ (getCurrentEpoch y.state).toNat := by
    rw [getPreviousEpoch_toNat]
    omega
  have currentExit : ¬ getCurrentEpoch y.state < w.exitEpoch := by
    rw [exit, UInt64.lt_iff_toNat_lt]
    omega
  have previousExit : ¬ getPreviousEpoch y.state < w.exitEpoch := by
    rw [exit, UInt64.lt_iff_toNat_lt]
    omega
  simp [isActiveValidator, currentExit, previousExit]

private theorem intervalGain_carry_cases {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (i : Nat) (v w : Validator)
    (before : x.state.validators.data[i]? = some v)
    (after : y.state.validators.data[i]? = some w)
    (inactive : isActiveValidator v (getCurrentEpoch x.state) = false)
    (recent : isActiveValidator w (getCurrentEpoch y.state) = true ∨
      isActiveValidator w (getPreviousEpoch y.state) = true) :
    isActiveValidator v (getPreviousEpoch x.state) = true ∨
      getCurrentEpoch x.state < v.activationEpoch := by
  have epochs : (getCurrentEpoch x.state).toNat ≤ (getCurrentEpoch y.state).toNat := by
    clear after recent
    induction tail with
    | nil => exact Nat.le_refl _
    | snoc pre step ih => exact ih.trans (coverage_step_epoch step)
  obtain ⟨last, found, lifecycle⟩ := tail.registryLifecycle.validators i v before
  have same : last = w := Option.some.inj (found.symm.trans after)
  subst last
  by_cases future : getCurrentEpoch x.state < v.activationEpoch
  · exact Or.inr future
  left
  have bounded : (getCurrentEpoch x.state).toNat < FAR_FUTURE_EPOCH.toNat := by
    have ne := getCurrentEpoch_ne_farFuture twoSlots x.state
    have bound := (getCurrentEpoch x.state).toNat_lt_size
    have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    have different : (getCurrentEpoch x.state).toNat ≠ FAR_FUTURE_EPOCH.toNat := by
      exact fun h => ne (UInt64.toNat_inj.mp h)
    simp only [UInt64.size] at bound
    omega
  have assigned : v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    rw [UInt64.lt_iff_toNat_lt] at future
    intro eq
    rw [eq] at future
    omega
  have activation := lifecycle.activationEpoch assigned
  have exitAssigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH := by
    simp only [isActiveValidator, Bool.and_eq_false_iff, decide_eq_false_iff_not,
      UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at inactive
    rw [UInt64.lt_iff_toNat_lt] at future
    intro eq
    rw [eq] at inactive
    omega
  have exit := lifecycle.exitEpoch exitAssigned
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
    UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, getPreviousEpoch_toNat,
    activation, exit] at recent ⊢
  simp only [isActiveValidator, Bool.and_eq_false_iff, decide_eq_false_iff_not,
    UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at inactive
  rw [UInt64.lt_iff_toNat_lt] at future
  omega

private theorem intervalGain_withdrawn_excluded {x y : ForkedBeaconState preset}
    (kept : RegistryLifecycle x.state y.state) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (ordered : ExitsOrdered x.state) (i : Nat) (v w : Validator)
    (before : x.state.validators.data[i]? = some v)
    (after : y.state.validators.data[i]? = some w)
    (withdrawn : v.withdrawableEpoch.toNat ≤ (getCurrentEpoch x.state).toNat)
    (later : (getCurrentEpoch x.state).toNat < (getCurrentEpoch y.state).toNat) :
    isActiveValidator w (getCurrentEpoch y.state) = false ∧
      isActiveValidator w (getPreviousEpoch y.state) = false := by
  have exit := UInt64.le_iff_toNat_le.mp (ordered v (Array.mem_of_getElem? before))
  have assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH := by
    have ne := getCurrentEpoch_ne_farFuture twoSlots x.state
    have bound := (getCurrentEpoch x.state).toNat_lt_size
    have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    have different : (getCurrentEpoch x.state).toNat ≠ FAR_FUTURE_EPOCH.toNat := by
      exact fun h => ne (UInt64.toNat_inj.mp h)
    simp only [UInt64.size] at bound
    intro eq
    rw [eq] at exit
    omega
  apply intervalGain_no_reentry kept i v w before after assigned
  rw [getPreviousEpoch_toNat]
  omega

private theorem intervalGain_recent_not_withdrawn {x y : ForkedBeaconState preset}
    (kept : RegistryLifecycle x.state y.state) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (ordered : ExitsOrdered x.state) (i : Nat) (v w : Validator)
    (before : x.state.validators.data[i]? = some v)
    (after : y.state.validators.data[i]? = some w)
    (later : (getCurrentEpoch x.state).toNat < (getCurrentEpoch y.state).toNat)
    (recent : isActiveValidator w (getCurrentEpoch y.state) = true ∨
      isActiveValidator w (getPreviousEpoch y.state) = true) :
    (getCurrentEpoch x.state).toNat < v.withdrawableEpoch.toNat := by
  by_contra withdrawn
  have excluded := intervalGain_withdrawn_excluded kept twoSlots ordered i v w before after
    (by omega) later
  rcases recent with current | previous
  · simp [excluded.1] at current
  · simp [excluded.2] at previous

private theorem intervalGain_index_bound {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (early : y.fork < .glamsterdam)
    (i : Nat) (w : Validator) (after : y.state.validators.data[i]? = some w)
    (recent : isActiveValidator w (getCurrentEpoch y.state) = true ∨
      isActiveValidator w (getPreviousEpoch y.state) = true) :
    effectiveAt y i -
        (if (x.state.validators.data[i]?.map fun v =>
          isActiveValidator v (getCurrentEpoch x.state)).getD false then effectiveAt x i else 0) ≤
      (match x.state.validators.data[i]? with
      | none => 0
      | some v => if isActiveValidator v (getCurrentEpoch x.state) then
          actualBalanceAt x i - effectiveAt x i
        else if isActiveValidator v (getPreviousEpoch x.state) ||
            getCurrentEpoch x.state < v.activationEpoch then
          max (effectiveAt x i) (actualBalanceAt x i)
        else 0) + pathCredits i tail.balancePath := by
  -- Admissions spend later credits; existing inactive keys retain their initial funding.
  cases before : x.state.validators.data[i]? with
  | none =>
    have absent : x.state.validators.data.size ≤ i := by
      simpa using (Array.getElem?_eq_none_iff.mp before)
    have bound := joining_growth_from_admission shared tail genesis early i absent
    simpa only [Option.map_none, Option.getD_none, Bool.false_eq_true, ↓reduceIte,
      Nat.sub_zero, Nat.zero_add] using bound
  | some v =>
    have present := (Array.getElem?_eq_some_iff.mp before).1
    cases active : isActiveValidator v (getCurrentEpoch x.state) with
    | true =>
      simpa only [Option.map_some, Option.getD_some, active, ↓reduceIte]
        using effective_gain_from_balance tail early i present
    | false =>
      have carried := intervalGain_carry_cases tail twoSlots i v w before after active recent
      have selected : (isActiveValidator v (getPreviousEpoch x.state) ||
          getCurrentEpoch x.state < v.activationEpoch) = true := by
        simpa only [Bool.or_eq_true, decide_eq_true_eq] using carried
      simpa only [Option.map_some, Option.getD_some, active, Bool.false_eq_true,
        ↓reduceIte, Nat.sub_zero, selected]
        using intervalGain_existing_funding tail early i present

private theorem intervalGain_active_key {fork : Fork} (s : BeaconState preset fork)
    (within : s.RegistryWithinLimit) (unique : PubkeysDistinct s)
    (i : Nat) (v : Validator) (found : s.validators.data[i]? = some v) :
    v.pubkey ∈ activeKeys s ↔ isActiveValidator v (getCurrentEpoch s) = true := by
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have small : i < 2 ^ 64 := by
    exact (Nat.lt_of_lt_of_le inside within).trans (UInt64.toNat_lt _)
  have numeric : i.toUInt64.toNat = i := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' small]
  constructor
  · intro member
    simp only [activeKeys, keysAt, List.mem_toFinset, List.mem_filterMap] at member
    obtain ⟨j, active, key⟩ := member
    obtain ⟨w, read, active⟩ := (mem_getActiveValidatorIndices within).mp active
    have sameKey : w.pubkey = v.pubkey := by simpa [read] using key
    obtain ⟨hi, vi⟩ := Array.getElem?_eq_some_iff.mp found
    obtain ⟨hj, wj⟩ := Array.getElem?_eq_some_iff.mp read
    have same : j.toNat = i := unique.eq_of_getElem_eq
      (by simpa [validatorKeys] using hj) (by simpa [validatorKeys] using hi)
      (by simpa [validatorKeys, vi, wj] using sameKey)
    have equal : w = v := Option.some.inj ((same ▸ read).symm.trans found)
    simpa [equal] using active
  · intro active
    simp only [activeKeys, keysAt, List.mem_toFinset, List.mem_filterMap]
    refine ⟨i.toUInt64, (mem_getActiveValidatorIndices within).mpr
      ⟨v, by simpa [numeric] using found, active⟩, ?_⟩
    simp [numeric, found]

private theorem intervalGain_reference_at {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .glamsterdam)
    (i : Nat) (w : Validator) (after : y.state.validators.data[i]? = some w) :
    Models.supported (activeKeys x.state) (effectiveWeight x.state) w.pubkey =
      (if (x.state.validators.data[i]?.map fun v =>
        isActiveValidator v (getCurrentEpoch x.state)).getD false then effectiveAt x i else 0) := by
  have uniqueX := shared.unique (genesis_unique genesis)
  have uniqueY := (shared.append tail).unique (genesis_unique genesis)
  have earlyX := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have within := x.state.validators.bound earlyX
  have sameIndex {j : Nat} {v : Validator} (before : x.state.validators.data[j]? = some v)
      (key : v.pubkey = w.pubkey) : j = i := by
    obtain ⟨last, found, preserved⟩ := tail.key_preserved j v before
    obtain ⟨hj, lastEq⟩ := Array.getElem?_eq_some_iff.mp found
    obtain ⟨hi, wEq⟩ := Array.getElem?_eq_some_iff.mp after
    exact uniqueY.eq_of_getElem_eq
      (by simpa [validatorKeys] using hj) (by simpa [validatorKeys] using hi)
      (by simpa [validatorKeys, lastEq, wEq] using preserved.trans key)
  cases before : x.state.validators.data[i]? with
  | none =>
    have absent : w.pubkey ∉ activeKeys x.state := by
      intro member
      simp only [activeKeys, keysAt, List.mem_toFinset, List.mem_filterMap] at member
      obtain ⟨j, active, key⟩ := member
      obtain ⟨v, found, _⟩ := (mem_getActiveValidatorIndices within).mp active
      have same := sameIndex found (by simpa [found] using key)
      rw [same, before] at found
      cases found
    simp [Models.supported, absent]
  | some v =>
    obtain ⟨last, found, preserved⟩ := tail.key_preserved i v before
    have same : last = w := Option.some.inj (found.symm.trans after)
    have key : w.pubkey = v.pubkey := same ▸ preserved
    rw [key]
    simp only [Models.supported, intervalGain_active_key x.state within uniqueX
      i v before, effectiveWeight_at x.state uniqueX i v before,
      Option.map_some, Option.getD_some]

private theorem intervalGain_recent_key {fork : Fork} (s : BeaconState preset fork)
    (within : s.RegistryWithinLimit)
    (key : Cryptography.Bls.BLSPubkey) :
    key ∈ activeKeys s ∪ keysAt s (getActiveValidatorIndices s (getPreviousEpoch s)) ↔
      ∃ (i : Nat) (v : Validator), s.validators.data[i]? = some v ∧ v.pubkey = key ∧
      (isActiveValidator v (getCurrentEpoch s) = true ∨
        isActiveValidator v (getPreviousEpoch s) = true) := by
  have member (epoch : Epoch) : key ∈ keysAt s (getActiveValidatorIndices s epoch) ↔
      ∃ (i : Nat) (v : Validator), s.validators.data[i]? = some v ∧ v.pubkey = key ∧
        isActiveValidator v epoch = true := by
    constructor
    · intro selected
      simp only [keysAt, List.mem_toFinset, List.mem_filterMap] at selected
      obtain ⟨i, active, keyEq⟩ := selected
      obtain ⟨v, found, active⟩ := (mem_getActiveValidatorIndices within).mp active
      exact ⟨i.toNat, v, found, by simpa [found] using keyEq, active⟩
    · rintro ⟨i, v, found, keyEq, active⟩
      have inside := (Array.getElem?_eq_some_iff.mp found).1
      have small := (Nat.lt_of_lt_of_le inside within).trans (UInt64.toNat_lt _)
      have numeric : i.toUInt64.toNat = i := by
        rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' small]
      simp only [keysAt, List.mem_toFinset, List.mem_filterMap]
      refine ⟨i.toUInt64, (mem_getActiveValidatorIndices within).mpr
        ⟨v, by simpa [numeric] using found, active⟩, ?_⟩
      simp [numeric, found, keyEq]
  simp only [Finset.mem_union, activeKeys, member]
  constructor
  · rintro (⟨i, v, found, keyEq, active⟩ | ⟨i, v, found, keyEq, active⟩)
    · exact ⟨i, v, found, keyEq, Or.inl active⟩
    · exact ⟨i, v, found, keyEq, Or.inr active⟩
  · rintro ⟨i, v, found, keyEq, active | active⟩
    · exact Or.inl ⟨i, v, found, keyEq, active⟩
    · exact Or.inr ⟨i, v, found, keyEq, active⟩

private def intervalGain_indices (y : ForkedBeaconState preset) : Finset Nat :=
  (Finset.range y.state.validators.data.size).filter fun i =>
    ∃ w, y.state.validators.data[i]? = some w ∧
      (isActiveValidator w (getCurrentEpoch y.state) = true ∨
        isActiveValidator w (getPreviousEpoch y.state) = true)

/-- The reference gain is at most a sum over the indices recent at the later state.

It is an inequality: the slashed recent keys add terms to the index sum but not to the gain. -/
private theorem intervalGain_reference_sum {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .glamsterdam) :
    referenceGain x y ≤ ∑ i ∈ intervalGain_indices y,
      (effectiveAt y i -
        (if (x.state.validators.data[i]?.map fun v =>
          isActiveValidator v (getCurrentEpoch x.state)).getD false then
            effectiveAt x i else 0)) := by
  have unique := (shared.append tail).unique (genesis_unique genesis)
  have inside (i) (h : i ∈ intervalGain_indices y) : i < y.state.validators.data.size :=
    Finset.mem_range.mp (Finset.mem_filter.mp h).1
  let key (i : Nat) (h : i ∈ intervalGain_indices y) :=
    (y.state.validators.data[i]'(inside i h)).pubkey
  classical
  -- A recent key is unslashed now, so it was unslashed at the reference by forward persistence.
  --
  -- Its support over the unslashed reference keys is then its support over the active keys.
  have support : ∀ k ∈ recentKeys y.state,
      Models.supported (unslashedKeys x.state) (effectiveWeight x.state) k =
        Models.supported (activeKeys x.state) (effectiveWeight x.state) k := by
    intro k member
    unfold recentKeys at member
    have unslashedX : ¬ SlashedAt x.state k := fun slashed =>
      (Finset.mem_filter.mp member).2 (slashedAt_forward tail slashed)
    unfold Models.supported unslashedKeys
    simp only [Finset.mem_filter, unslashedX, not_false_eq_true, and_true]
  -- The unslashed recent keys are among all recent keys, whose sum is the index envelope.
  have subset : recentKeys y.state ⊆ activeKeys y.state ∪
      keysAt y.state (getActiveValidatorIndices y.state (getPreviousEpoch y.state)) := by
    unfold recentKeys
    exact Finset.filter_subset _ _
  unfold referenceGain
  rw [Finset.sum_congr rfl (fun k member => by rw [support k member])]
  refine (Finset.sum_le_sum_of_subset_of_nonneg subset (fun _ _ _ => Nat.zero_le _)).trans
    (Nat.le_of_eq ?_)
  symm
  -- Unique keys and preserved registry positions identify the reference subtraction.
  apply Finset.sum_bij key
  · intro i hi
    obtain ⟨w, found, recent⟩ := (Finset.mem_filter.mp hi).2
    apply (intervalGain_recent_key y.state (y.state.validators.bound early) _).mpr
    refine ⟨i, w, found, ?_, recent⟩
    simp only [key, (Array.getElem?_eq_some_iff.mp found).2]
  · intro i hi j hj equal
    exact unique.eq_of_getElem_eq
      (by simpa [validatorKeys] using inside i hi)
      (by simpa [validatorKeys] using inside j hj)
      (by simpa [validatorKeys, key] using equal)
  · intro k hk
    obtain ⟨i, w, found, same, recent⟩ :=
      (intervalGain_recent_key y.state (y.state.validators.bound early) k).mp hk
    have hi : i ∈ intervalGain_indices y := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1, w, found, recent⟩
    refine ⟨i, hi, ?_⟩
    simpa only [key, (Array.getElem?_eq_some_iff.mp found).2] using same
  · intro i hi
    obtain ⟨w, found, _⟩ := (Finset.mem_filter.mp hi).2
    have keyEq : key i hi = w.pubkey := by
      simp only [key, (Array.getElem?_eq_some_iff.mp found).2]
    rw [keyEq, effectiveWeight_at y.state unique i w found,
      intervalGain_reference_at shared tail genesis early i w found]

private def intervalGain_initial (x : ForkedBeaconState preset) (i : Nat) : Nat :=
  match x.state.validators.data[i]? with
  | none => 0
  | some v => if isActiveValidator v (getCurrentEpoch x.state) then
      actualBalanceAt x i - effectiveAt x i
    else if isActiveValidator v (getPreviousEpoch x.state) ||
        getCurrentEpoch x.state < v.activationEpoch then
      max (effectiveAt x i) (actualBalanceAt x i)
    else 0

private theorem intervalGain_path_bound {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (early : y.fork < .glamsterdam) :
    referenceGain x y ≤ (∑ i ∈ intervalGain_indices y, intervalGain_initial x i) +
      ∑ i ∈ intervalGain_indices y, pathCredits i tail.balancePath := by
  refine (intervalGain_reference_sum shared tail genesis early).trans ?_
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i member
  obtain ⟨w, found, recent⟩ := (Finset.mem_filter.mp member).2
  exact intervalGain_index_bound shared tail genesis twoSlots early i w found recent

private theorem intervalGain_zip_sum (vs : List Validator) (f : Validator → Nat → Nat) :
    (vs.zipIdx.map fun (v, i) => f v i).sum =
      ∑ i ∈ Finset.range vs.length, (vs[i]?.map (fun v => f v i)).getD 0 := by
  let weight := fun i => (vs[i]?.map (fun v => f v i)).getD 0
  have same : vs.zipIdx.map (fun (v, i) => f v i) =
      (vs.zipIdx.map Prod.snd).map weight := by
    rw [List.map_map]
    apply List.map_congr_left
    rintro ⟨v, i⟩ member
    have found := List.mem_zipIdx_iff_getElem?.mp member
    simp [weight, found]
  rw [same, List.zipIdx_map_snd]
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range,
    Multiset.map_coe, Multiset.sum_coe, List.range_eq_range']

private theorem intervalGain_excess_sum (x : ForkedBeaconState preset)
    (early : x.fork < .glamsterdam) :
    initialExcess x = ∑ i ∈ Finset.range x.state.validators.data.size,
      (x.state.validators.data[i]?.map fun v =>
        if isActiveValidator v (getCurrentEpoch x.state) then
          actualBalanceAt x i - effectiveAt x i else 0).getD 0 := by
  have filterSum {α : Type} (xs : List α) (f : α → Option Nat) :
      (xs.filterMap f).sum = (xs.map fun a => (f a).getD 0).sum := by
    induction xs with
    | nil => rfl
    | cons a xs ih => cases h : f a <;> simp [h, ih]
  unfold initialExcess getActiveValidatorIndices
  rw [List.map_filterMap, filterSum]
  have zipped := intervalGain_zip_sum x.state.validators.data.toList
    (fun v i => if isActiveValidator v (getCurrentEpoch x.state) then
      actualBalanceAt x i - effectiveAt x i else 0)
  simp only [Array.length_toList, Array.getElem?_toList] at zipped
  rw [← zipped]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨v, i⟩ member
  have found := List.mem_zipIdx_iff_getElem?.mp member
  have inside := (List.getElem?_eq_some_iff.mp found).1
  have small : i < 2 ^ 64 :=
    (Nat.lt_of_lt_of_le (by simpa using inside) (x.state.validators.bound early)).trans
      (UInt64.toNat_lt _)
  have numeric : i.toUInt64.toNat = i := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' small]
  dsimp only [Function.comp_def]
  split <;> simp_all
  all_goals simp only [Nat.mod_eq_of_lt small]

private theorem intervalGain_initial_sum (x : ForkedBeaconState preset)
    (early : x.fork < .glamsterdam) :
    (∑ i ∈ Finset.range x.state.validators.data.size, intervalGain_initial x i) =
      activationCarry x + initialExcess x := by
  rw [intervalGain_excess_sum x early]
  unfold activationCarry
  rw [intervalGain_zip_sum x.state.validators.data.toList
    (fun v i => if isActiveValidator v (getCurrentEpoch x.state) then 0
      else if isActiveValidator v (getPreviousEpoch x.state) ||
          getCurrentEpoch x.state < v.activationEpoch then
        max (effectiveAt x i) (actualBalanceAt x i) else 0)]
  simp only [Array.length_toList, Array.getElem?_toList]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases found : x.state.validators.data[i]? with
  | none => simp [intervalGain_initial, found]
  | some v =>
    cases active : isActiveValidator v (getCurrentEpoch x.state) <;>
      simp [intervalGain_initial, found, active]

private theorem intervalGain_initial_subset (x y : ForkedBeaconState preset)
    (early : x.fork < .glamsterdam) :
    (∑ i ∈ intervalGain_indices y, intervalGain_initial x i) ≤
      activationCarry x + initialExcess x := by
  rw [← intervalGain_initial_sum x early]
  apply Finset.sum_le_sum_of_ne_zero
  intro i _ nonzero
  apply Finset.mem_range.mpr
  by_contra outside
  have absent : x.state.validators.data[i]? = none := Array.getElem?_eq_none_iff.mpr (by omega)
  simp [intervalGain_initial, absent] at nonzero

private theorem intervalGain_replay_bound {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (early : y.fork < .glamsterdam)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    referenceGain x y ≤ activationCarry x + initialExcess x +
      (events.map fun e => ∑ i ∈ intervalGain_indices y,
        (actualBalanceAt e.after i - actualBalanceAt e.before i)).sum := by
  have gain := intervalGain_path_bound shared tail genesis twoSlots early
  have initial := intervalGain_initial_subset x y
    (Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early)
  -- Keep the endpoint support restriction when replacing path credits by replay credits.
  have covered : (∑ i ∈ intervalGain_indices y, pathCredits i tail.balancePath) ≤
      ∑ i ∈ intervalGain_indices y,
        (events.map fun e => actualBalanceAt e.after i - actualBalanceAt e.before i).sum := by
    apply Finset.sum_le_sum
    intro i _
    exact coverage_run tail early high endEpoch replayed false i
  have exchange : (∑ i ∈ intervalGain_indices y,
      (events.map fun e => actualBalanceAt e.after i - actualBalanceAt e.before i).sum) =
      (events.map fun e => ∑ i ∈ intervalGain_indices y,
        (actualBalanceAt e.after i - actualBalanceAt e.before i)).sum := by
    clear replayed covered
    induction events with
    | nil => simp
    | cons e rest ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
  rw [exchange] at covered
  omega

private theorem intervalGain_selected_deposit (y : ForkedBeaconState preset)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (e : BalanceEvent preset)
    (kept : RegistryLifecycle e.before.state y.state)
    (ordered : ExitsOrdered e.before.state)
    (later : (getCurrentEpoch e.before.state).toNat < (getCurrentEpoch y.state).toNat)
    (matched : BalancesMatch e.after.state) :
    (∑ i ∈ intervalGain_indices y, (actualBalanceAt e.after i - actualBalanceAt e.before i)) ≤
      ∑ i ∈ Finset.range e.after.state.validators.data.size,
        if (e.before.state.validators.data[i]?.map (fun v =>
            decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch e.before.state).toNat))).getD
            false then 0 else actualBalanceAt e.after i - actualBalanceAt e.before i := by
  have selected (i) (member : i ∈ intervalGain_indices y) :
      (e.before.state.validators.data[i]?.map (fun v =>
        decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch e.before.state).toNat))).getD
          false = false := by
    cases found : e.before.state.validators.data[i]? with
    | none => rfl
    | some v =>
      obtain ⟨w, after, recent⟩ := (Finset.mem_filter.mp member).2
      have notWithdrawn := intervalGain_recent_not_withdrawn kept twoSlots ordered i v w
        found after later recent
      simp only [Option.map_some, Option.getD_some, decide_eq_false_iff_not]
      omega
  calc
    _ = ∑ i ∈ intervalGain_indices y,
        if (e.before.state.validators.data[i]?.map (fun v =>
            decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch e.before.state).toNat))).getD
            false then 0 else actualBalanceAt e.after i - actualBalanceAt e.before i := by
      apply Finset.sum_congr rfl
      intro i member
      simp only [selected i member, Bool.false_eq_true, ↓reduceIte]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_ne_zero
      intro i _ nonzero
      apply Finset.mem_range.mpr
      by_contra outside
      have absent : e.after.state.balances.data[i]? = none :=
        Array.getElem?_eq_none_iff.mpr (by dsimp [BalancesMatch] at matched; omega)
      simp only [actualBalanceAt, absent, Option.map_none, Option.getD_none, Nat.zero_sub,
        ite_self] at nonzero
      exact nonzero rfl

private theorem intervalGain_event_credit (y : ForkedBeaconState preset)
    (e : BalanceEvent preset) (bounded : e.credits ≤ e.creditLimit) :
    (∑ i ∈ intervalGain_indices y, (actualBalanceAt e.after i - actualBalanceAt e.before i)) ≤
      e.creditLimit := by
  apply le_trans (b := e.credits) _ bounded
  unfold BalanceEvent.credits
  apply Finset.sum_le_sum_of_ne_zero
  intro i _ nonzero
  apply Finset.mem_range.mpr
  by_contra outside
  have absent : e.after.state.balances.data[i]? = none :=
    Array.getElem?_eq_none_iff.mpr (by omega)
  simp [actualBalanceAt, absent] at nonzero

private theorem intervalGain_residual_other (x : ForkedBeaconState preset) (high : Nat)
    (e : BalanceEvent preset) (other : e.source ≠ .deposits) :
    residualCredit (config := config) x high e = e.creditLimit := by
  cases source : e.source <;> simp_all [residualCredit]

private theorem intervalGain_residual_deposit (x : ForkedBeaconState preset) (high : Nat)
    (e : BalanceEvent preset) (deposit : e.source = .deposits) :
    residualCredit (config := config) x high e =
      if .pectra ≤ e.before.fork then 0 else
        if high + 1 < config.ELECTRA_FORK_EPOCH.toNat then
          ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
            actualBalanceAt e.after i.toNat - actualBalanceAt e.before i.toNat).sum
        else e.creditLimit := by
  simp only [residualCredit, deposit]

private theorem intervalGain_preupgrade_credit (x y : ForkedBeaconState preset) (high : Nat)
    (e : BalanceEvent preset) (deposit : e.source = .deposits)
    (before : e.before.fork < .pectra)
    (crossing : config.ELECTRA_FORK_EPOCH.toNat ≤ high + 1)
    (bounded : e.credits ≤ e.creditLimit) :
    (∑ i ∈ intervalGain_indices y, (actualBalanceAt e.after i - actualBalanceAt e.before i)) ≤
      residualCredit (config := config) x high e := by
  rw [intervalGain_residual_deposit x high e deposit]
  have notElectra : ¬ Fork.pectra ≤ e.before.fork := Nat.not_le.mpr before
  have notBefore : ¬ high + 1 < config.ELECTRA_FORK_EPOCH.toNat := by omega
  simp only [notElectra, notBefore, ↓reduceIte]
  exact intervalGain_event_credit y e bounded

private theorem intervalGain_crossing_sources (x y : ForkedBeaconState preset) (high : Nat)
    (events : List (BalanceEvent preset))
    (crossing : config.ELECTRA_FORK_EPOCH.toNat ≤ high + 1)
    (bounded : ∀ e ∈ events, e.credits ≤ e.creditLimit)
    (depositBudget : Nat)
    (deposits : (events.map fun e =>
      if e.source = .deposits ∧ .pectra ≤ e.before.fork then
        ∑ i ∈ intervalGain_indices y, (actualBalanceAt e.after i - actualBalanceAt e.before i)
      else 0).sum ≤ depositBudget) :
    (events.map fun e => ∑ i ∈ intervalGain_indices y,
      (actualBalanceAt e.after i - actualBalanceAt e.before i)).sum ≤
      depositBudget + (events.map (residualCredit (config := config) x high)).sum := by
  have pointwise : ∀ e ∈ events,
      (∑ i ∈ intervalGain_indices y,
        (actualBalanceAt e.after i - actualBalanceAt e.before i)) ≤
      (if e.source = .deposits ∧ .pectra ≤ e.before.fork then
        ∑ i ∈ intervalGain_indices y, (actualBalanceAt e.after i - actualBalanceAt e.before i)
      else 0) + residualCredit (config := config) x high e := by
    intro e member
    by_cases deposit : e.source = .deposits
    · by_cases electra : .pectra ≤ e.before.fork
      · simp only [deposit, electra, and_self, ↓reduceIte]
        omega
      · simp only [deposit, electra, and_false, ↓reduceIte, Nat.zero_add]
        exact intervalGain_preupgrade_credit x y high e deposit (Nat.lt_of_not_le electra) crossing
          (bounded e member)
    · simp only [deposit, false_and, ↓reduceIte, Nat.zero_add]
      rw [intervalGain_residual_other x high e deposit]
      exact intervalGain_event_credit y e (bounded e member)
  have sum := List.sum_le_sum pointwise
  rw [List.sum_map_add] at sum
  omega

private theorem intervalGain_crossing_endpoint {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (early : y.fork < .glamsterdam)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events)
    (crossing : config.ELECTRA_FORK_EPOCH.toNat ≤ high + 1)
    (bounded : ∀ e ∈ events, e.credits ≤ e.creditLimit)
    (deposits : (events.map fun e =>
      if e.source = .deposits ∧ .pectra ≤ e.before.fork then
        ∑ i ∈ intervalGain_indices y, (actualBalanceAt e.after i - actualBalanceAt e.before i)
      else 0).sum ≤ depositWindow (config := config) x high) :
    referenceGain x y ≤ activationWindow (config := config) x high + initialExcess x +
      (events.map (residualCredit (config := config) x high)).sum := by
  have gain := intervalGain_replay_bound shared tail genesis twoSlots early high endEpoch
    events replayed
  have sources := intervalGain_crossing_sources x y high events crossing bounded
    (depositWindow (config := config) x high) deposits
  unfold activationWindow
  omega

private theorem intervalGain_deposit_filter_sum (y : ForkedBeaconState preset)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (events : List (BalanceEvent preset))
    (sites : ∀ e ∈ events, e.source = .deposits → .pectra ≤ e.before.fork →
      (∀ i, actualBalanceAt e.after i ≤ actualBalanceAt e.before i) ∨
      (RegistryLifecycle e.before.state y.state ∧ ExitsOrdered e.before.state ∧
        (getCurrentEpoch e.before.state).toNat < (getCurrentEpoch y.state).toNat ∧
        BalancesMatch e.after.state)) :
    (events.map fun e => if e.source = .deposits ∧ .pectra ≤ e.before.fork then
      ∑ i ∈ intervalGain_indices y, (actualBalanceAt e.after i - actualBalanceAt e.before i)
      else 0).sum ≤
    (events.map fun e => if e.source = .deposits ∧ .pectra ≤ e.before.fork then
      ∑ i ∈ Finset.range e.after.state.validators.data.size,
        if (e.before.state.validators.data[i]?.map (fun v =>
          decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch e.before.state).toNat))).getD
          false then 0 else actualBalanceAt e.after i - actualBalanceAt e.before i
      else 0).sum := by
  apply List.sum_le_sum
  intro e member
  split
  · rename_i selected
    rcases sites e member selected.1 selected.2 with zero | ⟨kept, ordered, later, matched⟩
    · simp only [Nat.sub_eq_zero_of_le (zero _), Finset.sum_const_zero, Nat.zero_le]
    · exact intervalGain_selected_deposit y twoSlots e kept ordered later matched
  · exact Nat.le_refl _

private theorem intervalGain_deposit_sites {x y : ForkedBeaconState preset}
    (events : List (BalanceEvent preset))
    (provenance : ∀ e ∈ events,
      RegistryLifecycle x.state e.before.state ∧
      RegistryLifecycle e.before.state e.after.state ∧
      RegistryLifecycle e.after.state y.state ∧
      ExitsOrdered e.before.state ∧ BalancesMatch e.after.state ∧
      (getCurrentEpoch x.state).toNat ≤ (getCurrentEpoch e.before.state).toNat ∧
      (getCurrentEpoch e.before.state).toNat ≤ (getCurrentEpoch y.state).toNat)
    (epochs : ∀ e ∈ events, e.source = .deposits → .pectra ≤ e.before.fork →
      (∀ i, actualBalanceAt e.after i ≤ actualBalanceAt e.before i) ∨
      (getCurrentEpoch e.before.state).toNat < (getCurrentEpoch y.state).toNat) :
    ∀ e ∈ events, e.source = .deposits → .pectra ≤ e.before.fork →
      (∀ i, actualBalanceAt e.after i ≤ actualBalanceAt e.before i) ∨
      (RegistryLifecycle e.before.state y.state ∧ ExitsOrdered e.before.state ∧
        (getCurrentEpoch e.before.state).toNat < (getCurrentEpoch y.state).toNat ∧
        BalancesMatch e.after.state) := by
  intro e member deposit electra
  rcases epochs e member deposit electra with zero | later
  · exact Or.inl zero
  · obtain ⟨_, first, last, ordered, matched, _⟩ := provenance e member
    exact Or.inr ⟨first.trans last, ordered, later, matched⟩

private theorem intervalGain_events_bounded {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    EventsBounded events := by
  have invariant {z : ForkedBeaconState preset} (run : Run config checks g z) :
      Invariant z.state := by
    induction run with
    | nil =>
      obtain ⟨_, _, _, ok⟩ := genesis
      exact (initializeBeaconStateFromEth1_invariant ok).2
    | snoc pre step ih =>
      cases step with
      | slot ok => exact (advanceSlotAcross_invariant ih ok).1
      | block engine signed due ok =>
        exact (frame_processBlock (applySignedBlock_ok ok).2.1).invariant ih
  induction tail generalizing events with
  | nil => cases replayed; simp [EventsBounded]
  | @snoc middle last pre step ih =>
    have selected := (coverage_step_epoch step).trans endEpoch
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    simp only [selected, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
    obtain ⟨added, addedOk, rfl⟩ := rest
    have previous := ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early) selected prior priorOk
    obtain ⟨actual, actualOk, bound⟩ := stepBalanceEvents_bounded step
      (invariant (shared.append pre)).balancesMatch early
    cases Except.ok.inj (actualOk.symm.trans addedOk)
    exact eventsBounded_append previous bound

private theorem intervalGain_crossing_of_interfaces {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (early : y.fork < .glamsterdam)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events)
    (crossing : config.ELECTRA_FORK_EPOCH.toNat ≤ high + 1) :
    referenceGain x y ≤ activationWindow (config := config) x high + initialExcess x +
      (events.map (residualCredit (config := config) x high)).sum := by
  apply intervalGain_crossing_endpoint shared tail genesis twoSlots early high endEpoch
    events replayed crossing (fun e member =>
      (intervalGain_events_bounded shared tail genesis early high endEpoch
        events replayed e member).1)
  exact (intervalGain_deposit_filter_sum y twoSlots events
    (intervalGain_deposit_sites events
      (replay_event_provenance shared tail genesis early high endEpoch events replayed)
      (replay_electra_deposit_epoch shared tail genesis early high endEpoch
        events replayed))).trans
      (funding_deposit_capacity shared tail genesis early high endEpoch events replayed)

private theorem intervalGain_joining_split {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (newBound carryBound : Nat)
    (newKeys : Models.stake (effectiveWeight y.state)
      (recentKeys y.state \ recentKeys x.state) ≤ newBound)
    (oldKeys : Models.stake (effectiveWeight y.state)
      ((recentKeys y.state ∩ recentKeys x.state) \ activeKeys x.state) ≤ carryBound) :
    Models.stake (effectiveWeight y.state) (recentKeys y.state \ activeKeys x.state) ≤
      newBound + carryBound := by
  -- A key recent now and active at the reference was unslashed there, so recent there too.
  have active : ∀ k ∈ recentKeys y.state, k ∈ activeKeys x.state → k ∈ recentKeys x.state := by
    intro k recent member
    unfold recentKeys at recent ⊢
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ member, fun slashed =>
      (Finset.mem_filter.mp recent).2 (slashedAt_forward tail slashed)⟩
  have partition : recentKeys y.state \ activeKeys x.state =
      (recentKeys y.state \ recentKeys x.state) ∪
        ((recentKeys y.state ∩ recentKeys x.state) \ activeKeys x.state) := by
    ext k
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro ⟨recent, inactive⟩
      by_cases old : k ∈ recentKeys x.state
      · exact Or.inr ⟨⟨recent, old⟩, inactive⟩
      · exact Or.inl ⟨recent, old⟩
    · rintro (⟨recent, fresh⟩ | ⟨⟨recent, _⟩, inactive⟩)
      · exact ⟨recent, fun h => fresh (active k recent h)⟩
      · exact ⟨recent, inactive⟩
  have disjoint : Disjoint (recentKeys y.state \ recentKeys x.state)
      ((recentKeys y.state ∩ recentKeys x.state) \ activeKeys x.state) := by
    apply Finset.disjoint_left.mpr
    intro k first last
    exact (Finset.mem_sdiff.mp first).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp last).1).2
  unfold Models.stake at *
  rw [partition, Finset.sum_union disjoint]
  exact Nat.add_le_add newKeys oldKeys

/-- The reference gain splits into the gains of reference-active keys and the joining stake.

It is an inequality over the unslashed recent keys.

A recent key is unslashed now, so by forward persistence it was unslashed at the reference. -/
private theorem intervalGain_reference_partition {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) :
    referenceGain x y ≤ gaining x y +
      Models.stake (effectiveWeight y.state) (recentKeys y.state \ activeKeys x.state) := by
  classical
  have partition : recentKeys y.state =
      (recentKeys y.state ∩ activeKeys x.state) ∪
        (recentKeys y.state \ activeKeys x.state) := by
    ext k
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have disjoint : Disjoint (recentKeys y.state ∩ activeKeys x.state)
      (recentKeys y.state \ activeKeys x.state) := by
    apply Finset.disjoint_left.mpr
    intro k first last
    exact (Finset.mem_sdiff.mp last).2 (Finset.mem_inter.mp first).2
  unfold referenceGain
  conv_lhs => rw [partition, Finset.sum_union disjoint]
  apply Nat.add_le_add
  · unfold gaining
    rw [Finset.inter_comm]
    apply Finset.sum_le_sum
    intro k member
    obtain ⟨active, recent⟩ := Finset.mem_inter.mp member
    unfold recentKeys at recent
    have unslashedX : ¬ SlashedAt x.state k := fun slashed =>
      (Finset.mem_filter.mp recent).2 (slashedAt_forward tail slashed)
    have reference : k ∈ unslashedKeys x.state := by
      unfold unslashedKeys
      exact Finset.mem_filter.mpr ⟨active, unslashedX⟩
    simp [Models.supported, reference]
  · unfold Models.stake
    apply Finset.sum_le_sum
    intro k member
    have absent : k ∉ unslashedKeys x.state := fun reference => (Finset.mem_sdiff.mp member).2
      (by unfold unslashedKeys at reference; exact (Finset.mem_filter.mp reference).1)
    simp [Models.supported, absent]

private theorem intervalGain_active_sum (x : ForkedBeaconState preset)
    (unique : PubkeysDistinct x.state) (early : x.fork < .glamsterdam)
    (f : Cryptography.Bls.BLSPubkey → Nat) :
    (∑ k ∈ activeKeys x.state, f k) =
      ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
        (x.state.validators.data[i.toNat]?.map fun v => f v.pubkey).getD 0).sum := by
  let indices := getActiveValidatorIndices x.state (getCurrentEpoch x.state)
  have within := x.state.validators.bound early
  have inside (i) (hi : i ∈ indices) : i.toNat < x.state.validators.data.size := by
    obtain ⟨v, found, _⟩ := (mem_getActiveValidatorIndices within).mp hi
    exact (Array.getElem?_eq_some_iff.mp found).1
  have nodup : indices.Nodup := by
    simpa [indices, List.Nodup] using
      (getActiveValidatorIndices_sorted within (getCurrentEpoch x.state)).imp UInt64.ne_of_lt
  rw [← List.sum_toFinset _ nodup]
  let key (i : ValidatorIndex) (hi : i ∈ indices.toFinset) :=
    (x.state.validators.data[i.toNat]'(inside i (List.mem_toFinset.mp hi))).pubkey
  symm
  apply Finset.sum_bij key
  · intro i hi
    simp only [activeKeys, keysAt, List.mem_toFinset, List.mem_filterMap]
    exact ⟨i, List.mem_toFinset.mp hi, by simp [key, inside i (List.mem_toFinset.mp hi)]⟩
  · intro i hi j hj same
    apply UInt64.toNat_inj.mp
    apply unique.eq_of_getElem_eq
      (by simpa [validatorKeys] using inside i (List.mem_toFinset.mp hi))
      (by simpa [validatorKeys] using inside j (List.mem_toFinset.mp hj))
    simpa [validatorKeys, key] using same
  · intro k hk
    simp only [activeKeys, keysAt, List.mem_toFinset, List.mem_filterMap] at hk
    obtain ⟨i, hi, found⟩ := hk
    exact ⟨i, List.mem_toFinset.mpr hi, by
      simpa [key, Array.getElem?_eq_getElem, inside i hi] using found⟩
  · intro i hi
    simp [key, inside i (List.mem_toFinset.mp hi)]

private theorem intervalGain_active_path {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .glamsterdam) :
    gaining x y ≤ initialExcess x +
      ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
        pathCredits i.toNat tail.balancePath).sum := by
  have uniqueX := shared.unique (genesis_unique genesis)
  have uniqueY := (shared.append tail).unique (genesis_unique genesis)
  have earlyX := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have allKeys : gaining x y ≤ ∑ k ∈ activeKeys x.state,
      (effectiveWeight y.state k - effectiveWeight x.state k) := by
    apply Finset.sum_le_sum_of_subset
    exact Finset.inter_subset_left
  apply allKeys.trans
  rw [intervalGain_active_sum x uniqueX earlyX]
  unfold initialExcess
  rw [← List.sum_map_add]
  apply List.sum_le_sum
  intro i member
  obtain ⟨v, before, _⟩ :=
    (mem_getActiveValidatorIndices (x.state.validators.bound earlyX)).mp member
  obtain ⟨w, after, key⟩ := tail.key_preserved i.toNat v before
  have first := effectiveWeight_at x.state uniqueX i.toNat v before
  have last := effectiveWeight_at y.state uniqueY i.toNat w after
  have gain := intervalGain_existing_funding tail early i.toNat
    (Array.getElem?_eq_some_iff.mp before).1
  simp only [before, Option.map_some, Option.getD_some]
  rw [first, ← key, last]
  have etaX : (⟨x.fork, x.state⟩ : ForkedBeaconState preset) = x := by cases x; rfl
  have etaY : (⟨y.fork, y.state⟩ : ForkedBeaconState preset) = y := by cases y; rfl
  rw [etaX, etaY]
  omega

private theorem intervalGain_active_replay {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    gaining x y ≤ initialExcess x +
      (events.map fun e =>
        ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
          actualBalanceAt e.after i.toNat - actualBalanceAt e.before i.toNat).sum).sum := by
  have gain := intervalGain_active_path shared tail genesis early
  have credits := List.sum_le_sum (l := getActiveValidatorIndices x.state (getCurrentEpoch x.state))
    (fun i _ => coverage_run tail early high endEpoch replayed false i.toNat)
  have exchange {α β : Type} (xs : List α) (ys : List β) (f : α → β → Nat) :
      (xs.map fun a => (ys.map (f a)).sum).sum =
        (ys.map fun b => (xs.map fun a => f a b).sum).sum := by
    induction xs with
    | nil => simp
    | cons a rest ih => simp only [List.map_cons, List.sum_cons, ih, List.sum_map_add]
  simp only [coveragePath, coverageDelta, Bool.false_eq_true, ↓reduceIte] at credits
  rw [exchange] at credits
  omega

private theorem intervalGain_active_event (x : ForkedBeaconState preset)
    (early : x.fork < .glamsterdam) (e : BalanceEvent preset)
    (bounded : e.credits ≤ e.creditLimit) :
    ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
      actualBalanceAt e.after i.toNat - actualBalanceAt e.before i.toNat).sum ≤ e.creditLimit := by
  let indices := getActiveValidatorIndices x.state (getCurrentEpoch x.state)
  have nodup : indices.Nodup := by
    simpa [indices, List.Nodup] using
      (getActiveValidatorIndices_sorted (x.state.validators.bound early)
        (getCurrentEpoch x.state)).imp UInt64.ne_of_lt
  rw [← List.sum_toFinset _ nodup]
  have injective : Function.Injective UInt64.toNat := fun _ _ h => UInt64.toNat_inj.mp h
  rw [← Finset.sum_image (f := fun i => actualBalanceAt e.after i - actualBalanceAt e.before i)
    (g := UInt64.toNat) (fun _ _ _ _ h => injective h)]
  apply le_trans (b := e.credits) _ bounded
  unfold BalanceEvent.credits
  apply Finset.sum_le_sum_of_ne_zero
  intro i _ nonzero
  apply Finset.mem_range.mpr
  by_contra outside
  have absent : e.after.state.balances.data[i]? = none :=
    Array.getElem?_eq_none_iff.mpr (by omega)
  simp [actualBalanceAt, absent] at nonzero

private theorem intervalGain_active_residual {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events)
    (before : ∀ e ∈ events, e.source = .deposits → e.before.fork < .pectra) :
    gaining x y ≤ initialExcess x +
      (events.map (residualCredit (config := config) x high)).sum := by
  apply (intervalGain_active_replay shared tail genesis early high endEpoch events replayed).trans
  apply Nat.add_le_add_left
  apply List.sum_le_sum
  intro e member
  have credit := intervalGain_active_event x
    (Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early) e
    (intervalGain_events_bounded shared tail genesis early high endEpoch events replayed e member).1
  by_cases deposit : e.source = .deposits
  · rw [intervalGain_residual_deposit x high e deposit]
    have notElectra : ¬ Fork.pectra ≤ e.before.fork := Nat.not_le.mpr (before e member deposit)
    rw [ite_eq_right notElectra]
    split
    · exact Nat.le_refl _
    · exact credit
  · rw [intervalGain_residual_other x high e deposit]
    exact credit

private theorem intervalGain_upgrade_epoch {s t : ForkedBeaconState preset}
    (ok : processUpgrades config checks s = .ok t)
    (initial : .pectra ≤ s.fork → config.ELECTRA_FORK_EPOCH.toNat ≤
      (getCurrentEpoch s.state).toNat) :
    .pectra ≤ t.fork → config.ELECTRA_FORK_EPOCH.toNat ≤
      (getCurrentEpoch t.state).toNat := by
  fun_induction processUpgrades config checks s generalizing t with
  | case1 s due ih =>
    obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
    apply ih next rest
    intro electra
    have slot := (upgradeFrame_upgradeNext nextOk).slot
    have epoch : getCurrentEpoch next.val.state = getCurrentEpoch s.state := by
      simp only [getCurrentEpoch, slot]
    rw [epoch]
    by_cases old : .pectra ≤ s.fork
    · exact initial old
    · obtain ⟨fork, state⟩ := s
      cases fork <;> simp only at old
      all_goals try (exact False.elim (old (by decide)))
      all_goals simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
        throw] at nextOk
      all_goals try contradiction
      all_goals try (obtain ⟨_, _, rfl⟩ := nextOk)
      all_goals try (exact False.elim (of_decide_eq_false rfl electra))
      simp only [upgradeDue, Config.nextFork, Option.any_some, Bool.and_eq_true,
        beq_iff_eq] at due
      have scheduled : getCurrentEpoch state = config.ELECTRA_FORK_EPOCH := by
        exact due.2
      rw [scheduled]
  | case2 s notDue => cases ok; exact initial

private theorem intervalGain_reachable_epoch {g y : ForkedBeaconState preset}
    (run : Run config checks g y) (genesis : Genesis (config := config) (checks := checks) g) :
    .pectra ≤ y.fork → config.ELECTRA_FORK_EPOCH.toNat ≤
      (getCurrentEpoch y.state).toNat := by
  induction run with
  | nil =>
    intro electra
    obtain ⟨hash, time, deposits, ok⟩ := genesis
    have altair : Fork.altair ≤ g.fork := Nat.le_trans (by decide) electra
    simp [initializeBeaconStateFromEth1, altair, throw] at ok
  | @snoc middle last pre step ih =>
    cases step with
    | slot ok =>
      obtain ⟨advanced, advanceOk, upgrades⟩ := bind_ok_iff.mp ok
      apply intervalGain_upgrade_epoch upgrades
      intro electra
      have previous := ih electra
      have moved := advanceSlot_slot advanceOk
      have epochs : (getCurrentEpoch middle.state).toNat ≤
          (getCurrentEpoch advanced).toNat := by
        simp only [getCurrentEpoch_toNat]
        exact Nat.div_le_div_right (by omega)
      exact previous.trans epochs
    | block engine signed due ok =>
      intro electra
      have previous := ih electra
      have slot := (frame_processBlock (applySignedBlock_ok ok).2.1).slot
      simpa only [getCurrentEpoch, slot] using previous

private theorem intervalGain_boundary_carry (x : ForkedBeaconState preset)
    (early : x.fork < .glamsterdam) (unique : PubkeysDistinct x.state) :
    boundaryStake x ≤ activationCarry x := by
  refine (boundaryStake_le_cohort x early unique).trans ?_
  let selected := fun v : Validator =>
    v.activationEpoch.toNat < (getCurrentEpoch x.state).toNat &&
      v.exitEpoch.toNat == (getCurrentEpoch x.state).toNat
  have filtered (vs : List Validator) :
      ((vs.filter selected).map (·.effectiveBalance.toNat)).sum =
        (vs.map fun v => if selected v then v.effectiveBalance.toNat else 0).sum := by
    induction vs with
    | nil => simp
    | cons v rest ih => cases h : selected v <;> simp [h, ih]
  have forget : (x.state.validators.data.toList.zipIdx.map fun (v, _) =>
      if selected v then v.effectiveBalance.toNat else 0) =
      x.state.validators.data.toList.map
        (fun v => if selected v then v.effectiveBalance.toNat else 0) := by
    exact (List.map_map (f := Prod.fst)
      (g := fun v => if selected v then v.effectiveBalance.toNat else 0)).symm.trans
        (congrArg (List.map _) (List.zipIdx_map_fst 0 _))
  unfold inheritedCohort activationCarry
  rw [← List.foldl_map (f := fun v : Validator => v.effectiveBalance.toNat)
    (g := fun n v => n + v), ← List.sum_eq_foldl, filtered, ← forget]
  apply List.sum_le_sum
  rintro ⟨v, i⟩ member
  have found : x.state.validators.data[i]? = some v := by
    simpa using List.mem_zipIdx_iff_getElem?.mp member
  by_cases cohort : selected v = true
  · have membership : v.activationEpoch.toNat < (getCurrentEpoch x.state).toNat ∧
        v.exitEpoch.toNat = (getCurrentEpoch x.state).toNat := by
      simpa [selected] using cohort
    obtain ⟨previous, inactive⟩ := (previous_only_iff_exit x.state v).mpr membership
    simp only [cohort, ↓reduceIte, inactive, Bool.false_eq_true, previous, Bool.true_or]
    simp [effectiveAt, found]
  · simp [cohort]

private theorem intervalGain_pre_electra_of_split {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (parameters : Parameters preset)
    (unique : PubkeysDistinct x.state)
    (early : y.fork < .pectra) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset))
    (splitBound :
      Models.stake (effectiveWeight y.state) (recentKeys y.state \ recentKeys x.state) ≤
        ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) *
          cohortCap config y.state.validators.data.size * preset.MAX_EFFECTIVE_BALANCE.toNat ∧
      Models.stake (effectiveWeight y.state)
        ((recentKeys y.state ∩ recentKeys x.state) \ activeKeys x.state) ≤ boundaryStake x)
    (gainBound : gaining x y ≤ initialExcess x +
      (events.map (residualCredit (config := config) x high)).sum) :
    referenceGain x y ≤ activationWindow (config := config) x high + initialExcess x +
      (events.map (residualCredit (config := config) x high)).sum := by
  have joined := intervalGain_joining_split tail _ _ splitBound.1 splitBound.2
  have before : x.fork < .pectra :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have carryBound := intervalGain_boundary_carry x (Nat.lt_trans before (by decide)) unique
  have registry := registry_le_window tail (Nat.lt_trans early (by decide)) high endEpoch
    (by have := parameters.slots; omega)
  have count : cohortCap config y.state.validators.data.size ≤
      cohortCap config (registryWindow x high) :=
    max_le_max_left _ (Nat.div_le_div_right registry)
  have horizon : (getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat ≤
      driftHorizon x high := by unfold driftHorizon; omega
  have countBound := Nat.mul_le_mul_right preset.MAX_EFFECTIVE_BALANCE.toNat
    (Nat.mul_le_mul horizon count)
  refine (intervalGain_reference_partition tail).trans ?_
  unfold activationWindow
  rw [ite_eq_left before]
  omega

/-- Funding churn bounds Electra deposits that can contribute to recent voting stake.

Withdrawn-key exceptions do not reactivate an exited validator and contribute no such stake. -/
private theorem gains_and_activations_over_interval {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (caps : CapOrder preset)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    referenceGain x y ≤
      activationWindow (config := config) x high + initialExcess x +
        (events.map (residualCredit (config := config) x high)).sum := by
  by_cases crossing : config.ELECTRA_FORK_EPOCH.toNat ≤ high + 1
  · exact intervalGain_crossing_of_interfaces shared tail genesis twoSlots early high
      endEpoch events replayed crossing
  · have before : y.fork < .pectra := by
      apply Nat.lt_of_not_le
      intro electra
      have scheduled := intervalGain_reachable_epoch (shared.append tail) genesis electra
      omega
    apply intervalGain_pre_electra_of_split tail parameters
      (shared.unique (genesis_unique genesis)) before high endEpoch events
      (joining_before_electra_split shared tail genesis twoSlots caps before)
    apply intervalGain_active_residual shared tail genesis early high endEpoch events replayed
    intro e member _
    exact Nat.lt_of_le_of_lt
      (replay_event_fork_le shared tail genesis early high endEpoch events replayed e member) before

/-- A conservative source envelope, separate from the exact observed-state drift.

The boundary term is supplied by boundaryWindow, not by the cumulative exit envelope.

Queue, registry and rounding bounds still need tighter transition proofs. -/
def sourceDrift (x : ForkedBeaconState preset) (high boundary : Nat)
    (events : List (BalanceEvent preset)) : Nat :=
  2 * (exitWindow (config := config) x high events + lossCorrection x events) +
    activationWindow (config := config) x high + initialExcess x +
    (events.map (residualCredit (config := config) x high)).sum + 2 * boundary

/-- Extending a replay prefix and its boundary budget cannot shrink the source envelope. -/
private theorem sourceDrift_le_of_prefix (x : ForkedBeaconState preset) (high : Nat)
    {before after : List (BalanceEvent preset)} (initial : before <+: after)
    {first last : Nat} (boundary : first ≤ last) :
    sourceDrift (config := config) x high first before ≤
      sourceDrift (config := config) x high last after := by
  have sums (f : BalanceEvent preset → Nat) : (before.map f).sum ≤ (after.map f).sum := by
    obtain ⟨rest, rfl⟩ := initial
    simp only [List.map_append, List.sum_append]
    omega
  have loss : lossCorrection x before ≤ lossCorrection x after := by
    apply List.sum_le_sum
    intro i _
    cases found : x.state.validators.data[i.toNat]? with
    | none => simp
    | some v =>
      cases slashed : v.slashed with
      | true => simp [slashed]
      | false =>
        simp only [slashed, Bool.false_eq_true, ↓reduceIte]
        have monotone := sums (referenceDebit i.toNat)
        split <;> split <;> omega
  have active : activeStakeWindow (config := config) x high before ≤
      activeStakeWindow (config := config) x high after := by
    unfold activeStakeWindow
    split
    · have monotone := sums fundingCredit
      omega
    · exact Nat.le_refl _
  have rates : consolidationRate (preset := preset) (config := config)
      (activeStakeWindow (config := config) x high before) ≤
      consolidationRate (preset := preset) (config := config)
        (activeStakeWindow (config := config) x high after) :=
    Nat.sub_le_sub_right (max_le_max_left _
      (Nat.div_le_div_right (max_le_max_left _ active))) _
  have exits : exitWindow (config := config) x high before ≤
      exitWindow (config := config) x high after := by
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_left rates _)) _
  have credits := sums (residualCredit (config := config) x high)
  unfold sourceDrift
  omega

/-- The source envelope is a derived upper bound, not the definition of the safety loss. -/
theorem derivedDrift_le_sources {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset)
    (early : y.fork < .glamsterdam) (high : Nat)
    (startEpoch : (getCurrentEpoch x.state).toNat ≤ high + 1) :
    ∃ events, tail.balanceEvents high = .ok events ∧
      derivedDrift high tail ≤
        sourceDrift (config := config) x high (boundaryWindow high tail) events := by
  obtain ⟨events, replayed, bounds⟩ :=
    source_bounds_over_interval shared tail genesis early high
  clear bounds
  refine ⟨events, replayed, ?_⟩
  have atState {y : ForkedBeaconState preset} (run : Run config checks x y)
      (early : y.fork < .glamsterdam)
      (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
      (events : List (BalanceEvent preset)) (replayed : run.balanceEvents high = .ok events) :
      stateDrift x y ≤ sourceDrift (config := config) x high (boundaryStake y) events := by
    have losses := nonaccountable_losses_over_interval shared run genesis parameters caps
      aligned early high within events replayed
    have gains := gains_and_activations_over_interval shared run genesis parameters twoSlots caps
      early high within events replayed
    unfold stateDrift sourceDrift
    omega
  induction tail generalizing events with
  | nil => exact atState .nil early startEpoch events replayed
  | @snoc middle last pre step ih =>
    have beforeFork : middle.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt step.chainStep.fork_le early
    obtain ⟨prior, priorOk, initial⟩ := pre.balanceEvents_prefix
      (Run.nil.snoc step) high events replayed
    have before := ih beforeFork prior priorOk
    have budget := sourceDrift_le_of_prefix (config := config) x high initial
      (first := boundaryWindow high pre) (last := boundaryWindow high (pre.snoc step))
      (by simp only [boundaryWindow]; split <;> omega)
    have past := Nat.le_trans before budget
    simp only [derivedDrift, boundaryWindow]
    split
    · rename_i within
      simp only [boundaryWindow, within, ↓reduceIte] at past
      have current := atState (pre.snoc step) early within events replayed
      have enlarged := sourceDrift_le_of_prefix (config := config) x high
        (List.prefix_refl events) (Nat.le_max_right (boundaryWindow high pre) (boundaryStake last))
      exact max_le past (current.trans enlarged)
    · rename_i beyond
      simpa only [boundaryWindow, beyond, ↓reduceIte] using past

end

end EthLib.Consensus.DirectSafety
