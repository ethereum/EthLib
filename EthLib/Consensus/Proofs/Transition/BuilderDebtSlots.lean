module

public import EthLib.Consensus.Proofs.Transition.BuilderDebtEpoch
public import EthLib.Consensus.Proofs.Transition.Invariants

/-!
# Proofs: slots keep the builder debt invariant

A slot caches the roots of the state and of the latest block.

From Gloas it also marks the next payload as not yet available.

None of this touches the builders, their payments, their withdrawals or the latest bid.

It keeps the slot and the slot of the latest block too, which place the parent payment.

The last slot of an epoch runs the epoch transition.

Each of its steps keeps those fields, except the step of the builder payments.

That step, with the move to the next slot, keeps the invariant under a positive quorum.

So every slot keeps the invariant, and so does a run of slots.

[EIP-7732] adds the builders and the epoch step of their payments.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#state-transition
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-! ## The steps that keep the builder fields -/

/-- Setting a validator keeps the builder fields and the two slots. -/
theorem builderFrame_setValidator {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after) : BuilderFrame state after := by
  obtain ⟨_, rfl⟩ := setValidator_ok set
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Setting a balance keeps the builder fields and the two slots. -/
theorem builderFrame_setBalance {index : ValidatorIndex} {balance : Gwei}
    (set : state.setBalance index balance = .ok after) : BuilderFrame state after := by
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Raising a balance keeps the builder fields and the two slots. -/
theorem builderFrame_increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : BuilderFrame state after :=
  let ⟨_, set⟩ := increaseBalance_ok computed
  builderFrame_setBalance set

/-- Lowering a balance keeps the builder fields and the two slots. -/
theorem builderFrame_decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : BuilderFrame state after :=
  let ⟨_, set⟩ := decreaseBalance_ok computed
  builderFrame_setBalance set

/-- Starting the exit of a validator keeps the builder fields and the two slots. -/
theorem builderFrame_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) :
    BuilderFrame state after := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok computed
  · exact BuilderFrame.refl _
  refine BuilderFrame.trans ?_ (builderFrame_setValidator set)
  unfold exitQueue at queue
  split at queue
  · simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at queue
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := queue
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at queue
    obtain ⟨_, _, rfl, _⟩ := queue
    exact BuilderFrame.refl _

/-! ## The steps of an epoch before the builder payments -/

private theorem builderFrame_processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) :
    BuilderFrame state after := by
  obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · exact BuilderFrame.refl _
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    exact ⟨by rw [← rest], by rw [← rest], by rw [← rest], by rw [← rest], by rw [← rest],
      by rw [← rest]⟩

private theorem builderFrame_processInactivityUpdates {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) :
    BuilderFrame state after := by
  unfold processInactivityUpdates at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ BuilderFrame.refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem builderFrame_applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (computed : applyAllDeltas state deltas = .ok after) : BuilderFrame state after :=
  BuilderFrame.foldlM (fun _ _ _ ok => by
    simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, lowered⟩ := ok
    exact (builderFrame_increaseBalance raised).trans (builderFrame_decreaseBalance lowered))
    computed

private theorem builderFrame_processRewardsAndPenalties
    (computed : processRewardsAndPenalties config state = .ok after) :
    BuilderFrame state after := by
  unfold processRewardsAndPenalties at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ BuilderFrame.refl _
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact BuilderFrame.foldlM (fun _ _ _ ok => builderFrame_applyAllDeltas ok) applied
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact builderFrame_applyAllDeltas applied

private theorem builderFrame_processRegistryUpdates
    (computed : processRegistryUpdates config state = .ok after) : BuilderFrame state after := by
  unfold processRegistryUpdates at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, computed⟩ := computed
    refine BuilderFrame.foldlM (fun _ _ _ ok => ?_) computed
    simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, set⟩ := ok
      exact builderFrame_setValidator set
    split at ok
    · exact builderFrame_initiateValidatorExit (liftAccessor_ok.mp ok)
    split at ok
    · exact builderFrame_setValidator (liftAccessor_ok.mp ok)
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ BuilderFrame.refl _
  simp only [bind_ok_iff] at computed
  obtain ⟨_, updatedOk, activated⟩ := computed
  refine (BuilderFrame.foldlM (fun _ _ _ ok => ?_) updatedOk).trans
    (BuilderFrame.foldlM (fun _ _ _ ok => ?_) activated)
  · simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, _, markedOk, ok⟩ := ok
    have set := builderFrame_setValidator markedOk
    split at ok
    · exact set.trans (builderFrame_initiateValidatorExit (liftAccessor_ok.mp ok))
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ set
  · simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, set⟩ := ok
    exact builderFrame_setValidator set

private theorem builderFrame_processSlashings (computed : processSlashings state = .ok after) :
    BuilderFrame state after := by
  unfold processSlashings at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    refine BuilderFrame.foldlM (fun _ _ _ ok => ?_) applied
    simp only [applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, lowered⟩ := ok
        exact builderFrame_decreaseBalance lowered
      · simp only [pure, Except.pure, Except.ok.injEq] at ok
        exact ok ▸ BuilderFrame.refl _
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ BuilderFrame.refl _
  · refine BuilderFrame.foldlM (fun _ _ _ ok => ?_) computed
    simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, _, _, lowered⟩ := ok
        exact builderFrame_decreaseBalance lowered
      · simp only [pure, Except.pure, Except.ok.injEq] at ok
        exact ok ▸ BuilderFrame.refl _
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ BuilderFrame.refl _

private theorem builderFrame_processEth1DataReset {before : fork < .hegota}
    (computed : processEth1DataReset before state = .ok after) : BuilderFrame state after := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ BuilderFrame.refl _

/-- Adding a validator keeps the builder fields and the two slots. -/
theorem builderFrame_addValidatorToRegistry {pubkey withdrawalCredentials amount}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    BuilderFrame state after := by
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  split at computed
  · cases computed
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases computed

/-- Applying a pending deposit keeps the builder fields and the two slots. -/
theorem builderFrame_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    BuilderFrame state after := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact BuilderFrame.refl _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact builderFrame_addValidatorToRegistry computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ BuilderFrame.refl _
  · rw [liftAccessor_ok] at computed
    exact builderFrame_increaseBalance computed

private theorem builderFrame_passPendingDeposits {stop : PendingDeposit → Bool}
    {nextEpoch : Epoch} {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      BuilderFrame state pass.1.state
  | [], _, _, _, _, _, computed => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact BuilderFrame.refl _
  | deposit :: rest, state, processed, count, postponed, pass, computed => by
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      exact BuilderFrame.refl _
    split at computed
    · split at computed
      · cases computed
      rename_i credited
      split at computed
      · cases computed
      cases computed
      exact (builderFrame_applyPendingDeposit credited).trans
        (builderFrame_passPendingDeposits (deposits := rest) ‹_›)
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact builderFrame_passPendingDeposits (deposits := rest) ‹_›
    split at computed
    · cases computed
    split at computed
    · cases computed
      exact BuilderFrame.refl _
    split at computed
    · cases computed
    rename_i credited
    split at computed
    · cases computed
    cases computed
    exact (builderFrame_applyPendingDeposit credited).trans
      (builderFrame_passPendingDeposits (deposits := rest) ‹_›)

private theorem builderFrame_passPendingConsolidations {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      BuilderFrame state result.1
  | [], _, _, computed => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact BuilderFrame.refl _
  | consolidation :: rest, state, result, computed => by
    simp only [passPendingConsolidations, bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨source, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨⟨passed, read⟩, passedOk, computed⟩ := computed
      cases computed
      exact builderFrame_passPendingConsolidations (result := (passed, read)) passedOk
    split at computed
    · cases computed
      exact BuilderFrame.refl _
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, lowered, loweredOk, raised, raisedOk, ⟨passed, read⟩, passedOk, computed⟩ :=
      computed
    cases computed
    exact ((builderFrame_decreaseBalance loweredOk).trans
      (builderFrame_increaseBalance raisedOk)).trans
      (builderFrame_passPendingConsolidations (result := (passed, read)) passedOk)

private theorem builderFrame_processPendingBalances
    (computed : processPendingBalances config checks state = .ok after) :
    BuilderFrame state after := by
  unfold processPendingBalances at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, deposited, consolidated⟩ := computed
    refine BuilderFrame.trans (second := ‹_›) ?_ ?_
    · unfold processPendingDeposits at deposited
      simp only [bind, Except.bind, pure, Except.pure] at deposited
      repeat' (split at deposited <;> try cases deposited)
      all_goals
        exact (builderFrame_passPendingDeposits ‹_›).trans ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · unfold processPendingConsolidations at consolidated
      simp only [bind, Except.bind, pure, Except.pure] at consolidated
      repeat' (split at consolidated <;> try cases consolidated)
      all_goals
        exact (builderFrame_passPendingConsolidations ‹_›).trans ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ BuilderFrame.refl _

/-! ## The steps of an epoch after the builder payments -/

private theorem builderFrame_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) : BuilderFrame state after := by
  unfold processEffectiveBalanceUpdates at computed
  refine BuilderFrame.foldlM (fun _ _ _ ok => ?_) computed
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, set⟩ := ok
  exact builderFrame_setValidator set

private theorem builderFrame_processHistoricalSummariesUpdate {capella : .shapella ≤ fork}
    (computed : processHistoricalSummariesUpdate state capella = .ok after) :
    BuilderFrame state after := by
  unfold processHistoricalSummariesUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals first
    | exact BuilderFrame.refl _
    | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem builderFrame_processSyncCommitteeUpdates {altair : .altair ≤ fork}
    (computed : processSyncCommitteeUpdates state altair = .ok after) :
    BuilderFrame state after := by
  unfold processSyncCommitteeUpdates at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals first
    | exact BuilderFrame.refl _
    | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem builderFrame_processSlashingsReset
    (computed : processSlashingsReset state = .ok after) : BuilderFrame state after := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq computed
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem builderFrame_processRandaoMixesReset
    (computed : processRandaoMixesReset state = .ok after) : BuilderFrame state after := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq computed
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem builderFrame_processProposerLookahead {fulu : .fusaka ≤ fork}
    (computed : processProposerLookahead state fulu = .ok after) : BuilderFrame state after := by
  simp only [processProposerLookahead, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem builderFrame_processPtcWindow {gloas : .glamsterdam ≤ fork}
    (computed : processPtcWindow state gloas = .ok after) : BuilderFrame state after := by
  simp only [processPtcWindow, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- From Gloas, the epoch transition keeps the builder fields, except the step of the payments. -/
private theorem processEpoch_builderSplit {gloas : .glamsterdam ≤ fork}
    (computed : processEpoch config checks state = .ok after) :
    ∃ pending paid, BuilderFrame state pending ∧
      processBuilderPendingPayments pending gloas = .ok paid ∧ BuilderFrame paid after := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) gloas
  have capella : .shapella ≤ fork := Nat.le_trans (by decide) gloas
  have fulu : .fusaka ≤ fork := Nat.le_trans (by decide) gloas
  unfold processEpoch processEpochAltair at computed
  simp only [bind_ok_iff, altair, capella, fulu, gloas, ↓reduceDIte, liftAccessor_ok] at computed
  obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
    registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk, balanced,
    balancedOk, cleared, clearedOk, mixed, mixedOk, rooted, rootedOk, synced, syncedOk, looked,
    lookedOk, windowed⟩ := computed
  have resetFrame : BuilderFrame slashed reset := by
    split at resetOk
    · exact builderFrame_processEth1DataReset resetOk
    · simp only [pure, Except.pure, Except.ok.injEq] at resetOk
      exact resetOk ▸ BuilderFrame.refl _
  refine ⟨pending, paid, ?_, paidOk, ?_⟩
  · exact (builderFrame_processJustificationAndFinalization justifiedOk).trans <|
      (builderFrame_processInactivityUpdates scoredOk).trans <|
      (builderFrame_processRewardsAndPenalties rewardedOk).trans <|
      (builderFrame_processRegistryUpdates registeredOk).trans <|
      (builderFrame_processSlashings slashedOk).trans <|
      resetFrame.trans (builderFrame_processPendingBalances pendingOk)
  have rotated : BuilderFrame rooted (processParticipationFlagUpdates rooted altair) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact (builderFrame_processEffectiveBalanceUpdates balancedOk).trans <|
    (builderFrame_processSlashingsReset clearedOk).trans <|
    (builderFrame_processRandaoMixesReset mixedOk).trans <|
    (builderFrame_processHistoricalSummariesUpdate rootedOk).trans <|
    rotated.trans <|
    (builderFrame_processSyncCommitteeUpdates syncedOk).trans <|
    (builderFrame_processProposerLookahead lookedOk).trans (builderFrame_processPtcWindow windowed)

/-! ## Slots -/

private theorem builderFrame_processSlot (computed : processSlot state = .ok after) :
    BuilderFrame state after := by
  have header : after.latestBlockHeader.slot = state.latestBlockHeader.slot := by
    unfold processSlot at computed
    simp only [bind_ok_iff, liftSsz_ok, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, computed⟩ := computed
    split at computed
    · obtain ⟨_, _, _, _, rfl⟩ := unsetNextPayloadAvailability_ok (liftAccessor_ok.mp computed)
      dsimp only
      split <;> rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      dsimp only
      split <;> rfl
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok computed
  exact ⟨rfl, header, rfl, rfl, rfl, rfl⟩

/-- A move to a slot of the same epoch keeps the position of the parent payment. -/
private theorem parentPaymentPosition_withSlot {next : Slot}
    (same : next.toNat / preset.SLOTS_PER_EPOCH.toNat =
      state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat) :
    parentPaymentPosition { state with slot := next } = parentPaymentPosition state := by
  have epoch : computeEpochAtSlot preset next = computeEpochAtSlot preset state.slot := by
    apply UInt64.toNat_inj.mp
    simpa only [computeEpochAtSlot, UInt64.toNat_div] using same
  unfold parentPaymentPosition getPreviousEpoch getCurrentEpoch
  dsimp only
  rw [epoch]

/-- A move to a slot of the same epoch keeps the builder debt invariant. -/
private theorem BuilderDebtCovered.withSlot {gloas : .glamsterdam ≤ fork} {next : Slot}
    (same : next.toNat / preset.SLOTS_PER_EPOCH.toNat =
      state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat)
    (holds : BuilderDebtCovered state gloas) :
    BuilderDebtCovered { state with slot := next } gloas :=
  .of_position (parentPaymentPosition_withSlot same) rfl rfl rfl rfl holds

/-- With a positive quorum, one slot keeps the builder debt invariant. -/
theorem BuilderDebtCovered.advanceSlot (positive : preset.PaymentQuorumPositive)
    {gloas : .glamsterdam ≤ fork} (holds : BuilderDebtCovered state gloas)
    (computed : advanceSlot config checks state = .ok after) : BuilderDebtCovered after gloas := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have cachedFrame := builderFrame_processSlot cachedOk
  have cachedHolds := holds.of_frame cachedFrame
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    obtain ⟨pending, paid, before, paidOk, tail⟩ := processEpoch_builderSplit epochedOk
    have paidHolds := (cachedHolds.of_frame before).processBuilderPendingPayments positive paidOk
      (by rw [before.slot, cachedFrame.slot]; exact sum) boundary
    have frame : BuilderFrame { paid with slot := next } { epoched with slot := next } :=
      ⟨rfl, tail.headerSlot, tail.builders, tail.payments, tail.withdrawals, tail.bid⟩
    exact paidHolds.of_frame frame
  · rename_i inside
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    exact cachedHolds.withSlot
      (by rw [cachedFrame.slot]; exact nextSlot_epoch_of_inside sum inside)

/-- With a positive quorum, a run of slots keeps the builder debt invariant. -/
theorem BuilderDebtCovered.processSlots (positive : preset.PaymentQuorumPositive)
    {gloas : .glamsterdam ≤ fork} (holds : BuilderDebtCovered state gloas) {slot : Slot}
    (computed : processSlots config checks state slot = .ok after) :
    BuilderDebtCovered after gloas := by
  simp only [Consensus.processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨-, -, advanced⟩ := computed
  generalize slot.toNat - state.slot.toNat = count at advanced
  induction count generalizing state with
  | zero =>
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at advanced
    exact advanced ▸ holds
  | succ count step =>
    simp only [advanceSlots, bind_ok_iff] at advanced
    obtain ⟨next, nextOk, rest⟩ := advanced
    exact step (holds.advanceSlot positive nextOk) rest

end EthLib.Consensus
