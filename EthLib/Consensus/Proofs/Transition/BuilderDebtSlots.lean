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

A run of slots also keeps the builders.

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

/-- Adding a validator keeps the builder fields and the two slots. -/
theorem builderFrame_addValidatorToRegistry {pubkey withdrawalCredentials amount}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    BuilderFrame state after := by
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  split at computed
  · cases computed
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases computed

/-- Keeping the builder fields and the two slots satisfies the laws of the epoch steps. -/
private theorem builderEpochFrameLaws : EpochFrameLaws (@BuilderFrame preset fork)
    where
  refl := BuilderFrame.refl
  trans := BuilderFrame.trans
  setValidator := fun set _ _ _ _ => builderFrame_setValidator set
  increaseBalance := builderFrame_increaseBalance
  decreaseBalance := builderFrame_decreaseBalance
  initiateValidatorExit := builderFrame_initiateValidatorExit
  addValidatorToRegistry := builderFrame_addValidatorToRegistry
  eth1DataVotes _ _ := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  inactivityScores _ _ := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  slashings _ _ := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  randaoMixes _ _ := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  historicalRoots _ _ := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  historicalSummaries _ _ := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  participationRecords _ := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  pendingDeposits _ _ _ := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  pendingConsolidations _ _ := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  syncCommittees _ _ _ := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  proposerLookahead _ _ := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  ptcWindow _ _ := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Applying a pending deposit keeps the builder fields and the two slots. -/
theorem builderFrame_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    BuilderFrame state after :=
  builderEpochFrameLaws.applyPendingDeposit computed

/-- From Gloas, the epoch transition keeps the builder fields, except the step of the payments.

The step of the payments reads the state that the epoch transition reaches before it. -/
theorem processEpoch_builderSplit {gloas : .glamsterdam ≤ fork}
    (computed : processEpoch config checks state = .ok after) :
    ∃ pending paid, epochBeforePayments config checks state = .ok pending ∧
      BuilderFrame state pending ∧
      processBuilderPendingPayments pending gloas = .ok paid ∧ BuilderFrame paid after := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) gloas
  unfold processEpoch at computed
  simp only [altair, ↓reduceDIte] at computed
  obtain ⟨pending, paid, rooted, pendingOk, paidOk, middle, tail⟩ :=
    builderEpochFrameLaws.processEpochAltair_paymentSplit computed
  obtain ⟨justified, justifiedOk, head⟩ := builderEpochFrameLaws.epochBeforePayments_split pendingOk
  have justifiedFrame : BuilderFrame state justified := by
    obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok justifiedOk
    · exact BuilderFrame.refl _
    · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
      exact ⟨by rw [← rest], by rw [← rest], by rw [← rest], by rw [← rest], by rw [← rest],
        by rw [← rest]⟩
  have rotated : BuilderFrame rooted (processParticipationFlagUpdates rooted altair) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨pending, paid, pendingOk, justifiedFrame.trans head,
    by simpa only [gloas, ↓reduceDIte, liftAccessor_ok] using paidOk,
    middle.trans (rotated.trans tail)⟩

/-! ## Slots -/

/-- A slot keeps the builder fields, the slot and the slot of the latest block. -/
theorem builderFrame_processSlot (computed : processSlot state = .ok after) :
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

/-- One slot keeps the builders. -/
theorem advanceSlot_builders (gloas : .glamsterdam ≤ fork)
    (computed : advanceSlot config checks state = .ok after) :
    after.builders gloas = state.builders gloas := by
  obtain ⟨next, cached, epoched, -, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have cachedFrame := builderFrame_processSlot cachedOk
  unfold epochIfLast at epochedOk
  split at epochedOk
  · obtain ⟨pending, paid, -, before, paidOk, tail⟩ :=
      processEpoch_builderSplit (gloas := gloas) epochedOk
    have paidBuilders : paid.builders = pending.builders := by
      rw [processBuilderPendingPayments_eq paidOk]
    simp only [tail.builders, paidBuilders, before.builders, cachedFrame.builders]
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    simp only [cachedFrame.builders]

/-- A run of slots keeps the builders. -/
theorem processSlots_builders (gloas : .glamsterdam ≤ fork) {slot : Slot}
    (computed : processSlots config checks state slot = .ok after) :
    after.builders gloas = state.builders gloas := by
  simp only [Consensus.processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨-, -, advanced⟩ := computed
  generalize slot.toNat - state.slot.toNat = count at advanced
  induction count generalizing state with
  | zero =>
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at advanced
    subst advanced
    rfl
  | succ count step =>
    simp only [advanceSlots, bind_ok_iff] at advanced
    obtain ⟨next, nextOk, rest⟩ := advanced
    exact (step rest).trans (advanceSlot_builders gloas nextOk)

/-- A move to a slot of the same epoch keeps the builder debt invariant. -/
private theorem BuilderDebtCovered.withSlot {gloas : .glamsterdam ≤ fork} {next : Slot}
    (same : next.toNat / preset.SLOTS_PER_EPOCH.toNat =
      state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat)
    (holds : BuilderDebtCovered state gloas) :
    BuilderDebtCovered { state with slot := next } gloas :=
  .of_position (slotPaymentPosition_congr_epoch (after := { state with slot := next }) same _)
    rfl rfl rfl rfl holds

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
    obtain ⟨pending, paid, -, before, paidOk, tail⟩ := processEpoch_builderSplit epochedOk
    have paidHolds := (cachedHolds.of_frame before).processBuilderPendingPayments positive paidOk
      (by rw [before.slot, cachedFrame.slot]; exact sum) boundary
    exact paidHolds.of_frame (tail.withSlot next)
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
