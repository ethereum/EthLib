module

public import EthLib.Consensus.Proofs.Transition.Chain
public import EthLib.Consensus.Proofs.Transition.Committees
public import EthLib.Consensus.Proofs.Transition.PayloadInputs

/-!
# Proofs: activity up to the current epoch plus `MAX_SEED_LOOKAHEAD` stays fixed along a chain

A validator is active in an epoch from its activation epoch, up to its exit epoch.

The state transition sets an activation or an exit epoch only after a bound.

That bound is the current epoch plus `MAX_SEED_LOOKAHEAD`.

An activation lands at the first epoch an activation may take, `MAX_SEED_LOOKAHEAD + 1` epochs on.

An exit lands there or later, by the exit queue or the consolidation queue.

From Electra, the exit and consolidation queues of [EIP-7251] give no epoch before that one.

A new validator has no activation epoch yet, so it is active in no epoch.

So each step of a chain keeps which validators are active in each epoch up to that bound.

That holds at every fork, for slots, epochs, blocks and upgrades.

The current epoch never decreases along a chain.

So that bound never decreases either.

So along a run of steps, the active sets stay fixed in each epoch up to the bound of its start.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#specification
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-! ## Steps that keep activity -/

/-- A step that never shrinks the registry.

It keeps the slot and activity. -/
private def StepKeeps (state after : BeaconState preset fork) : Prop :=
  state.validators.data.size ≤ after.validators.data.size ∧
    ActiveStep state after

private theorem StepKeeps.refl (state : BeaconState preset fork) : StepKeeps state state :=
  ⟨Nat.le_refl _, ActiveStep.refl state⟩

private theorem StepKeeps.trans {first second third : BeaconState preset fork}
    (one : StepKeeps first second) (two : StepKeeps second third) : StepKeeps first third :=
  ⟨Nat.le_trans one.1 two.1, one.2.trans two.2⟩

private theorem StepKeeps.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (keeps : ∀ s x s', step s x = .ok s' → StepKeeps s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : StepKeeps state after :=
  foldlM_ok_invariant (StepKeeps state) (fun _ _ _ before ok => before.trans (keeps _ _ _ ok))
    (StepKeeps.refl state) computed

private theorem StepKeeps.of_step (grows : state.validators.data.size ≤ after.validators.data.size)
    (step : ActiveStep state after) : StepKeeps state after :=
  ⟨grows, step⟩

private theorem StepKeeps.of_validators
    (validators : after.validators.data = state.validators.data := by rfl)
    (slot : after.slot = state.slot := by rfl) : StepKeeps state after :=
  ⟨Nat.le_of_eq (congrArg Array.size validators).symm,
    ActiveStep.of_validators validators slot⟩

/-! ## Mutators -/

private theorem stepKeeps_setValidatorAt {index : Nat} {validator old : Validator}
    (found : getValidatorAt state index = .ok old)
    (same : ∀ epoch ≤ activityFixedEpoch state,
      isActiveValidator validator epoch = isActiveValidator old epoch)
    (set : state.setValidatorAt index validator = .ok after) : StepKeeps state after :=
  StepKeeps.of_step (Nat.le_of_eq (sameSizes_setValidatorAt set).1.symm)
    (activeStep_setValidatorAt found same set)

private theorem stepKeeps_setValidator {index : ValidatorIndex} {validator old : Validator}
    (found : getValidator state index = .ok old)
    (same : ∀ epoch ≤ activityFixedEpoch state,
      isActiveValidator validator epoch = isActiveValidator old epoch)
    (set : state.setValidator index validator = .ok after) : StepKeeps state after :=
  stepKeeps_setValidatorAt (by rwa [← getValidator_eq_getValidatorAt]) same
    (by rwa [← setValidator_eq_setValidatorAt])

private theorem stepKeeps_increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : StepKeeps state after :=
  StepKeeps.of_step (frame_increaseBalance computed).registryGrows
    (activeStep_increaseBalance computed)

private theorem stepKeeps_decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : StepKeeps state after :=
  StepKeeps.of_step (frame_decreaseBalance computed).registryGrows
    (activeStep_decreaseBalance computed)

private theorem stepKeeps_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) : StepKeeps state after :=
  StepKeeps.of_step (frame_initiateValidatorExit computed).registryGrows
    (activeStep_initiateValidatorExit computed)

private theorem stepKeeps_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    StepKeeps state after :=
  StepKeeps.of_step (frame_slashValidator computed).registryGrows
    (activeStep_slashValidator computed)

private theorem stepKeeps_addValidatorToRegistry {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    StepKeeps state after :=
  StepKeeps.of_step (by rw [addValidatorToRegistry_validators_eq_push computed]; simp)
    (activeStep_addValidatorToRegistry computed)

/-! ## Deposits -/

private theorem stepKeeps_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    StepKeeps state after := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact StepKeeps.refl _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact stepKeeps_addValidatorToRegistry computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ StepKeeps.refl _
  · simp only [liftAccessor_ok, bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    exact stepKeeps_increaseBalance computed

private theorem stepKeeps_applyDepositElectra {electra : .pectra ≤ fork}
    {pubkey : Cryptography.Bls.BLSPubkey} {withdrawalCredentials : Bytes32} {amount : Gwei}
    {signature : Cryptography.Bls.BLSSignature}
    (computed : applyDepositElectra config checks state electra pubkey withdrawalCredentials
      amount signature = .ok after) :
    StepKeeps state after := by
  unfold applyDepositElectra at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, added, pushed⟩ := computed
      obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
      exact (stepKeeps_addValidatorToRegistry added).trans StepKeeps.of_validators
    · cases computed
      exact StepKeeps.refl _
  · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
    exact StepKeeps.of_validators

private theorem stepKeeps_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    StepKeeps state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  refine (StepKeeps.of_validators (state := state)
    (after := { state with eth1DepositIndex := fun _ => next })).trans ?_
  unfold applyDeposit at applied
  split at applied
  · exact stepKeeps_applyDepositElectra applied
  · exact stepKeeps_applyPendingDeposit applied

/-! ## Requests of the execution layer -/

private theorem stepKeeps_processDepositRequest {electra : .pectra ≤ fork}
    {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    StepKeeps state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact StepKeeps.of_validators

private theorem stepKeeps_requestPartialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    StepKeeps state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    obtain ⟨-, validators, -⟩ := computeExitEpochAndUpdateChurn_earliest churned
    exact StepKeeps.of_validators (by rw [validators])
      (frame_computeExitEpochAndUpdateChurn churned).slot
  · cases computed
    exact StepKeeps.refl _

private theorem stepKeeps_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    StepKeeps state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact StepKeeps.refl _)
    | exact stepKeeps_initiateValidatorExit (liftAccessor_ok.mp computed)
    | exact stepKeeps_requestPartialWithdrawal computed

private theorem stepKeeps_queueExcessActiveBalance {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : queueExcessActiveBalance state electra index = .ok after) :
    StepKeeps state after := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, set, rfl⟩ := computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact StepKeeps.of_validators
  · cases computed
    exact StepKeeps.refl _

/-- Compounding credentials keep the activation and the exit epoch. -/
private theorem stepKeeps_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    StepKeeps state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨validator, found, _, set, queued⟩ := computed
  exact (stepKeeps_setValidator found (fun _ _ => by rfl) set).trans
    (stepKeeps_queueExcessActiveBalance queued)

/-- A consolidation from Electra takes effect after the current epoch plus `MAX_SEED_LOOKAHEAD`. -/
private theorem consolidationEpoch_lt {electra : .pectra ≤ fork} {balance : Gwei}
    {churned : BeaconState preset fork} {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (churned, epoch)) :
    (getCurrentEpoch state).toNat + preset.MAX_SEED_LOOKAHEAD.toNat < epoch.toNat := by
  cases first : computeActivationExitEpoch preset (getCurrentEpoch state) with
  | error =>
    simp [computeConsolidationEpochAndUpdateChurn, first, liftArith, Except.mapError, bind,
      Except.bind] at computed
  | ok firstEpoch =>
    have early := UInt64.le_iff_toNat_le.mp
      (computeConsolidationEpochAndUpdateChurn_first first computed).1
    have firstEq := (computeActivationExitEpoch_ok_iff.mp first).2
    omega

/-- The source of a consolidation had not started to exit, and exits after the fixed epoch.

It must be the validator at its index. -/
private theorem stepKeeps_queueConsolidation {electra : .pectra ≤ fork}
    {sourceIndex : ValidatorIndex} {source : Validator} {targetIndex : ValidatorIndex}
    (found : state.validators.data[sourceIndex.toNat]? = some source)
    (far : source.exitEpoch = FAR_FUTURE_EPOCH)
    (computed :
      queueConsolidation config state electra sourceIndex source targetIndex = .ok after) :
    StepKeeps state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure] at computed
  obtain ⟨⟨churnedState, exitEpoch⟩, churned, withdrawable, ⟨_, sum⟩, _, set, _, _, computed⟩ :=
    computed
  simp only [Except.ok.injEq] at computed
  subst computed
  have later := consolidationEpoch_lt churned
  obtain ⟨-, validators, -⟩ := computeConsolidationEpochAndUpdateChurn_earliest churned
  have slot := (frame_computeConsolidationEpochAndUpdateChurn churned).slot
  have first : StepKeeps state churnedState := StepKeeps.of_validators (by rw [validators]) slot
  have found' : getValidator churnedState sourceIndex = .ok source := by
    rw [getValidator, validators, found]
  refine first.trans ((stepKeeps_setValidator found' (fun _ le => ?_) set).trans
    StepKeeps.of_validators)
  have epochEq : getCurrentEpoch churnedState = getCurrentEpoch state := by
    simp only [getCurrentEpoch, slot]
  exact isActiveValidator_eq_of_exit rfl far
    (activityFixedEpoch_lt_of_toNat_lt (by rw [epochEq]; exact later)) le

private theorem stepKeeps_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    StepKeeps state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals try first
    | (cases computed; done)
    | (cases computed; exact StepKeeps.refl _)
    | exact stepKeeps_switchToCompoundingValidator (liftAccessor_ok.mp computed)
  -- The source had not started to exit.
  rename_i bothFar _ _ _ _ _ _ _ _
  exact stepKeeps_queueConsolidation (getElem?_toNat_of_ofNatChecked (by assumption))
    (beq_iff_eq.mp ((Bool.and_eq_true _ _).mp bothFar).1) computed

private theorem stepKeeps_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    StepKeeps state after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  exact (StepKeeps.foldlM (fun _ _ _ ok => stepKeeps_processDepositRequest ok) depositsOk).trans <|
    (StepKeeps.foldlM (fun _ _ _ ok => stepKeeps_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    StepKeeps.foldlM (fun _ _ _ ok => stepKeeps_processConsolidationRequest ok) consolidationsOk

/-! ## Withdrawals and the execution part of a block -/

private theorem stepKeeps_applyWithdrawal {withdrawal : Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) : StepKeeps state after := by
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, set⟩ := computed
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact StepKeeps.of_validators
  · exact stepKeeps_decreaseBalance computed

private theorem stepKeeps_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    StepKeeps state after := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : StepKeeps state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact StepKeeps.foldlM (fun _ _ _ ok => stepKeeps_applyWithdrawal ok) appliedOk
  have indexedStep : StepKeeps applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      exact StepKeeps.of_validators
    · cases indexedOk
      exact StepKeeps.refl _
  have queued : ∀ kept : BeaconState preset fork,
      StepKeeps kept (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals kept gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else kept) := by
    intro kept
    split <;> exact StepKeeps.of_validators
  have partials : ∀ kept : BeaconState preset fork,
      StepKeeps kept (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals kept electra expected.processedPartialWithdrawalsCount
      else kept) := by
    intro kept
    split <;> exact StepKeeps.of_validators
  have swept : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → StepKeeps kept finished := by
    intro kept ok
    split at ok
    · unfold updateNextWithdrawalBuilderIndex at ok
      dsimp only at ok
      split at ok
      · cases ok
        exact StepKeeps.of_validators
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
        obtain ⟨_, _, rfl⟩ := ok
        exact StepKeeps.of_validators
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ StepKeeps.refl _
  have lastStep : StepKeeps finished after := by
    unfold updateNextWithdrawalValidatorIndex at last
    simp only [bind_ok_iff] at last
    obtain ⟨_, _, last⟩ := last
    split at last
    · cases last
    · cases last
      exact StepKeeps.of_validators
  exact one.trans <| indexedStep.trans <| (queued _).trans <| (partials _).trans <|
    (swept _ sweptOk).trans lastStep

private theorem stepKeeps_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) : StepKeeps state after := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, applied⟩ := computed
      exact stepKeeps_applyExpectedWithdrawals applied
    · cases computed
      exact StepKeeps.refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact stepKeeps_applyExpectedWithdrawals applied

private theorem stepKeeps_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    StepKeeps state after := by
  obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact stepKeeps_setValidator found (fun _ _ => by simp only [isActiveValidator]) set

private theorem stepKeeps_processExecutionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    StepKeeps state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  exact StepKeeps.of_validators

private theorem stepKeeps_processBuilderDepositRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    StepKeeps state after := by
  unfold processBuilderDepositRequest addBuilderToRegistry at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact StepKeeps.of_validators)

private theorem stepKeeps_processBuilderExitRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    StepKeeps state after := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · exact StepKeeps.refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact StepKeeps.of_validators

private theorem stepKeeps_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    StepKeeps state after := by
  rcases processParentExecutionPayload_ok computed with ⟨-, -, rfl⟩ |
    ⟨-, settled, _, _, _, _, _, _, settledOk, depositsOk, withdrawalsOk, consolidationsOk,
      buildersOk, exitsOk, -, rfl⟩
  · exact StepKeeps.refl _
  · have settledStep : StepKeeps state settled := by
      rw [settleParentPayment_eq settledOk]
      exact StepKeeps.of_validators
    exact settledStep.trans <|
      (StepKeeps.foldlM (fun _ _ _ ok => stepKeeps_processDepositRequest ok) depositsOk).trans <|
      (StepKeeps.foldlM (fun _ _ _ ok => stepKeeps_processWithdrawalRequest ok)
        withdrawalsOk).trans <|
      (StepKeeps.foldlM (fun _ _ _ ok => stepKeeps_processConsolidationRequest ok)
        consolidationsOk).trans <|
      (StepKeeps.foldlM (fun _ _ _ ok => stepKeeps_processBuilderDepositRequest ok)
        buildersOk).trans <|
      (StepKeeps.foldlM (fun _ _ _ ok => stepKeeps_processBuilderExitRequest ok) exitsOk).trans
        StepKeeps.of_validators

private theorem stepKeeps_processExecutionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    StepKeeps state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok computed
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact StepKeeps.of_validators
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at recordedOk
    subst recordedOk
    exact StepKeeps.of_validators

private theorem stepKeeps_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    StepKeeps state after := by
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    exact (stepKeeps_processWithdrawals withdrawnOk).trans
      (stepKeeps_processExecutionPayloadBid bid)
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact (stepKeeps_processWithdrawals withdrawnOk).trans (stepKeeps_processExecutionPayload paid)
  · dsimp only at computed
    split at computed
    · exact stepKeeps_processExecutionPayload computed
    · cases computed
      exact StepKeeps.refl _

private theorem stepKeeps_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    StepKeeps state after := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  refine StepKeeps.foldlM (fun _ _ _ ok => ?_) folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    exact (stepKeeps_increaseBalance raised).trans (stepKeeps_increaseBalance paid)
  · exact stepKeeps_decreaseBalance (liftAccessor_ok.mp ok)

/-! ## The other steps of a block -/

private theorem stepKeeps_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) : StepKeeps state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact StepKeeps.of_validators

private theorem stepKeeps_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) : StepKeeps state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact StepKeeps.of_validators

private theorem stepKeeps_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) : StepKeeps state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  rw [← rest]
  exact StepKeeps.of_validators

private theorem stepKeeps_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    StepKeeps state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact stepKeeps_slashValidator slashed

private theorem stepKeeps_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    StepKeeps state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  refine foldlM_ok_invariant (fun step => StepKeeps state step.1)
    (fun step _ next before ok => before.trans ?_)
    (show StepKeeps state (state, false).1 from StepKeeps.refl state) folded
  obtain ⟨middle, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact stepKeeps_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at ok
    exact ok ▸ StepKeeps.refl _

private theorem stepKeeps_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    StepKeeps state after :=
  StepKeeps.of_validators (by rw [(processAttestation_registry computed).1])
    (frame_processAttestation computed).slot

private theorem stepKeeps_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    StepKeeps state after := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact stepKeeps_initiateValidatorExit exited

/-! ## Blocks -/

private theorem stepKeeps_processOperations {body : BeaconBlockBody preset fork}
    {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    StepKeeps state after := by
  unfold processOperations at computed
  split at computed
  · unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
    exact (StepKeeps.foldlM (fun _ _ _ ok => stepKeeps_processProposerSlashing ok)
      proposersOk).trans <|
      (StepKeeps.foldlM (fun _ _ _ ok => stepKeeps_processAttesterSlashing ok) attestersOk).trans <|
      (StepKeeps.foldlM (fun _ _ _ ok => stepKeeps_processAttestation ok) attestedOk).trans <|
      (StepKeeps.foldlM (fun _ _ _ ok => stepKeeps_processVoluntaryExit ok) exitsOk).trans <|
      (StepKeeps.foldlM (fun _ _ _ ok => stepKeeps_processBlsToExecutionChange ok)
        changesOk).trans <|
      StepKeeps.foldlM (fun _ _ _ ok => by
        rw [processPayloadAttestation_eq ok]
        exact StepKeeps.refl _) paid
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, exited,
    exitsOk, changed, changesOk, requestsOk⟩ := computed
  have changes : StepKeeps exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact StepKeeps.foldlM (fun _ _ _ ok => stepKeeps_processBlsToExecutionChange ok) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ StepKeeps.refl _
  have requests : StepKeeps changed after := by
    split at requestsOk
    · exact stepKeeps_processExecutionRequests requestsOk
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact requestsOk ▸ StepKeeps.refl _
  exact (StepKeeps.foldlM (fun _ _ _ ok => stepKeeps_processProposerSlashing ok)
    proposersOk).trans <|
    (StepKeeps.foldlM (fun _ _ _ ok => stepKeeps_processAttesterSlashing ok) attestersOk).trans <|
    (StepKeeps.foldlM (fun _ _ _ ok => stepKeeps_processAttestation ok) attestedOk).trans <|
    (StepKeeps.foldlM (fun _ _ _ ok => stepKeeps_processDeposit ok) depositedOk).trans <|
    (StepKeeps.foldlM (fun _ _ _ ok => stepKeeps_processVoluntaryExit ok) exitsOk).trans <|
    changes.trans requests

private theorem stepKeeps_processBlock {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    StepKeeps state after := by
  unfold processBlock at computed
  split at computed
  · unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, _, operatedOk, synced⟩ := computed
    have paidStep : StepKeeps state paid := by
      split at paidOk
      · exact stepKeeps_processParentExecutionPayload paidOk
      · cases paidOk
        exact StepKeeps.refl _
    have executedStep : StepKeeps headed executed := by
      split at executedOk
      · exact stepKeeps_processBlockExecution executedOk
      · cases executedOk
        exact StepKeeps.refl _
    have votedStep : StepKeeps revealed voted := by
      split at votedOk
      · exact stepKeeps_processEth1Data votedOk
      · cases votedOk
        exact StepKeeps.refl _
    exact paidStep.trans <| (stepKeeps_processBlockHeader headedOk).trans <|
      executedStep.trans <| (stepKeeps_processRandao revealedOk).trans <| votedStep.trans <|
      (stepKeeps_processOperations operatedOk).trans (stepKeeps_processSyncAggregate synced)
  simp only [bind_ok_iff] at computed
  obtain ⟨_, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := computed
  exact (stepKeeps_processBlockHeader headerOk).trans <| (stepKeeps_processRandao randaoOk).trans <|
    (stepKeeps_processEth1Data eth1Ok).trans (stepKeeps_processOperations operationsOk)

/-! ## The steps of an epoch -/

private theorem stepKeeps_processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) :
    StepKeeps state after :=
  StepKeeps.of_step
    (by rw [(processJustificationAndFinalization_keeps computed).2.2.2.2.2.1]; exact Nat.le_refl _)
    (activeStep_processJustificationAndFinalization computed)

private theorem stepKeeps_processInactivityUpdates {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) :
    StepKeeps state after := by
  unfold processInactivityUpdates at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ StepKeeps.refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact StepKeeps.of_validators

/-- From Electra, the registry updates of one validator keep activity up to the fixed epoch.

An activation goes to an epoch after the fixed epoch, and only from the far future. -/
private theorem stepKeeps_updateRegistryEntryElectra {activationEpoch : Epoch} {index : Nat}
    (later :
      (getCurrentEpoch state).toNat + preset.MAX_SEED_LOOKAHEAD.toNat < activationEpoch.toNat)
    (computed : updateRegistryEntryElectra config activationEpoch state index = .ok after) :
    StepKeeps state after := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, set⟩ := computed
    exact stepKeeps_setValidatorAt found (fun _ _ => by simp only [isActiveValidator]) set
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, exited⟩ := computed
    exact stepKeeps_initiateValidatorExit exited
  split at computed
  · rename_i eligible
    simp only [isEligibleForActivation, Bool.and_eq_true, beq_iff_eq] at eligible
    -- Neither the far-future epoch nor the new one is at or before the fixed epoch.
    exact stepKeeps_setValidatorAt found (fun _ le => isActiveValidator_eq_of_activation
      (.inl eligible.2) (activityFixedEpoch_lt_of_toNat_lt later) le) (liftAccessor_ok.mp computed)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ StepKeeps.refl _

private theorem stepKeeps_processRegistryUpdates
    (computed : processRegistryUpdates config state = .ok after) : StepKeeps state after := by
  have grows := (frame_processRegistryUpdates computed).registryGrows
  by_cases electra : Fork.pectra ≤ fork
  · unfold processRegistryUpdates at computed
    simp only [electra, ↓reduceIte, bind_ok_iff, liftAccessor_ok, liftArith,
      mapError_ok_iff] at computed
    obtain ⟨activationEpoch, activationOk, computed⟩ := computed
    have activationEq := (computeActivationExitEpoch_ok_iff.mp activationOk).2
    -- Each step keeps the slot, so the activation epoch stays after the fixed epoch.
    refine (foldlM_ok_invariant (fun middle => StepKeeps state middle ∧ middle.slot = state.slot)
      (fun middle _ next before ok => ⟨before.1.trans
        (stepKeeps_updateRegistryEntryElectra ?_ ok),
        (frame_updateRegistryEntryElectra ok).slot.trans before.2⟩)
      ⟨StepKeeps.refl state, rfl⟩ computed).1
    have epoch : getCurrentEpoch middle = getCurrentEpoch state := by
      simp only [getCurrentEpoch, before.2]
    rw [epoch, activationEq]
    omega
  · exact StepKeeps.of_step grows
      (activeStep_processRegistryUpdates (Nat.lt_of_not_le electra) computed)

private theorem stepKeeps_passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      StepKeeps state pass.1.state
  | [], _, _, _, _, _, computed => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact StepKeeps.refl _
  | deposit :: rest, state, processed, count, postponed, pass, computed => by
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      exact StepKeeps.refl _
    split at computed
    · cases computed
    split at computed
    · split at computed
      · cases computed
      rename_i credited
      split at computed
      · cases computed
      cases computed
      exact (stepKeeps_applyPendingDeposit credited).trans
        (stepKeeps_passPendingDeposits (deposits := rest) ‹_›)
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact stepKeeps_passPendingDeposits (deposits := rest) ‹_›
    split at computed
    · cases computed
    split at computed
    · cases computed
      exact StepKeeps.refl _
    split at computed
    · cases computed
    rename_i credited
    split at computed
    · cases computed
    cases computed
    exact (stepKeeps_applyPendingDeposit credited).trans
      (stepKeeps_passPendingDeposits (deposits := rest) ‹_›)

private theorem stepKeeps_processPendingBalances
    (computed : processPendingBalances config checks state = .ok after) :
    StepKeeps state after := by
  unfold processPendingBalances at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨middle, deposited, consolidated⟩ := computed
    have deposits : StepKeeps state middle := by
      unfold processPendingDeposits at deposited
      simp only [bind, Except.bind, pure, Except.pure] at deposited
      repeat' (split at deposited <;> try cases deposited)
      all_goals
        exact (stepKeeps_passPendingDeposits ‹_›).trans StepKeeps.of_validators
    exact deposits.trans (StepKeeps.of_validators
      (by rw [(processPendingConsolidations_kept consolidated).1])
      (frame_processPendingConsolidations consolidated).slot)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ StepKeeps.refl _

private theorem stepKeeps_epochTail {altair : .altair ≤ fork}
    {rooted synced looked : BeaconState preset fork}
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair)
      altair = .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) : StepKeeps rooted after := by
  have syncedStep : StepKeeps (processParticipationFlagUpdates rooted altair) synced := by
    unfold processSyncCommitteeUpdates at syncedOk
    simp only [bind, Except.bind, pure, Except.pure] at syncedOk
    repeat' (split at syncedOk <;> try cases syncedOk)
    all_goals exact StepKeeps.refl _
  have lookedStep : StepKeeps synced looked := by
    split at lookedOk
    · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at lookedOk
      obtain ⟨_, _, _, _, rfl⟩ := lookedOk
      exact StepKeeps.of_validators
    · simp only [pure, Except.pure, Except.ok.injEq] at lookedOk
      exact lookedOk ▸ StepKeeps.refl _
  have windowedStep : StepKeeps looked after := by
    split at windowed
    · simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at windowed
      obtain ⟨_, _, _, _, rfl⟩ := windowed
      exact StepKeeps.of_validators
    · simp only [pure, Except.pure, Except.ok.injEq] at windowed
      exact windowed ▸ StepKeeps.refl _
  exact (StepKeeps.of_validators : StepKeeps rooted _).trans <| syncedStep.trans <|
    lookedStep.trans windowedStep

private theorem stepKeeps_processEpochAltair {altair : .altair ≤ fork}
    (computed : processEpochAltair config checks state altair = .ok after) :
    StepKeeps state after := by
  unfold processEpochAltair at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
    registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk, balanced,
    balancedOk, cleared, clearedOk, mixed, mixedOk, computed⟩ := computed
  have resetStep : StepKeeps slashed reset := by
    split at resetOk
    · exact StepKeeps.of_step (frame_processEth1DataReset resetOk).registryGrows
        (activeStep_processEth1DataReset resetOk)
    · simp only [pure, Except.pure, Except.ok.injEq] at resetOk
      exact resetOk ▸ StepKeeps.refl _
  have paidStep : StepKeeps pending paid := by
    split at paidOk
    · simp only [processBuilderPendingPayments, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at paidOk
      obtain ⟨_, _, rfl⟩ := paidOk
      exact StepKeeps.of_validators
    · simp only [pure, Except.pure, Except.ok.injEq] at paidOk
      exact paidOk ▸ StepKeeps.refl _
  have mixedStep : StepKeeps cleared mixed := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    exact StepKeeps.of_validators
  have head : StepKeeps state mixed :=
    (stepKeeps_processJustificationAndFinalization justifiedOk).trans <|
    (stepKeeps_processInactivityUpdates scoredOk).trans <|
    (StepKeeps.of_step (frame_processRewardsAndPenalties rewardedOk).registryGrows
      (activeStep_processRewardsAndPenalties rewardedOk)).trans <|
    (stepKeeps_processRegistryUpdates registeredOk).trans <|
    (StepKeeps.of_step (frame_processSlashings slashedOk).registryGrows
      (activeStep_processSlashings slashedOk)).trans <|
    resetStep.trans <|
    (stepKeeps_processPendingBalances pendingOk).trans <|
    paidStep.trans <|
    (StepKeeps.of_step (frame_processEffectiveBalanceUpdates balancedOk).registryGrows
      (activeStep_processEffectiveBalanceUpdates balancedOk)).trans <|
    (StepKeeps.of_step (frame_processSlashingsReset clearedOk).registryGrows
      (activeStep_processSlashingsReset clearedOk)).trans mixedStep
  split at computed <;> simp only [bind_ok_iff] at computed <;>
    obtain ⟨rooted, rootedOk, synced, syncedOk, looked, lookedOk, windowed⟩ := computed
  · have rootedStep : StepKeeps mixed rooted := by
      unfold processHistoricalSummariesUpdate at rootedOk
      simp only [bind, Except.bind, pure, Except.pure] at rootedOk
      repeat' (split at rootedOk <;> try cases rootedOk)
      all_goals exact StepKeeps.refl _
    exact head.trans <| rootedStep.trans (stepKeeps_epochTail syncedOk lookedOk windowed)
  · exact head.trans <|
      (StepKeeps.of_step (frame_processHistoricalRootsUpdate rootedOk).registryGrows
        (activeStep_processHistoricalRootsUpdate rootedOk)).trans
      (stepKeeps_epochTail syncedOk lookedOk windowed)

/-- The epoch step keeps activity up to the current epoch plus `MAX_SEED_LOOKAHEAD`.

That holds at every fork. -/
theorem activeKept_processEpoch
    (computed : processEpoch config checks state = .ok after) :
    ActiveKept (activityFixedEpoch state) state after := by
  by_cases altair : Fork.altair ≤ fork
  · simp only [processEpoch, altair, ↓reduceDIte] at computed
    exact (stepKeeps_processEpochAltair computed).2.2
  · exact activeKept_processEpoch_of_lt_altair (Nat.lt_of_not_le altair) computed

/-- The epoch step never shrinks the registry. -/
private theorem processEpoch_registryGrows
    (computed : processEpoch config checks state = .ok after) :
    state.validators.data.size ≤ after.validators.data.size := by
  obtain ⟨_, justifiedOk, frame⟩ := processEpoch_frame computed
  rw [← (processJustificationAndFinalization_keeps justifiedOk).2.2.2.2.2.1]
  exact frame.registryGrows

/-! ## Slots and upgrades -/

/-- One slot never shrinks the registry.

It keeps activity. -/
private theorem advanceSlot_kept (computed : advanceSlot config checks state = .ok after) :
    state.validators.data.size ≤ after.validators.data.size ∧
      ActiveKept (activityFixedEpoch state) state after := by
  obtain ⟨next, cached, epoched, -, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  -- The slot step writes neither the registry nor the slot.
  have validators : cached.validators = state.validators := by rw [cachedEq]
  have epoch : activityFixedEpoch cached = activityFixedEpoch state :=
    activityFixedEpoch_eq_of_slot (by rw [cachedEq])
  have first : ActiveKept (activityFixedEpoch state) state cached :=
    ActiveKept.of_validators (by rw [validators]) _
  suffices kept : cached.validators.data.size ≤ epoched.validators.data.size ∧
      ActiveKept (activityFixedEpoch cached) cached epoched by
    refine ⟨validators ▸ kept.1, first.trans ?_⟩
    exact (epoch ▸ kept.2).trans (ActiveKept.of_validators rfl _)
  unfold epochIfLast at epochedOk
  split at epochedOk
  · exact ⟨processEpoch_registryGrows epochedOk, activeKept_processEpoch epochedOk⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    exact ⟨Nat.le_refl _, ActiveKept.refl _ _⟩

/-- One slot never shrinks the registry. -/
theorem advanceSlot_registryGrows (computed : advanceSlot config checks state = .ok after) :
    state.validators.data.size ≤ after.validators.data.size :=
  (advanceSlot_kept computed).1

/-- Queueing a validator that is not yet active keeps its activation and exit epochs. -/
private theorem stepKeeps_queuePreActivation {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queuePreActivation state electra index = .ok after) : StepKeeps state after := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨validator, found, _, -, _, -, _, set₁, _, set₂, rfl⟩ := computed
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  exact ((StepKeeps.of_validators : StepKeeps state _).trans
    (stepKeeps_setValidator (by exact found) (fun _ _ => by simp only [isActiveValidator])
      set₂)).trans StepKeeps.of_validators

private theorem stepKeeps_queueCompoundingExcess {electra : .pectra ≤ fork} {index : Nat}
    (computed : queueCompoundingExcess state electra index = .ok after) :
    StepKeeps state after := by
  unfold queueCompoundingExcess at computed
  split at computed
  · split at computed
    · exact stepKeeps_queueExcessActiveBalance (liftAccessor_ok.mp computed)
    · cases computed
      exact StepKeeps.refl _
  · cases computed
    exact StepKeeps.refl _

/-- The upgrade to Electra keeps activity up to the current epoch plus `MAX_SEED_LOOKAHEAD`. -/
private theorem activeKept_upgradeToElectra {pre : BeaconState preset .dencun}
    {post : BeaconState preset .pectra} (computed : upgradeToElectra config pre = .ok post) :
    ActiveKept (activityFixedEpoch pre) pre post := by
  simp only [upgradeToElectra, bind_ok_iff] at computed
  obtain ⟨_, -, _, -, _, -, _, -, middle, queued, compounded⟩ := computed
  have step := (StepKeeps.foldlM (fun _ _ _ ok => stepKeeps_queuePreActivation ok) queued).trans
    (StepKeeps.foldlM (fun _ _ _ ok => stepKeeps_queueCompoundingExcess ok) compounded)
  exact (ActiveKept.of_validators rfl _).trans
    step.2.2

/-- A block keeps activity up to the current epoch plus `MAX_SEED_LOOKAHEAD`, at every fork. -/
theorem activeKept_processBlock {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ActiveKept (activityFixedEpoch state) state after :=
  (stepKeeps_processBlock computed).2.2

/-! ## The attestations of a block -/

/-- A step of a block before its attestations.

It is a block frame, and it never shrinks the registry.

It keeps the slot and activity.

Of the RANDAO mixes, it writes at most the one of the current epoch. -/
private structure BeforeVotes (state after : BeaconState preset fork) : Prop where
  frame : BlockFrame state after
  step : StepKeeps state after
  mixes : MixesKeptBut (getCurrentEpoch state) state after

/-- Every state is a step before votes to itself. -/
private theorem BeforeVotes.refl (state : BeaconState preset fork) : BeforeVotes state state :=
  ⟨BlockFrame.refl state, StepKeeps.refl state, fun _ _ => rfl⟩

/-- Two steps before votes in a row are one. -/
private theorem BeforeVotes.trans {first second third : BeaconState preset fork}
    (one : BeforeVotes first second) (two : BeforeVotes second third) :
    BeforeVotes first third := by
  have epoch : getCurrentEpoch second = getCurrentEpoch first := by
    simp only [getCurrentEpoch, one.frame.slot]
  exact ⟨one.frame.trans two.frame, one.step.trans two.step,
    fun other apart => (two.mixes other (epoch ▸ apart)).trans (one.mixes other apart)⟩

/-- A block frame that never shrinks the registry and keeps the mixes is a step before votes. -/
private theorem BeforeVotes.of_mixes (frame : BlockFrame state after)
    (step : StepKeeps state after) (mixes : after.randaoMixes = state.randaoMixes) :
    BeforeVotes state after :=
  ⟨frame, step, fun _ _ => by rw [mixes]⟩

/-- A proposer slashing is a step before votes. -/
private theorem beforeVotes_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    BeforeVotes state after :=
  BeforeVotes.of_mixes (frame_processProposerSlashing computed)
    (stepKeeps_processProposerSlashing computed)
    (payloadInputs_processProposerSlashing computed).randaoMixes

/-- An attester slashing is a step before votes. -/
private theorem beforeVotes_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    BeforeVotes state after :=
  BeforeVotes.of_mixes (frame_processAttesterSlashing computed)
    (stepKeeps_processAttesterSlashing computed)
    (payloadInputs_processAttesterSlashing computed).randaoMixes

/-- The header step is a step before votes. -/
private theorem beforeVotes_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) : BeforeVotes state after :=
  BeforeVotes.of_mixes (frame_processBlockHeader computed) (stepKeeps_processBlockHeader computed)
    (payloadInputs_processBlockHeader computed).randaoMixes

/-- The RANDAO step is a step before votes. -/
private theorem beforeVotes_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) : BeforeVotes state after :=
  ⟨frame_processRandao computed, stepKeeps_processRandao computed,
    mixesKeptBut_processRandao computed⟩

/-- The vote on the deposit contract is a step before votes. -/
private theorem beforeVotes_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) : BeforeVotes state after :=
  BeforeVotes.of_mixes (frame_processEth1Data computed) (stepKeeps_processEth1Data computed)
    (payloadInputs_processEth1Data computed).randaoMixes

/-- Where a list of attestations starts, each has the attesters of an earlier state.

The start must have the slot of the earlier state, and keep its activity up to its current epoch.

Of the RANDAO mixes, the start may differ from it at most at the one of its current epoch.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
theorem getAttestingIndices_eq_of_foldlM {first last : BeaconState preset fork}
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (slotEq : first.slot = state.slot) (active : ActiveKept (getCurrentEpoch state) state first)
    (mixes : MixesKeptBut (getCurrentEpoch state) state first)
    {parentSlot : Slot} {attestations : List (Attestation preset fork)}
    (attested :
      attestations.foldlM (processAttestation config checks · parentSlot ·) first = .ok last) :
    ∀ attestation ∈ attestations,
      getAttestingIndices first attestation = getAttestingIndices state attestation := by
  intro attestation member
  -- The fold runs the attestation at a state with the slot of the earlier state.
  obtain ⟨index, bound, found⟩ := List.getElem_of_mem member
  obtain ⟨mid, _, prefixOk, ok, -⟩ := (foldlM_ok_steps (fun _ _ => True) (fun _ => trivial)
    (fun _ _ => trivial) (fun _ _ _ _ => trivial) attested).2 index bound
  rw [found] at ok
  have slot : mid.slot = state.slot :=
    foldlM_ok_invariant (fun next : BeaconState preset fork => next.slot = state.slot)
      (fun _ _ _ holds ok => (frame_processAttestation ok).slot.trans holds) slotEq prefixOk
  have current : getCurrentEpoch mid = getCurrentEpoch state := by
    simp only [getCurrentEpoch, slot]
  have previous : getPreviousEpoch mid = getPreviousEpoch state := by
    simp only [getPreviousEpoch, current]
  have previousNat := getPreviousEpoch_toNat state
  have recent := processAttestation_slotEpoch ok
  rw [previous, current] at recent
  have low : computeEpochAtSlot preset attestation.data.slot ≤ getCurrentEpoch state := by
    rcases recent with same | same <;> rw [same]
    · exact getPreviousEpoch_le state
    · exact UInt64.le_refl _
  have high : (getCurrentEpoch state).toNat ≤
      (computeEpochAtSlot preset attestation.data.slot).toNat + 1 := by
    rcases recent with same | same <;> rw [same] <;> omega
  exact getAttestingIndices_eq_of_activeKept apart (active.mono low) mixes low high

/-- The steps of a block before its attestations are a step before votes. -/
private theorem beforeVotes_attestationsStart {engine : ExecutionEngine preset fork}
    {state input proposersDone first : BeaconState preset fork}
    {block : BeaconBlock preset fork}
    (started : OperationsInput config checks engine state block input)
    (proposers : block.body.proposerSlashings.data.toList.foldlM
      (processProposerSlashing config checks) input = .ok proposersDone)
    (slashings : block.body.attesterSlashings.data.toList.foldlM
      (processAttesterSlashing config checks) proposersDone = .ok first) :
    BeforeVotes state first :=
  (started.step_of BeforeVotes BeforeVotes.refl BeforeVotes.trans
    (fun _ ok => BeforeVotes.of_mixes (frame_processParentExecutionPayload ok)
      (stepKeeps_processParentExecutionPayload ok)
      (payloadInputs_processParentExecutionPayload ok).randaoMixes)
    beforeVotes_processBlockHeader
    (fun _ ok => BeforeVotes.of_mixes (frame_processBlockExecution ok)
      (stepKeeps_processBlockExecution ok) (randaoMixes_processBlockExecution ok))
    beforeVotes_processRandao (fun _ ok => beforeVotes_processEth1Data ok)).trans <|
    (foldlM_ok_steps BeforeVotes BeforeVotes.refl BeforeVotes.trans
      (fun _ _ _ ok => beforeVotes_processProposerSlashing ok) proposers).1.trans <|
    (foldlM_ok_steps BeforeVotes BeforeVotes.refl BeforeVotes.trans
      (fun _ _ _ ok => beforeVotes_processAttesterSlashing ok) slashings).1

/-- Where the attestations of a block start, each has the attesters of the state before it.

The start is the state after the operations input and the slashings of the block.

The attestations succeed when they are processed in order from that start.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
theorem getAttestingIndices_attestationsStart
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {engine : ExecutionEngine preset fork} {state : BeaconState preset fork}
    {block : BeaconBlock preset fork}
    {input proposersDone first last : BeaconState preset fork}
    (started : OperationsInput config checks engine state block input)
    (proposers : block.body.proposerSlashings.data.toList.foldlM
      (processProposerSlashing config checks) input = .ok proposersDone)
    (slashings : block.body.attesterSlashings.data.toList.foldlM
      (processAttesterSlashing config checks) proposersDone = .ok first)
    (attested : block.body.attestations.data.toList.foldlM
      (processAttestation config checks · state.latestBlockHeader.slot ·) first = .ok last)
    {attestation : Attestation preset fork}
    (member : attestation ∈ block.body.attestations.data.toList) :
    getAttestingIndices first attestation = getAttestingIndices state attestation :=
  let head := beforeVotes_attestationsStart started proposers slashings
  getAttestingIndices_eq_of_foldlM apart head.frame.slot
    (head.step.2.2.mono (getCurrentEpoch_le_activityFixedEpoch _)) head.mixes attested
    attestation member

/-- A block runs its attestations in order, between two block frames.

Where they start, the attesters of each of them are those of the state before the block.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
theorem processBlock_attestationSplit
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ∃ first last, BlockFrame state first ∧
      (∀ attestation ∈ block.body.attestations.data,
        getAttestingIndices first attestation = getAttestingIndices state attestation) ∧
      block.body.attestations.data.toList.foldlM
        (processAttestation config checks · state.latestBlockHeader.slot ·) first = .ok last ∧
      BlockFrame last after := by
  obtain ⟨input, proposersDone, first, last, started, proposers, slashings, attested, tail⟩ :=
    processBlock_folds computed
  exact ⟨first, last, (beforeVotes_attestationsStart started proposers slashings).frame,
    fun _ member => getAttestingIndices_attestationsStart apart started proposers slashings
      attested (Array.mem_toList_iff.mpr member), attested, tail⟩

/-- One slot keeps activity up to the current epoch plus `MAX_SEED_LOOKAHEAD`, at every fork. -/
theorem activeKept_advanceSlot
    (computed : advanceSlot config checks state = .ok after) :
    ActiveKept (activityFixedEpoch state) state after :=
  (advanceSlot_kept computed).2

/-- An upgrade keeps activity in each epoch up to the current epoch plus `MAX_SEED_LOOKAHEAD`. -/
theorem activeKept_upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) :
    ActiveKept (activityFixedEpoch pre.state) pre.state post.val.state := by
  obtain ⟨fork, state⟩ := pre
  cases fork
  case phase0 =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact ActiveKept.of_validators (upgradeToAltair_spec upgraded).1 _
  case altair | bellatrix | shapella =>
    simp only [upgradeNext, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ActiveKept.of_validators rfl _
  case dencun =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact activeKept_upgradeToElectra upgraded
  case pectra =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact ActiveKept.of_validators (upgradeToFulu_spec upgraded).1 _
  case fusaka =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    exact ActiveKept.of_validators (upgradeToGloas_spec upgraded).1 _
  case glamsterdam =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact ActiveKept.of_validators (upgradeHezeFields_lists _).1 _
  all_goals
    simp only [upgradeNext] at computed
    cases computed

/-- One step of a chain never shrinks the registry, nor moves the current epoch back.

It keeps activity. -/
private theorem chainStep_kept {forked after : ForkedBeaconState preset}
    (step : ChainStep config checks forked after) :
    forked.state.validators.data.size ≤ after.state.validators.data.size ∧
      ActiveKept (activityFixedEpoch forked.state) forked.state after.state ∧
      getCurrentEpoch forked.state ≤ getCurrentEpoch after.state := by
  cases step with
  | slot computed =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
    -- The upgrades keep the slot, the registry and activity.
    obtain ⟨grows, active, slot⟩ := processUpgrades_induction
      (property := fun upgraded =>
        advanced.validators.data.size ≤ upgraded.state.validators.data.size ∧
          ActiveKept (activityFixedEpoch advanced) advanced upgraded.state ∧
          upgraded.state.slot = advanced.slot)
      (fun {pre} _ ⟨grows, active, slot⟩ stepOk => by
        have frame := upgradeFrame_upgradeNext stepOk
        have epoch : activityFixedEpoch pre.state = activityFixedEpoch advanced :=
          activityFixedEpoch_eq_of_slot slot
        exact ⟨Nat.le_trans grows frame.registryGrows,
          active.trans (epoch ▸ activeKept_upgradeNext stepOk), frame.slot.trans slot⟩)
      ⟨Nat.le_refl _, ActiveKept.refl _ _, rfl⟩ upgraded
    obtain ⟨advancedGrows, advancedActive⟩ := advanceSlot_kept advancedOk
    -- The slot moves on by one, so the current epoch does not move back.
    have later : getCurrentEpoch forked.state ≤ getCurrentEpoch advanced := by
      have sum := advanceSlot_slot advancedOk
      apply UInt64.le_iff_toNat_le.mpr
      rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, sum]
      exact Nat.div_le_div_right (Nat.le_succ _)
    have epoch : getCurrentEpoch after.state = getCurrentEpoch advanced := by
      simp only [getCurrentEpoch, slot]
    exact ⟨Nat.le_trans advancedGrows grows,
      advancedActive.trans (active.mono (activityFixedEpoch_mono later)), epoch ▸ later⟩
  | @block _ blockState blockAfter engine signed validateResult computed =>
    obtain ⟨-, blockOk, -⟩ := applySignedBlock_ok computed
    have kept := stepKeeps_processBlock blockOk
    have epoch : getCurrentEpoch blockAfter = getCurrentEpoch blockState := by
      simp only [getCurrentEpoch, (frame_processBlock blockOk).slot]
    exact ⟨kept.1, kept.2.2, UInt64.le_of_eq epoch.symm⟩

/-- A run of steps of a chain never shrinks the registry.

It keeps activity. -/
private theorem chainSteps_kept {first last : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) first last) :
    first.state.validators.data.size ≤ last.state.validators.data.size ∧
      ActiveKept (activityFixedEpoch first.state) first.state last.state := by
  induction steps using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨Nat.le_refl _, ActiveKept.refl _ _⟩
  | head step _ more =>
    obtain ⟨grows, active, later⟩ := chainStep_kept step
    exact ⟨Nat.le_trans grows more.1,
      active.trans (more.2.mono (activityFixedEpoch_mono later))⟩

/-- One step of a chain keeps activity up to the current epoch plus `MAX_SEED_LOOKAHEAD`. -/
theorem ChainStep.activeKept {forked after : ForkedBeaconState preset}
    (step : ChainStep config checks forked after) :
    ActiveKept (activityFixedEpoch forked.state) forked.state after.state :=
  (chainStep_kept step).2.1

/-- A run of steps of a chain keeps activity up to the fixed epoch of its start.

That is the current epoch of its start plus `MAX_SEED_LOOKAHEAD`. -/
theorem activeKept_of_chainSteps {first last : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) first last) :
    ActiveKept (activityFixedEpoch first.state) first.state last.state :=
  (chainSteps_kept steps).2

/-- One step of a chain does not move the current epoch back. -/
theorem ChainStep.currentEpoch_le {forked after : ForkedBeaconState preset}
    (step : ChainStep config checks forked after) :
    getCurrentEpoch forked.state ≤ getCurrentEpoch after.state :=
  (chainStep_kept step).2.2

/-- A run of steps of a chain does not move the current epoch back. -/
theorem currentEpoch_le_of_chainSteps {first last : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) first last) :
    getCurrentEpoch first.state ≤ getCurrentEpoch last.state := by
  induction steps with
  | refl => exact UInt64.le_refl _
  | tail _ step more => exact UInt64.le_trans more step.currentEpoch_le

/-- One step of a chain never shrinks the registry. -/
theorem ChainStep.registryGrows {forked after : ForkedBeaconState preset}
    (step : ChainStep config checks forked after) :
    forked.state.validators.data.size ≤ after.state.validators.data.size :=
  (chainStep_kept step).1

/-- A run of steps of a chain never shrinks the registry. -/
theorem registryGrows_of_chainSteps {first last : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) first last) :
    first.state.validators.data.size ≤ last.state.validators.data.size :=
  (chainSteps_kept steps).1

end EthLib.Consensus
