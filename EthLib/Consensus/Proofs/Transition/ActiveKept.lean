module

public import EthLib.Consensus.Proofs.Transition.Chain
public import EthLib.Consensus.Proofs.Transition.Committees
public import EthLib.Consensus.Proofs.Transition.PayloadInputs

/-!
# Proofs: the active validators of past epochs stay fixed along a chain

A validator is active in an epoch from its activation epoch, up to its exit epoch.

The state transition sets an activation or an exit epoch only after the current epoch.

An activation lands at the first epoch an activation may take, `MAX_SEED_LOOKAHEAD + 1` epochs on.

An exit lands there or later, by the exit queue or the consolidation queue.

From Electra, the exit and consolidation queues of [EIP-7251] give no epoch before that one.

A new validator has no activation epoch yet, so it is active in no epoch.

The theorems of a step still assume fewer than 2^64 validators, though no step needs it now.

So each step of a chain keeps which validators are active in each epoch up to its current epoch.

That holds at every fork, for slots, epochs, blocks and upgrades.

The current epoch never decreases along a chain.

So along a run of steps, the active sets of the epochs up to its first current epoch stay fixed.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#specification
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-! ## Steps below 2^64 validators -/

/-- A step that never shrinks the registry.

While the registry after it stays below 2^64 validators, it keeps the slot and activity. -/
private def StepBelow (state after : BeaconState preset fork) : Prop :=
  state.validators.data.size ≤ after.validators.data.size ∧
    (after.validators.data.size < 2 ^ 64 → ActiveStep state after)

private theorem StepBelow.refl (state : BeaconState preset fork) : StepBelow state state :=
  ⟨Nat.le_refl _, fun _ => ActiveStep.refl state⟩

private theorem StepBelow.trans {first second third : BeaconState preset fork}
    (one : StepBelow first second) (two : StepBelow second third) : StepBelow first third :=
  ⟨Nat.le_trans one.1 two.1, fun small =>
    (one.2 (Nat.lt_of_le_of_lt two.1 small)).trans (two.2 small)⟩

private theorem StepBelow.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (keeps : ∀ s x s', step s x = .ok s' → StepBelow s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : StepBelow state after :=
  foldlM_ok_invariant (StepBelow state) (fun _ _ _ before ok => before.trans (keeps _ _ _ ok))
    (StepBelow.refl state) computed

private theorem StepBelow.of_step (grows : state.validators.data.size ≤ after.validators.data.size)
    (step : ActiveStep state after) : StepBelow state after :=
  ⟨grows, fun _ => step⟩

private theorem StepBelow.of_validators
    (validators : after.validators.data = state.validators.data := by rfl)
    (slot : after.slot = state.slot := by rfl) : StepBelow state after :=
  ⟨Nat.le_of_eq (congrArg Array.size validators).symm, fun _ =>
    ActiveStep.of_validators validators slot⟩

/-! ## Mutators -/

private theorem stepBelow_setValidator {index : ValidatorIndex} {validator old : Validator}
    (found : getValidator state index = .ok old)
    (same : ∀ epoch ≤ getCurrentEpoch state,
      isActiveValidator validator epoch = isActiveValidator old epoch)
    (set : state.setValidator index validator = .ok after) : StepBelow state after :=
  StepBelow.of_step (Nat.le_of_eq (sameSizes_setValidator set).1.symm)
    (activeStep_setValidator found same set)

private theorem stepBelow_increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : StepBelow state after :=
  StepBelow.of_step (frame_increaseBalance computed).registryGrows
    (activeStep_increaseBalance computed)

private theorem stepBelow_decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : StepBelow state after :=
  StepBelow.of_step (frame_decreaseBalance computed).registryGrows
    (activeStep_decreaseBalance computed)

private theorem stepBelow_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) : StepBelow state after :=
  StepBelow.of_step (frame_initiateValidatorExit computed).registryGrows
    (activeStep_initiateValidatorExit computed)

private theorem stepBelow_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    StepBelow state after :=
  StepBelow.of_step (frame_slashValidator computed).registryGrows
    (activeStep_slashValidator computed)

private theorem stepBelow_addValidatorToRegistry {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    StepBelow state after :=
  StepBelow.of_step (frame_addValidatorToRegistry computed).registryGrows
    (activeStep_addValidatorToRegistry computed)

/-! ## Deposits -/

private theorem stepBelow_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    StepBelow state after := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact StepBelow.refl _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact stepBelow_addValidatorToRegistry computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ StepBelow.refl _
  · simp only [liftAccessor_ok, bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    exact stepBelow_increaseBalance computed

private theorem stepBelow_applyDepositElectra {electra : .pectra ≤ fork}
    {pubkey : Cryptography.Bls.BLSPubkey} {withdrawalCredentials : Bytes32} {amount : Gwei}
    {signature : Cryptography.Bls.BLSSignature}
    (computed : applyDepositElectra config checks state electra pubkey withdrawalCredentials
      amount signature = .ok after) :
    StepBelow state after := by
  unfold applyDepositElectra at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, added, pushed⟩ := computed
      obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
      exact (stepBelow_addValidatorToRegistry added).trans StepBelow.of_validators
    · cases computed
      exact StepBelow.refl _
  · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
    exact StepBelow.of_validators

private theorem stepBelow_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    StepBelow state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  refine (StepBelow.of_validators (state := state)
    (after := { state with eth1DepositIndex := fun _ => next })).trans ?_
  unfold applyDeposit at applied
  split at applied
  · exact stepBelow_applyDepositElectra applied
  · exact stepBelow_applyPendingDeposit applied

/-! ## Requests of the execution layer -/

private theorem stepBelow_processDepositRequest {electra : .pectra ≤ fork}
    {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    StepBelow state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact StepBelow.of_validators

private theorem stepBelow_requestPartialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    StepBelow state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    obtain ⟨-, validators, -⟩ := computeExitEpochAndUpdateChurn_earliest churned
    exact StepBelow.of_validators (by rw [validators])
      (frame_computeExitEpochAndUpdateChurn churned).slot
  · cases computed
    exact StepBelow.refl _

private theorem stepBelow_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    StepBelow state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact StepBelow.refl _)
    | exact stepBelow_initiateValidatorExit (liftAccessor_ok.mp computed)
    | exact stepBelow_requestPartialWithdrawal computed

private theorem stepBelow_queueExcessActiveBalance {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : queueExcessActiveBalance state electra index = .ok after) :
    StepBelow state after := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, set, rfl⟩ := computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact StepBelow.of_validators
  · cases computed
    exact StepBelow.refl _

/-- Compounding credentials keep the activation and the exit epoch. -/
private theorem stepBelow_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    StepBelow state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨validator, found, _, set, queued⟩ := computed
  exact (stepBelow_setValidator found (fun _ _ => by rfl) set).trans
    (stepBelow_queueExcessActiveBalance queued)

/-- A consolidation from Electra takes effect after the current epoch. -/
private theorem consolidationEpoch_lt {electra : .pectra ≤ fork} {balance : Gwei}
    {churned : BeaconState preset fork} {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (churned, epoch)) :
    (getCurrentEpoch state).toNat < epoch.toNat := by
  cases first : computeActivationExitEpoch preset (getCurrentEpoch state) with
  | error =>
    simp [computeConsolidationEpochAndUpdateChurn, first, liftArith, Except.mapError, bind,
      Except.bind] at computed
  | ok firstEpoch =>
    have early := UInt64.le_iff_toNat_le.mp
      (computeConsolidationEpochAndUpdateChurn_first first computed).1
    have firstEq := (computeActivationExitEpoch_ok_iff.mp first).2
    omega

/-- The source of a consolidation had not started to exit, and exits after the current epoch.

It must be the validator at its index. -/
private theorem stepBelow_queueConsolidation {electra : .pectra ≤ fork}
    {sourceIndex : ValidatorIndex} {source : Validator} {targetIndex : ValidatorIndex}
    (found : state.validators.data[sourceIndex.toNat]? = some source)
    (far : source.exitEpoch = FAR_FUTURE_EPOCH)
    (computed :
      queueConsolidation config state electra sourceIndex source targetIndex = .ok after) :
    StepBelow state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure] at computed
  obtain ⟨⟨churnedState, exitEpoch⟩, churned, withdrawable, ⟨_, sum⟩, _, set, _, _, computed⟩ :=
    computed
  simp only [Except.ok.injEq] at computed
  subst computed
  have later := consolidationEpoch_lt churned
  obtain ⟨-, validators, -⟩ := computeConsolidationEpochAndUpdateChurn_earliest churned
  have slot := (frame_computeConsolidationEpochAndUpdateChurn churned).slot
  have first : StepBelow state churnedState := StepBelow.of_validators (by rw [validators]) slot
  have found' : getValidator churnedState sourceIndex = .ok source := by
    rw [getValidator, validators, found]
  refine first.trans ((stepBelow_setValidator found' (fun _ le => ?_) set).trans
    StepBelow.of_validators)
  have epochEq : getCurrentEpoch churnedState = getCurrentEpoch state := by
    simp only [getCurrentEpoch, slot]
  exact isActiveValidator_eq_of_exit rfl far
    (by rw [epochEq]; exact UInt64.lt_iff_toNat_lt.mpr later) le

private theorem stepBelow_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    StepBelow state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals try first
    | (cases computed; done)
    | (cases computed; exact StepBelow.refl _)
    | exact stepBelow_switchToCompoundingValidator (liftAccessor_ok.mp computed)
  -- The source had not started to exit.
  rename_i bothFar _ _ _ _ _ _ _ _
  exact stepBelow_queueConsolidation (getElem?_toNat_of_ofNatChecked (by assumption))
    (beq_iff_eq.mp ((Bool.and_eq_true _ _).mp bothFar).1) computed

private theorem stepBelow_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    StepBelow state after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  exact (StepBelow.foldlM (fun _ _ _ ok => stepBelow_processDepositRequest ok) depositsOk).trans <|
    (StepBelow.foldlM (fun _ _ _ ok => stepBelow_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    StepBelow.foldlM (fun _ _ _ ok => stepBelow_processConsolidationRequest ok) consolidationsOk

/-! ## Withdrawals and the execution part of a block -/

private theorem stepBelow_applyWithdrawal {withdrawal : Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) : StepBelow state after := by
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, set⟩ := computed
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact StepBelow.of_validators
  · exact stepBelow_decreaseBalance computed

private theorem stepBelow_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    StepBelow state after := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : StepBelow state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact StepBelow.foldlM (fun _ _ _ ok => stepBelow_applyWithdrawal ok) appliedOk
  have indexedStep : StepBelow applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      exact StepBelow.of_validators
    · cases indexedOk
      exact StepBelow.refl _
  have queued : ∀ kept : BeaconState preset fork,
      StepBelow kept (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals kept gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else kept) := by
    intro kept
    split <;> exact StepBelow.of_validators
  have partials : ∀ kept : BeaconState preset fork,
      StepBelow kept (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals kept electra expected.processedPartialWithdrawalsCount
      else kept) := by
    intro kept
    split <;> exact StepBelow.of_validators
  have swept : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → StepBelow kept finished := by
    intro kept ok
    split at ok
    · unfold updateNextWithdrawalBuilderIndex at ok
      dsimp only at ok
      split at ok
      · cases ok
        exact StepBelow.of_validators
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
        obtain ⟨_, _, rfl⟩ := ok
        exact StepBelow.of_validators
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ StepBelow.refl _
  have lastStep : StepBelow finished after := by
    unfold updateNextWithdrawalValidatorIndex at last
    simp only [bind_ok_iff] at last
    obtain ⟨_, _, last⟩ := last
    split at last
    · cases last
    · cases last
      exact StepBelow.of_validators
  exact one.trans <| indexedStep.trans <| (queued _).trans <| (partials _).trans <|
    (swept _ sweptOk).trans lastStep

private theorem stepBelow_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) : StepBelow state after := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, applied⟩ := computed
      exact stepBelow_applyExpectedWithdrawals applied
    · cases computed
      exact StepBelow.refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact stepBelow_applyExpectedWithdrawals applied

private theorem stepBelow_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    StepBelow state after := by
  obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact stepBelow_setValidator found (fun _ _ => by simp only [isActiveValidator]) set

private theorem stepBelow_processExecutionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    StepBelow state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  exact StepBelow.of_validators

private theorem stepBelow_processBuilderDepositRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    StepBelow state after := by
  unfold processBuilderDepositRequest addBuilderToRegistry at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact StepBelow.of_validators)

private theorem stepBelow_processBuilderExitRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    StepBelow state after := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · exact StepBelow.refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact StepBelow.of_validators

private theorem stepBelow_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    StepBelow state after := by
  rcases processParentExecutionPayload_ok computed with ⟨-, -, rfl⟩ |
    ⟨-, settled, _, _, _, _, _, _, settledOk, depositsOk, withdrawalsOk, consolidationsOk,
      buildersOk, exitsOk, -, rfl⟩
  · exact StepBelow.refl _
  · have settledStep : StepBelow state settled := by
      rw [settleParentPayment_eq settledOk]
      exact StepBelow.of_validators
    exact settledStep.trans <|
      (StepBelow.foldlM (fun _ _ _ ok => stepBelow_processDepositRequest ok) depositsOk).trans <|
      (StepBelow.foldlM (fun _ _ _ ok => stepBelow_processWithdrawalRequest ok)
        withdrawalsOk).trans <|
      (StepBelow.foldlM (fun _ _ _ ok => stepBelow_processConsolidationRequest ok)
        consolidationsOk).trans <|
      (StepBelow.foldlM (fun _ _ _ ok => stepBelow_processBuilderDepositRequest ok)
        buildersOk).trans <|
      (StepBelow.foldlM (fun _ _ _ ok => stepBelow_processBuilderExitRequest ok) exitsOk).trans
        StepBelow.of_validators

private theorem stepBelow_processExecutionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    StepBelow state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok computed
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact StepBelow.of_validators
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at recordedOk
    subst recordedOk
    exact StepBelow.of_validators

private theorem stepBelow_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    StepBelow state after := by
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    exact (stepBelow_processWithdrawals withdrawnOk).trans
      (stepBelow_processExecutionPayloadBid bid)
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact (stepBelow_processWithdrawals withdrawnOk).trans (stepBelow_processExecutionPayload paid)
  · dsimp only at computed
    split at computed
    · exact stepBelow_processExecutionPayload computed
    · cases computed
      exact StepBelow.refl _

private theorem stepBelow_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    StepBelow state after := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  refine StepBelow.foldlM (fun _ _ _ ok => ?_) folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    exact (stepBelow_increaseBalance raised).trans (stepBelow_increaseBalance paid)
  · exact stepBelow_decreaseBalance (liftAccessor_ok.mp ok)

/-! ## The other steps of a block -/

private theorem stepBelow_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) : StepBelow state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact StepBelow.of_validators

private theorem stepBelow_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) : StepBelow state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact StepBelow.of_validators

private theorem stepBelow_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) : StepBelow state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  rw [← rest]
  exact StepBelow.of_validators

private theorem stepBelow_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    StepBelow state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact stepBelow_slashValidator slashed

private theorem stepBelow_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    StepBelow state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  refine foldlM_ok_invariant (fun step => StepBelow state step.1)
    (fun step _ next before ok => before.trans ?_)
    (show StepBelow state (state, false).1 from StepBelow.refl state) folded
  obtain ⟨middle, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact stepBelow_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at ok
    exact ok ▸ StepBelow.refl _

private theorem stepBelow_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    StepBelow state after :=
  StepBelow.of_validators (by rw [(processAttestation_registry computed).1])
    (frame_processAttestation computed).slot

private theorem stepBelow_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    StepBelow state after := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact stepBelow_initiateValidatorExit exited

/-! ## Blocks -/

private theorem stepBelow_processOperations {body : BeaconBlockBody preset fork}
    {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    StepBelow state after := by
  unfold processOperations at computed
  split at computed
  · unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
    exact (StepBelow.foldlM (fun _ _ _ ok => stepBelow_processProposerSlashing ok)
      proposersOk).trans <|
      (StepBelow.foldlM (fun _ _ _ ok => stepBelow_processAttesterSlashing ok) attestersOk).trans <|
      (StepBelow.foldlM (fun _ _ _ ok => stepBelow_processAttestation ok) attestedOk).trans <|
      (StepBelow.foldlM (fun _ _ _ ok => stepBelow_processVoluntaryExit ok) exitsOk).trans <|
      (StepBelow.foldlM (fun _ _ _ ok => stepBelow_processBlsToExecutionChange ok)
        changesOk).trans <|
      StepBelow.foldlM (fun _ _ _ ok => by
        rw [processPayloadAttestation_eq ok]
        exact StepBelow.refl _) paid
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, exited,
    exitsOk, changed, changesOk, requestsOk⟩ := computed
  have changes : StepBelow exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact StepBelow.foldlM (fun _ _ _ ok => stepBelow_processBlsToExecutionChange ok) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ StepBelow.refl _
  have requests : StepBelow changed after := by
    split at requestsOk
    · exact stepBelow_processExecutionRequests requestsOk
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact requestsOk ▸ StepBelow.refl _
  exact (StepBelow.foldlM (fun _ _ _ ok => stepBelow_processProposerSlashing ok)
    proposersOk).trans <|
    (StepBelow.foldlM (fun _ _ _ ok => stepBelow_processAttesterSlashing ok) attestersOk).trans <|
    (StepBelow.foldlM (fun _ _ _ ok => stepBelow_processAttestation ok) attestedOk).trans <|
    (StepBelow.foldlM (fun _ _ _ ok => stepBelow_processDeposit ok) depositedOk).trans <|
    (StepBelow.foldlM (fun _ _ _ ok => stepBelow_processVoluntaryExit ok) exitsOk).trans <|
    changes.trans requests

private theorem stepBelow_processBlock {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    StepBelow state after := by
  unfold processBlock at computed
  split at computed
  · unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, _, operatedOk, synced⟩ := computed
    have paidStep : StepBelow state paid := by
      split at paidOk
      · exact stepBelow_processParentExecutionPayload paidOk
      · cases paidOk
        exact StepBelow.refl _
    have executedStep : StepBelow headed executed := by
      split at executedOk
      · exact stepBelow_processBlockExecution executedOk
      · cases executedOk
        exact StepBelow.refl _
    have votedStep : StepBelow revealed voted := by
      split at votedOk
      · exact stepBelow_processEth1Data votedOk
      · cases votedOk
        exact StepBelow.refl _
    exact paidStep.trans <| (stepBelow_processBlockHeader headedOk).trans <|
      executedStep.trans <| (stepBelow_processRandao revealedOk).trans <| votedStep.trans <|
      (stepBelow_processOperations operatedOk).trans (stepBelow_processSyncAggregate synced)
  simp only [bind_ok_iff] at computed
  obtain ⟨_, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := computed
  exact (stepBelow_processBlockHeader headerOk).trans <| (stepBelow_processRandao randaoOk).trans <|
    (stepBelow_processEth1Data eth1Ok).trans (stepBelow_processOperations operationsOk)

/-! ## The steps of an epoch -/

private theorem stepBelow_processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) :
    StepBelow state after :=
  StepBelow.of_step
    (by rw [(processJustificationAndFinalization_keeps computed).2.2.2.2.2.1]; exact Nat.le_refl _)
    (activeStep_processJustificationAndFinalization computed)

private theorem stepBelow_processInactivityUpdates {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) :
    StepBelow state after := by
  unfold processInactivityUpdates at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ StepBelow.refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact StepBelow.of_validators

/-- From Electra, the registry updates of one validator keep activity up to the current epoch.

An activation goes to an epoch after the current epoch, and only from the far future. -/
private theorem stepBelow_updateRegistryEntryElectra {activationEpoch : Epoch} {index : Nat}
    (later : (getCurrentEpoch state).toNat < activationEpoch.toNat)
    (computed : updateRegistryEntryElectra config activationEpoch state index = .ok after) :
    StepBelow state after := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, set⟩ := computed
    exact stepBelow_setValidator found (fun _ _ => by simp only [isActiveValidator]) set
  split at computed
  · exact stepBelow_initiateValidatorExit (liftAccessor_ok.mp computed)
  split at computed
  · rename_i eligible
    simp only [isEligibleForActivation, Bool.and_eq_true, beq_iff_eq] at eligible
    -- Neither the far-future epoch nor the new one is at or before the current epoch.
    exact stepBelow_setValidator found (fun _ le => isActiveValidator_eq_of_activation
      (.inl eligible.2) (UInt64.lt_iff_toNat_lt.mpr later) le) (liftAccessor_ok.mp computed)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ StepBelow.refl _

private theorem stepBelow_processRegistryUpdates
    (computed : processRegistryUpdates config state = .ok after) : StepBelow state after := by
  have grows := (frame_processRegistryUpdates computed).registryGrows
  by_cases electra : Fork.pectra ≤ fork
  · unfold processRegistryUpdates at computed
    simp only [electra, ↓reduceIte, bind_ok_iff, liftAccessor_ok, liftArith,
      mapError_ok_iff] at computed
    obtain ⟨activationEpoch, activationOk, computed⟩ := computed
    have activationEq := (computeActivationExitEpoch_ok_iff.mp activationOk).2
    -- Each step keeps the slot, so the activation epoch stays after the current epoch.
    refine (foldlM_ok_invariant (fun middle => StepBelow state middle ∧ middle.slot = state.slot)
      (fun middle _ next before ok => ⟨before.1.trans
        (stepBelow_updateRegistryEntryElectra ?_ ok),
        (frame_updateRegistryEntryElectra ok).slot.trans before.2⟩)
      ⟨StepBelow.refl state, rfl⟩ computed).1
    have epoch : getCurrentEpoch middle = getCurrentEpoch state := by
      simp only [getCurrentEpoch, before.2]
    rw [epoch, activationEq]
    omega
  · exact StepBelow.of_step grows
      (activeStep_processRegistryUpdates (Nat.lt_of_not_le electra) computed)

private theorem stepBelow_passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      StepBelow state pass.1.state
  | [], _, _, _, _, _, computed => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact StepBelow.refl _
  | deposit :: rest, state, processed, count, postponed, pass, computed => by
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      exact StepBelow.refl _
    split at computed
    · split at computed
      · cases computed
      rename_i credited
      split at computed
      · cases computed
      cases computed
      exact (stepBelow_applyPendingDeposit credited).trans
        (stepBelow_passPendingDeposits (deposits := rest) ‹_›)
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact stepBelow_passPendingDeposits (deposits := rest) ‹_›
    split at computed
    · cases computed
    split at computed
    · cases computed
      exact StepBelow.refl _
    split at computed
    · cases computed
    rename_i credited
    split at computed
    · cases computed
    cases computed
    exact (stepBelow_applyPendingDeposit credited).trans
      (stepBelow_passPendingDeposits (deposits := rest) ‹_›)

private theorem stepBelow_processPendingBalances
    (computed : processPendingBalances config checks state = .ok after) :
    StepBelow state after := by
  unfold processPendingBalances at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨middle, deposited, consolidated⟩ := computed
    have deposits : StepBelow state middle := by
      unfold processPendingDeposits at deposited
      simp only [bind, Except.bind, pure, Except.pure] at deposited
      repeat' (split at deposited <;> try cases deposited)
      all_goals
        exact (stepBelow_passPendingDeposits ‹_›).trans StepBelow.of_validators
    exact deposits.trans (StepBelow.of_validators
      (by rw [(processPendingConsolidations_kept consolidated).1])
      (frame_processPendingConsolidations consolidated).slot)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ StepBelow.refl _

private theorem stepBelow_epochTail {altair : .altair ≤ fork}
    {rooted synced looked : BeaconState preset fork}
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair)
      altair = .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) : StepBelow rooted after := by
  have syncedStep : StepBelow (processParticipationFlagUpdates rooted altair) synced := by
    unfold processSyncCommitteeUpdates at syncedOk
    simp only [bind, Except.bind, pure, Except.pure] at syncedOk
    repeat' (split at syncedOk <;> try cases syncedOk)
    all_goals exact StepBelow.refl _
  have lookedStep : StepBelow synced looked := by
    split at lookedOk
    · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at lookedOk
      obtain ⟨_, _, _, _, rfl⟩ := lookedOk
      exact StepBelow.of_validators
    · simp only [pure, Except.pure, Except.ok.injEq] at lookedOk
      exact lookedOk ▸ StepBelow.refl _
  have windowedStep : StepBelow looked after := by
    split at windowed
    · simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at windowed
      obtain ⟨_, _, _, _, rfl⟩ := windowed
      exact StepBelow.of_validators
    · simp only [pure, Except.pure, Except.ok.injEq] at windowed
      exact windowed ▸ StepBelow.refl _
  exact (StepBelow.of_validators : StepBelow rooted _).trans <| syncedStep.trans <|
    lookedStep.trans windowedStep

private theorem stepBelow_processEpochAltair {altair : .altair ≤ fork}
    (computed : processEpochAltair config checks state altair = .ok after) :
    StepBelow state after := by
  unfold processEpochAltair at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
    registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk, balanced,
    balancedOk, cleared, clearedOk, mixed, mixedOk, computed⟩ := computed
  have resetStep : StepBelow slashed reset := by
    split at resetOk
    · exact StepBelow.of_step (frame_processEth1DataReset resetOk).registryGrows
        (activeStep_processEth1DataReset resetOk)
    · simp only [pure, Except.pure, Except.ok.injEq] at resetOk
      exact resetOk ▸ StepBelow.refl _
  have paidStep : StepBelow pending paid := by
    split at paidOk
    · simp only [processBuilderPendingPayments, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at paidOk
      obtain ⟨_, _, rfl⟩ := paidOk
      exact StepBelow.of_validators
    · simp only [pure, Except.pure, Except.ok.injEq] at paidOk
      exact paidOk ▸ StepBelow.refl _
  have mixedStep : StepBelow cleared mixed := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    exact StepBelow.of_validators
  have head : StepBelow state mixed :=
    (stepBelow_processJustificationAndFinalization justifiedOk).trans <|
    (stepBelow_processInactivityUpdates scoredOk).trans <|
    (StepBelow.of_step (frame_processRewardsAndPenalties rewardedOk).registryGrows
      (activeStep_processRewardsAndPenalties rewardedOk)).trans <|
    (stepBelow_processRegistryUpdates registeredOk).trans <|
    (StepBelow.of_step (frame_processSlashings slashedOk).registryGrows
      (activeStep_processSlashings slashedOk)).trans <|
    resetStep.trans <|
    (stepBelow_processPendingBalances pendingOk).trans <|
    paidStep.trans <|
    (StepBelow.of_step (frame_processEffectiveBalanceUpdates balancedOk).registryGrows
      (activeStep_processEffectiveBalanceUpdates balancedOk)).trans <|
    (StepBelow.of_step (frame_processSlashingsReset clearedOk).registryGrows
      (activeStep_processSlashingsReset clearedOk)).trans mixedStep
  split at computed <;> simp only [bind_ok_iff] at computed <;>
    obtain ⟨rooted, rootedOk, synced, syncedOk, looked, lookedOk, windowed⟩ := computed
  · have rootedStep : StepBelow mixed rooted := by
      unfold processHistoricalSummariesUpdate at rootedOk
      simp only [bind, Except.bind, pure, Except.pure] at rootedOk
      repeat' (split at rootedOk <;> try cases rootedOk)
      all_goals exact StepBelow.refl _
    exact head.trans <| rootedStep.trans (stepBelow_epochTail syncedOk lookedOk windowed)
  · exact head.trans <|
      (StepBelow.of_step (frame_processHistoricalRootsUpdate rootedOk).registryGrows
        (activeStep_processHistoricalRootsUpdate rootedOk)).trans
      (stepBelow_epochTail syncedOk lookedOk windowed)

/-- The epoch step keeps activity in each epoch up to its current epoch, at every fork.

The registry after it must hold fewer than 2^64 validators. -/
theorem activeKept_processEpoch
    (small : after.validators.data.size < 2 ^ 64)
    (computed : processEpoch config checks state = .ok after) :
    ActiveKept (getCurrentEpoch state) state after := by
  by_cases altair : Fork.altair ≤ fork
  · simp only [processEpoch, altair, ↓reduceDIte] at computed
    exact ((stepBelow_processEpochAltair computed).2 small).2
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

While the registry after it stays below 2^64 validators, it keeps activity. -/
private theorem advanceSlot_kept (computed : advanceSlot config checks state = .ok after) :
    state.validators.data.size ≤ after.validators.data.size ∧
      (after.validators.data.size < 2 ^ 64 →
        ActiveKept (getCurrentEpoch state) state after) := by
  obtain ⟨next, cached, epoched, -, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  -- The slot step writes neither the registry nor the slot.
  have validators : cached.validators = state.validators := by rw [cachedEq]
  have epoch : getCurrentEpoch cached = getCurrentEpoch state := by
    simp only [getCurrentEpoch, cachedEq]
  have first : ActiveKept (getCurrentEpoch state) state cached :=
    ActiveKept.of_validators (by rw [validators]) _
  suffices kept : cached.validators.data.size ≤ epoched.validators.data.size ∧
      (epoched.validators.data.size < 2 ^ 64 →
        ActiveKept (getCurrentEpoch cached) cached epoched) by
    refine ⟨validators ▸ kept.1, fun small => first.trans ?_⟩
    exact (epoch ▸ kept.2 small).trans (ActiveKept.of_validators rfl _)
  unfold epochIfLast at epochedOk
  split at epochedOk
  · exact ⟨processEpoch_registryGrows epochedOk, fun small =>
      activeKept_processEpoch small epochedOk⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    exact ⟨Nat.le_refl _, fun _ => ActiveKept.refl _ _⟩

/-- Queueing a validator that is not yet active keeps its activation and exit epochs. -/
private theorem stepBelow_queuePreActivation {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queuePreActivation state electra index = .ok after) : StepBelow state after := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨validator, found, _, -, _, -, _, set₁, _, set₂, rfl⟩ := computed
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  exact ((StepBelow.of_validators : StepBelow state _).trans
    (stepBelow_setValidator (by exact found) (fun _ _ => by simp only [isActiveValidator])
      set₂)).trans StepBelow.of_validators

private theorem stepBelow_queueCompoundingExcess {electra : .pectra ≤ fork} {index : Nat}
    (computed : queueCompoundingExcess state electra index = .ok after) :
    StepBelow state after := by
  unfold queueCompoundingExcess at computed
  split at computed
  · split at computed
    · exact stepBelow_queueExcessActiveBalance (liftAccessor_ok.mp computed)
    · cases computed
      exact StepBelow.refl _
  · cases computed
    exact StepBelow.refl _

/-- The upgrade to Electra keeps activity up to the current epoch. -/
private theorem activeKept_upgradeToElectra {pre : BeaconState preset .dencun}
    {post : BeaconState preset .pectra} (computed : upgradeToElectra config pre = .ok post) :
    ActiveKept (getCurrentEpoch pre) pre post := by
  simp only [upgradeToElectra, bind_ok_iff] at computed
  obtain ⟨_, -, _, -, _, -, _, -, middle, queued, compounded⟩ := computed
  have step := (StepBelow.foldlM (fun _ _ _ ok => stepBelow_queuePreActivation ok) queued).trans
    (StepBelow.foldlM (fun _ _ _ ok => stepBelow_queueCompoundingExcess ok) compounded)
  exact (ActiveKept.of_validators rfl _).trans
    (step.2 (BeaconState.validators_size_lt_of_lt_glamsterdam (by decide) _)).2

/-- A block keeps activity in each epoch up to its current epoch, at every fork.

The registry after it must hold fewer than 2^64 validators. -/
theorem activeKept_processBlock {block : BeaconBlock preset fork}
    (small : after.validators.data.size < 2 ^ 64)
    (computed : processBlock config checks engine state block = .ok after) :
    ActiveKept (getCurrentEpoch state) state after :=
  ((stepBelow_processBlock computed).2 small).2

/-! ## The attestations of a block -/

/-- A step of a block before its attestations.

It is a block frame, and it never shrinks the registry.

While the registry after it stays below 2^64 validators, it keeps the slot and activity.

Of the RANDAO mixes, it writes at most the one of the current epoch. -/
private structure BeforeVotes (state after : BeaconState preset fork) : Prop where
  frame : BlockFrame state after
  step : StepBelow state after
  mixes : MixesKeptBut (getCurrentEpoch state) state after

/-- Every state is a step before votes to itself. -/
private theorem BeforeVotes.refl (state : BeaconState preset fork) : BeforeVotes state state :=
  ⟨BlockFrame.refl state, StepBelow.refl state, fun _ _ => rfl⟩

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
    (step : StepBelow state after) (mixes : after.randaoMixes = state.randaoMixes) :
    BeforeVotes state after :=
  ⟨frame, step, fun _ _ => by rw [mixes]⟩

/-- A proposer slashing is a step before votes. -/
private theorem beforeVotes_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    BeforeVotes state after :=
  BeforeVotes.of_mixes (frame_processProposerSlashing computed)
    (stepBelow_processProposerSlashing computed)
    (payloadInputs_processProposerSlashing computed).randaoMixes

/-- An attester slashing is a step before votes. -/
private theorem beforeVotes_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    BeforeVotes state after :=
  BeforeVotes.of_mixes (frame_processAttesterSlashing computed)
    (stepBelow_processAttesterSlashing computed)
    (payloadInputs_processAttesterSlashing computed).randaoMixes

/-- The header step is a step before votes. -/
private theorem beforeVotes_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) : BeforeVotes state after :=
  BeforeVotes.of_mixes (frame_processBlockHeader computed) (stepBelow_processBlockHeader computed)
    (payloadInputs_processBlockHeader computed).randaoMixes

/-- The RANDAO step is a step before votes. -/
private theorem beforeVotes_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) : BeforeVotes state after :=
  ⟨frame_processRandao computed, stepBelow_processRandao computed,
    mixesKeptBut_processRandao computed⟩

/-- The vote on the deposit contract is a step before votes. -/
private theorem beforeVotes_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) : BeforeVotes state after :=
  BeforeVotes.of_mixes (frame_processEth1Data computed) (stepBelow_processEth1Data computed)
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

/-- A block runs its attestations in order, between two block frames.

Where they start, the attesters of each of them are those of the state before the block.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes.

The registry after the block must hold fewer than 2^64 validators. -/
theorem processBlock_attestationSplit
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {block : BeaconBlock preset fork} (small : after.validators.data.size < 2 ^ 64)
    (computed : processBlock config checks engine state block = .ok after) :
    ∃ first last, BlockFrame state first ∧
      (∀ attestation ∈ block.body.attestations.data,
        getAttestingIndices first attestation = getAttestingIndices state attestation) ∧
      block.body.attestations.data.toList.foldlM
        (processAttestation config checks · state.latestBlockHeader.slot ·) first = .ok last ∧
      BlockFrame last after := by
  obtain ⟨operatedFirst, operatedLast, blockHead, operated, blockTail⟩ :=
    processBlock_split_of BeforeVotes BeforeVotes.refl BeforeVotes.trans
      (fun _ ok => BeforeVotes.of_mixes (frame_processParentExecutionPayload ok)
        (stepBelow_processParentExecutionPayload ok)
        (payloadInputs_processParentExecutionPayload ok).randaoMixes)
      beforeVotes_processBlockHeader
      (fun _ ok => BeforeVotes.of_mixes (frame_processBlockExecution ok)
        (stepBelow_processBlockExecution ok) (randaoMixes_processBlockExecution ok))
      beforeVotes_processRandao (fun _ ok => beforeVotes_processEth1Data ok) computed
  obtain ⟨first, last, operationsHead, attested, operationsTail⟩ :=
    processOperations_split_of BeforeVotes BeforeVotes.refl BeforeVotes.trans
      beforeVotes_processProposerSlashing beforeVotes_processAttesterSlashing operated
  have head := blockHead.trans operationsHead
  have tail := operationsTail.trans blockTail
  -- The attestations keep the registry, so the registry where they start is below 2^64.
  have kept : last.validators = first.validators :=
    foldlM_ok_invariant (fun next : BeaconState preset fork => next.validators = first.validators)
      (fun _ _ _ holds ok => (processAttestation_registry ok).1.trans holds) rfl attested
  have below : first.validators.data.size < 2 ^ 64 := by
    rw [← kept]
    exact Nat.lt_of_le_of_lt tail.registryGrows small
  have active := (head.step.2 below).2
  exact ⟨first, last, head.frame, fun attestation member =>
    getAttestingIndices_eq_of_foldlM apart head.frame.slot active head.mixes attested attestation
      (Array.mem_toList_iff.mpr member), attested, tail⟩

/-- One slot keeps activity in each epoch up to its current epoch, at every fork.

The registry after it must hold fewer than 2^64 validators. -/
theorem activeKept_advanceSlot (small : after.validators.data.size < 2 ^ 64)
    (computed : advanceSlot config checks state = .ok after) :
    ActiveKept (getCurrentEpoch state) state after :=
  (advanceSlot_kept computed).2 small

/-- An upgrade keeps activity in each epoch up to its current epoch. -/
theorem activeKept_upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) :
    ActiveKept (getCurrentEpoch pre.state) pre.state post.val.state := by
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

While the registry after it stays below 2^64 validators, it keeps activity. -/
private theorem chainStep_kept {forked after : ForkedBeaconState preset}
    (step : ChainStep config checks forked after) :
    forked.state.validators.data.size ≤ after.state.validators.data.size ∧
      (after.state.validators.data.size < 2 ^ 64 →
        ActiveKept (getCurrentEpoch forked.state) forked.state after.state) ∧
      getCurrentEpoch forked.state ≤ getCurrentEpoch after.state := by
  cases step with
  | slot computed =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
    -- The upgrades keep the slot, the registry and activity.
    obtain ⟨grows, active, slot⟩ := processUpgrades_induction
      (property := fun upgraded =>
        advanced.validators.data.size ≤ upgraded.state.validators.data.size ∧
          ActiveKept (getCurrentEpoch advanced) advanced upgraded.state ∧
          upgraded.state.slot = advanced.slot)
      (fun {pre} _ ⟨grows, active, slot⟩ stepOk => by
        have frame := upgradeFrame_upgradeNext stepOk
        have epoch : getCurrentEpoch pre.state = getCurrentEpoch advanced := by
          simp only [getCurrentEpoch, slot]
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
    refine ⟨Nat.le_trans advancedGrows grows, fun small => ?_, epoch ▸ later⟩
    exact (advancedActive (Nat.lt_of_le_of_lt grows small)).trans (active.mono later)
  | @block _ blockState blockAfter engine signed validateResult computed =>
    obtain ⟨-, blockOk, -⟩ := applySignedBlock_ok computed
    have kept := stepBelow_processBlock blockOk
    have epoch : getCurrentEpoch blockAfter = getCurrentEpoch blockState := by
      simp only [getCurrentEpoch, (frame_processBlock blockOk).slot]
    exact ⟨kept.1, fun small => (kept.2 small).2, UInt64.le_of_eq epoch.symm⟩

/-- A run of steps of a chain never shrinks the registry.

While the registry at its end stays below 2^64 validators, it keeps activity. -/
private theorem chainSteps_kept {first last : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) first last) :
    first.state.validators.data.size ≤ last.state.validators.data.size ∧
      (last.state.validators.data.size < 2 ^ 64 →
        ActiveKept (getCurrentEpoch first.state) first.state last.state) := by
  induction steps using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨Nat.le_refl _, fun _ => ActiveKept.refl _ _⟩
  | head step _ more =>
    obtain ⟨grows, active, later⟩ := chainStep_kept step
    exact ⟨Nat.le_trans grows more.1, fun small =>
      (active (Nat.lt_of_le_of_lt more.1 small)).trans ((more.2 small).mono later)⟩

/-- One step of a chain keeps activity in each epoch up to its current epoch.

The registry after it must hold fewer than 2^64 validators. -/
theorem ChainStep.activeKept {forked after : ForkedBeaconState preset}
    (small : after.state.validators.data.size < 2 ^ 64)
    (step : ChainStep config checks forked after) :
    ActiveKept (getCurrentEpoch forked.state) forked.state after.state :=
  (chainStep_kept step).2.1 small

/-- A run of steps of a chain keeps activity in each epoch up to the current epoch of its start.

The registry at its end must hold fewer than 2^64 validators. -/
theorem activeKept_of_chainSteps {first last : ForkedBeaconState preset}
    (small : last.state.validators.data.size < 2 ^ 64)
    (steps : Relation.ReflTransGen (ChainStep config checks) first last) :
    ActiveKept (getCurrentEpoch first.state) first.state last.state :=
  (chainSteps_kept steps).2 small

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

end EthLib.Consensus
