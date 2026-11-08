module

public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.ParentPayload

/-!
# Proofs: what the checks of a payload and of a bid read

The checks of a payload and of a bid read a few fields of the state.

They read the slot, the genesis time, the RANDAO mixes and the block roots.

They also read the latest payload header and the latest block header.

From Gloas they read the latest block hash and the latest bid.

Most steps of a block keep all of these fields, when they succeed.

The withdrawals keep them, and from Gloas so do the requests of a parent payload.

The sync aggregate and the vote on the deposit contract keep them, and from Gloas the operations.

A full parent changes only the latest block hash among them, and the header step only the header.

The RANDAO step changes only the mixes, and the bid step only the latest bid.

So from Gloas a block leaves its own bid as the latest bid, and its header as the latest header.

The latest block hash after the block is then the parent hash of that bid.

From Gloas a block that succeeds also runs an operations step that succeeds.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}
  {gloas : .glamsterdam ≤ fork}

/-- Two states that agree on what the checks of a payload and of a bid read of them.

They have one slot, one genesis time, one buffer of RANDAO mixes and one buffer of block roots.

They also have one latest payload header and one latest block header.

From Gloas they have one latest block hash and one latest bid. -/
structure PayloadInputs (state after : BeaconState preset fork) : Prop where
  slot : after.slot = state.slot
  genesisTime : after.genesisTime = state.genesisTime
  randaoMixes : after.randaoMixes = state.randaoMixes
  blockRoots : after.blockRoots = state.blockRoots
  latestExecutionPayloadHeader :
    after.latestExecutionPayloadHeader = state.latestExecutionPayloadHeader
  latestBlockHeader : after.latestBlockHeader = state.latestBlockHeader
  latestBlockHash : after.latestBlockHash = state.latestBlockHash
  latestExecutionPayloadBid : after.latestExecutionPayloadBid = state.latestExecutionPayloadBid

theorem PayloadInputs.refl (state : BeaconState preset fork) : PayloadInputs state state :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem PayloadInputs.trans {first second third : BeaconState preset fork}
    (one : PayloadInputs first second) (two : PayloadInputs second third) :
    PayloadInputs first third :=
  ⟨two.slot.trans one.slot, two.genesisTime.trans one.genesisTime,
    two.randaoMixes.trans one.randaoMixes, two.blockRoots.trans one.blockRoots,
    two.latestExecutionPayloadHeader.trans one.latestExecutionPayloadHeader,
    two.latestBlockHeader.trans one.latestBlockHeader,
    two.latestBlockHash.trans one.latestBlockHash,
    two.latestExecutionPayloadBid.trans one.latestExecutionPayloadBid⟩

/-- A fold whose every step keeps the inputs of a payload keeps them. -/
theorem PayloadInputs.foldlM {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (kept : ∀ s x s', step s x = .ok s' → PayloadInputs s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : PayloadInputs state after :=
  foldlM_ok_invariant (PayloadInputs state) (fun _ _ _ before ok => before.trans (kept _ _ _ ok))
    (PayloadInputs.refl state) computed

/-! ## Mutators -/

theorem payloadInputs_setValidator {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after) : PayloadInputs state after := by
  obtain ⟨_, rfl⟩ := setValidator_ok set
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem payloadInputs_setBalance {index : ValidatorIndex} {balance : Gwei}
    (set : state.setBalance index balance = .ok after) : PayloadInputs state after := by
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem payloadInputs_increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : PayloadInputs state after := by
  obtain ⟨_, set⟩ := increaseBalance_ok computed
  exact payloadInputs_setBalance set

theorem payloadInputs_decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : PayloadInputs state after := by
  obtain ⟨_, set⟩ := decreaseBalance_ok computed
  exact payloadInputs_setBalance set

theorem payloadInputs_exitQueue {exitBalance : Gwei} {exitEpoch : Epoch}
    (computed : exitQueue config state exitBalance = .ok (after, exitEpoch)) :
    PayloadInputs state after := by
  unfold exitQueue at computed
  split at computed
  · simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := computed
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, rfl, _⟩ := computed
    exact PayloadInputs.refl _

theorem payloadInputs_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) :
    PayloadInputs state after := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok computed
  · exact PayloadInputs.refl _
  · exact (payloadInputs_exitQueue queue).trans (payloadInputs_setValidator set)

/-- Slashing a validator keeps the inputs of a payload. -/
theorem payloadInputs_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    PayloadInputs state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, last, exitedOk, -, -, markedOk, -, -, -, loweredOk, -, -,
    raisedOk, lastOk, done⟩ := slashValidator_ok computed
  -- The last step changes at most the builder payments, which are not an input of a payload.
  have cancelled : PayloadInputs last after := by
    subst done
    split
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact PayloadInputs.refl _
  refine (payloadInputs_initiateValidatorExit exitedOk).trans <|
    ((payloadInputs_setValidator markedOk).trans ?_).trans <|
    (payloadInputs_decreaseBalance loweredOk).trans <|
    (payloadInputs_increaseBalance raisedOk).trans <|
    (payloadInputs_increaseBalance lastOk).trans cancelled
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The requests of a parent payload -/

theorem payloadInputs_processDepositRequest {electra : .pectra ≤ fork}
    {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    PayloadInputs state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem payloadInputs_requestPartialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    PayloadInputs state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churned
    obtain ⟨_, _, _, _, _, _, churned⟩ := churned
    cases churned
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases computed
    exact PayloadInputs.refl _

theorem payloadInputs_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    PayloadInputs state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact PayloadInputs.refl _)
    | exact payloadInputs_initiateValidatorExit (liftAccessor_ok.mp computed)
    | exact payloadInputs_requestPartialWithdrawal computed

theorem payloadInputs_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    PayloadInputs state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨_, _, _, set, queued⟩ := computed
  refine (payloadInputs_setValidator set).trans ?_
  simp only [queueExcessActiveBalance, bind_ok_iff] at queued
  obtain ⟨_, _, queued⟩ := queued
  split at queued
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
    obtain ⟨_, _, _, _, _, set, rfl⟩ := queued
    exact (payloadInputs_setBalance set).trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases queued
    exact PayloadInputs.refl _

theorem payloadInputs_queueConsolidation {electra : .pectra ≤ fork}
    {sourcePosition : Nat} {source : Validator} {targetIndex : ValidatorIndex}
    (computed :
      queueConsolidation config state electra sourcePosition source targetIndex = .ok after) :
    PayloadInputs state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure] at computed
  obtain ⟨⟨_, _⟩, churned, _, _, _, set, _, _, computed⟩ := computed
  simp only [Except.ok.injEq] at computed
  subst computed
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at churned
  obtain ⟨_, _, _, _, _, _, churned⟩ := churned
  cases churned
  refine (PayloadInputs.trans ?_ (payloadInputs_setValidator set)).trans ?_ <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem payloadInputs_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    PayloadInputs state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact PayloadInputs.refl _)
    | exact payloadInputs_switchToCompoundingValidator (liftAccessor_ok.mp computed)
    | exact payloadInputs_queueConsolidation computed

theorem payloadInputs_processBuilderDepositRequest {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    PayloadInputs state after := by
  unfold processBuilderDepositRequest addBuilderToRegistry at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem payloadInputs_processBuilderExitRequest {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    PayloadInputs state after := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · exact PayloadInputs.refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem payloadInputs_settleParentPayment
    (computed : settleParentPayment state gloas = .ok after) : PayloadInputs state after := by
  unfold settleParentPayment at computed
  split at computed
  · have settled := liftAccessor_ok.mp computed
    unfold settleBuilderPayment at settled
    split at settled
    · cases settled
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · cases settled
  · simp only at computed
    split at computed <;> cases computed <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A full parent changes only the latest block hash among the inputs of a payload.

Its payment and its requests keep them, and it then records the hash of the latest bid. -/
theorem payloadInputs_applyParentExecutionPayload {requests : ExecutionRequests preset fork}
    (computed : applyParentExecutionPayload config checks state gloas requests = .ok after) :
    PayloadInputs state { after with latestBlockHash := state.latestBlockHash } := by
  unfold applyParentExecutionPayload at computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, settled, settledOk, requested, requestedOk, _, _, rfl⟩ :=
    computed
  unfold processParentRequests at requestedOk
  simp only [bind_ok_iff, ← Array.foldlM_toList] at requestedOk
  obtain ⟨_, depositsOk, _, withdrawalsOk, _, consolidationsOk, _, buildersOk, exitsOk⟩ :=
    requestedOk
  have kept := (payloadInputs_settleParentPayment settledOk).trans <|
    (PayloadInputs.foldlM (fun _ _ _ ok => payloadInputs_processDepositRequest ok)
      depositsOk).trans <|
    (PayloadInputs.foldlM (fun _ _ _ ok => payloadInputs_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    (PayloadInputs.foldlM (fun _ _ _ ok => payloadInputs_processConsolidationRequest ok)
      consolidationsOk).trans <|
    (PayloadInputs.foldlM (fun _ _ _ ok => payloadInputs_processBuilderDepositRequest ok)
      buildersOk).trans <|
    PayloadInputs.foldlM (fun _ _ _ ok => payloadInputs_processBuilderExitRequest ok) exitsOk
  exact ⟨kept.slot, kept.genesisTime, kept.randaoMixes, kept.blockRoots,
    kept.latestExecutionPayloadHeader, kept.latestBlockHeader, rfl,
    kept.latestExecutionPayloadBid⟩

/-- A full parent keeps the latest bid.

Its payment and its requests leave the bid as it was. -/
theorem applyParentExecutionPayload_latestExecutionPayloadBid
    {requests : ExecutionRequests preset fork}
    (computed : applyParentExecutionPayload config checks state gloas requests = .ok after) :
    after.latestExecutionPayloadBid = state.latestExecutionPayloadBid :=
  (payloadInputs_applyParentExecutionPayload computed).latestExecutionPayloadBid

/-- The parent step changes only the latest block hash among the inputs of a payload. -/
theorem payloadInputs_processParentExecutionPayload {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    PayloadInputs state { after with latestBlockHash := state.latestBlockHash } := by
  unfold processParentExecutionPayload at computed
  dsimp only at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact PayloadInputs.refl _
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, applied⟩ := computed
  exact payloadInputs_applyParentExecutionPayload applied

/-! ## Withdrawals -/

/-- A withdrawal changes a balance, and none of the inputs of a payload. -/
theorem payloadInputs_applyWithdrawal {withdrawal : Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) : PayloadInputs state after := by
  unfold applyWithdrawal at computed
  split at computed
  · obtain ⟨_, _, set⟩ := bind_ok_iff.mp computed
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact payloadInputs_decreaseBalance computed

/-- Applying the expected withdrawals changes none of the inputs of a payload. -/
theorem payloadInputs_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    PayloadInputs state after := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : PayloadInputs state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact PayloadInputs.foldlM (fun _ _ _ ok => payloadInputs_applyWithdrawal ok) appliedOk
  have two : PayloadInputs applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · obtain ⟨_, _, built⟩ := bind_ok_iff.mp indexedOk
      cases built
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · cases indexedOk
      exact PayloadInputs.refl _
  have three : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → PayloadInputs kept finished := by
    intro kept ok
    split at ok
    · unfold updateNextWithdrawalBuilderIndex at ok
      dsimp only at ok
      split at ok
      · cases ok
        exact PayloadInputs.refl _
      · obtain ⟨_, _, built⟩ := bind_ok_iff.mp ok
        cases built
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · cases ok
      exact PayloadInputs.refl _
  have queued : PayloadInputs indexed (if electra : .pectra ≤ fork then
      updatePendingPartialWithdrawals (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals indexed gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else indexed) electra expected.processedPartialWithdrawalsCount
    else if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals indexed gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else indexed) := by
    split <;> split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have four : PayloadInputs finished after := by
    unfold updateNextWithdrawalValidatorIndex at last
    obtain ⟨_, _, last⟩ := bind_ok_iff.mp last
    dsimp only at last
    split at last
    · cases last
    · cases last
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact one.trans (two.trans (queued.trans ((three _ sweptOk).trans four)))

/-- The withdrawal step changes none of the inputs of a payload. -/
theorem payloadInputs_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) :
    PayloadInputs state after := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · obtain ⟨_, _, applied⟩ := bind_ok_iff.mp computed
      exact payloadInputs_applyExpectedWithdrawals (liftAccessor_ok.mp applied)
    · cases computed
      exact PayloadInputs.refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact payloadInputs_applyExpectedWithdrawals applied

/-! ## The operations of a block -/

theorem payloadInputs_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    PayloadInputs state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact payloadInputs_slashValidator slashed

theorem payloadInputs_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    PayloadInputs step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact payloadInputs_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ PayloadInputs.refl _

theorem payloadInputs_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    PayloadInputs state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant (fun step => PayloadInputs state step.1)
    (fun _ _ _ before ok => before.trans (payloadInputs_slashIfSlashable ok))
    (show PayloadInputs state (state, false).1 from PayloadInputs.refl state) folded

theorem payloadInputs_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    PayloadInputs state after := by
  unfold processAttestation at computed
  split at computed
  · unfold processAttestationAltair at computed
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := computed
    have last : PayloadInputs raised after := by
      split at final
      · rw [recordPaymentWeight_eq final]
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · cases final
        exact PayloadInputs.refl _
    have flags : ∀ (current : Bool) (participation : EpochParticipation preset fork),
        PayloadInputs state (setEpochParticipation state current participation) := by
      intro current participation
      unfold setEpochParticipation
      split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact (flags _ _).trans ((payloadInputs_increaseBalance raisedOk).trans last)
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
  have kept := recordPendingAttestation_ok recorded
  split at kept <;>
  · obtain ⟨_, rest⟩ := kept
    rw [← rest]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem payloadInputs_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    PayloadInputs state after := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact payloadInputs_initiateValidatorExit exited

theorem payloadInputs_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    PayloadInputs state after := by
  obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact payloadInputs_setValidator set

/-- From Gloas the operations of a block keep the inputs of a payload. -/
theorem payloadInputs_processOperations (gloas : .glamsterdam ≤ fork)
    {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    PayloadInputs state after := by
  simp only [processOperations, gloas, ↓reduceDIte, processOperationsGloas, bind_ok_iff,
    ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
    attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
  exact (PayloadInputs.foldlM (fun _ _ _ ok => payloadInputs_processProposerSlashing ok)
      proposersOk).trans <|
    (PayloadInputs.foldlM (fun _ _ _ ok => payloadInputs_processAttesterSlashing ok)
      attestersOk).trans <|
    (PayloadInputs.foldlM (fun _ _ _ ok => payloadInputs_processAttestation ok)
      attestedOk).trans <|
    (PayloadInputs.foldlM (fun _ _ _ ok => payloadInputs_processVoluntaryExit ok) exitsOk).trans <|
    (PayloadInputs.foldlM (fun _ _ _ ok => payloadInputs_processBlsToExecutionChange ok)
      changesOk).trans <|
    PayloadInputs.foldlM (fun _ _ _ ok => by
      rw [processPayloadAttestation_eq ok]
      exact PayloadInputs.refl _) paid

/-- The sync aggregate keeps the inputs of a payload. -/
theorem payloadInputs_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    PayloadInputs state after := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  refine PayloadInputs.foldlM (fun _ _ _ ok => ?_) folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    exact (payloadInputs_increaseBalance raised).trans (payloadInputs_increaseBalance paid)
  · exact payloadInputs_decreaseBalance (liftAccessor_ok.mp ok)

/-- The vote on the deposit contract keeps the inputs of a payload. -/
theorem payloadInputs_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) : PayloadInputs state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  rw [← rest]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## A block from Gloas -/

/-- The header step changes only the latest block header among the inputs of a payload. -/
theorem payloadInputs_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) :
    PayloadInputs state { after with latestBlockHeader := state.latestBlockHeader } := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact PayloadInputs.refl _

/-- The RANDAO step changes only the mixes among the inputs of a payload. -/
theorem payloadInputs_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) :
    PayloadInputs state { after with randaoMixes := state.randaoMixes } := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact PayloadInputs.refl _

/-- The bid step changes only the latest bid among the inputs of a payload. -/
theorem payloadInputs_processExecutionPayloadBid {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    PayloadInputs state
      { after with latestExecutionPayloadBid := state.latestExecutionPayloadBid } := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok computed
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at recordedOk
    subst recordedOk
    exact PayloadInputs.refl _

/-- From Gloas, a block runs its parent, header, withdrawal and bid steps in that order.

The steps after the bid keep the slot, the latest block header, the latest block hash and bid. -/
theorem processBlock_steps (gloas : .glamsterdam ≤ fork) {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ∃ parented headed withdrawn bidded, ∃ payload,
      processParentExecutionPayload config checks state gloas block.body = .ok parented ∧
      processBlockHeader parented block = .ok headed ∧
      processWithdrawals headed (Nat.le_trans (by decide) gloas) payload = .ok withdrawn ∧
      processExecutionPayloadBid config checks withdrawn gloas
        (block.body.signedExecutionPayloadBid gloas) = .ok bidded ∧
      after.slot = bidded.slot ∧ after.latestBlockHeader = bidded.latestBlockHeader ∧
      after.latestBlockHash = bidded.latestBlockHash ∧
      after.latestExecutionPayloadBid = bidded.latestExecutionPayloadBid := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) gloas
  have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) gloas
  simp only [processBlock, altair, ↓reduceDIte, processBlockAltair, gloas, bellatrix,
    processBlockExecution, bind_ok_iff] at computed
  obtain ⟨parented, parentOk, headed, headedOk, bidded, ⟨withdrawn, withdrawnOk, biddedOk⟩,
    revealed, revealedOk, voted, votedOk, operated, operatedOk, synced⟩ := computed
  have randao := payloadInputs_processRandao revealedOk
  have voting : PayloadInputs revealed voted := by
    split at votedOk
    · exact payloadInputs_processEth1Data votedOk
    · cases votedOk
      exact PayloadInputs.refl _
  have rest := voting.trans <| (payloadInputs_processOperations gloas operatedOk).trans <|
    payloadInputs_processSyncAggregate synced
  exact ⟨parented, headed, withdrawn, bidded, _, parentOk, headedOk, withdrawnOk, biddedOk,
    rest.slot.trans randao.slot, rest.latestBlockHeader.trans randao.latestBlockHeader,
    rest.latestBlockHash.trans randao.latestBlockHash,
    rest.latestExecutionPayloadBid.trans randao.latestExecutionPayloadBid⟩

/-- From Gloas, a block step that succeeds runs an operations step that succeeds.

The operations read the slot of the parent from the latest block header before the block. -/
theorem processBlock_operations (gloas : .glamsterdam ≤ fork) {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ∃ voted operated, processOperations config checks voted block.body
      state.latestBlockHeader.slot = .ok operated := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) gloas
  have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) gloas
  simp only [processBlock, altair, ↓reduceDIte, processBlockAltair, gloas, bellatrix,
    processBlockExecution, bind_ok_iff] at computed
  -- Four steps and the vote on the deposit contract come first, and Heze drops the vote.
  obtain ⟨-, -, -, -, -, -, -, -, voted, -, operated, operatedOk, -⟩ := computed
  exact ⟨voted, operated, operatedOk⟩

/-- From Gloas, a block leaves its own bid as the latest bid. -/
theorem latestExecutionPayloadBid_processBlock (gloas : .glamsterdam ≤ fork)
    {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    after.latestExecutionPayloadBid gloas =
      (block.body.signedExecutionPayloadBid gloas).message := by
  obtain ⟨_, _, _, _, _, _, _, _, bid, -, -, -, kept⟩ := processBlock_steps gloas computed
  rw [kept]
  exact latestExecutionPayloadBid_processExecutionPayloadBid bid

/-- From Gloas, the latest block hash after a block is the parent hash of the latest bid. -/
theorem latestBlockHash_processBlock (gloas : .glamsterdam ≤ fork)
    {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    after.latestBlockHash gloas = (after.latestExecutionPayloadBid gloas).parentBlockHash := by
  obtain ⟨_, _, withdrawn, _, _, _, _, _, bid, -, -, hash, kept⟩ :=
    processBlock_steps gloas computed
  obtain ⟨-, -, -, -, parentHash, -⟩ :=
    checkExecutionPayloadBid_ok_iff.mp (processExecutionPayloadBid_ok bid).1
  rw [hash, kept, latestExecutionPayloadBid_processExecutionPayloadBid bid, parentHash]
  exact congrFun (payloadInputs_processExecutionPayloadBid bid).latestBlockHash gloas

/-- From Gloas, a block leaves its header as the latest block header.

The header holds the slot, the proposer and the parent root of the block, and the root of its body.

Its state root is zero. -/
theorem latestBlockHeader_processBlock (gloas : .glamsterdam ≤ fork)
    {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ∃ bodyRoot, Serialization.Ssz.SszType.hashTreeRoot block.body = .ok bodyRoot ∧
      after.latestBlockHeader =
        { slot := block.slot, proposerIndex := block.proposerIndex,
          parentRoot := block.parentRoot, stateRoot := Vector.replicate 32 0, bodyRoot } := by
  obtain ⟨_, _, _, _, _, _, headedOk, withdrawnOk, bid, -, header, -, -⟩ :=
    processBlock_steps gloas computed
  obtain ⟨bodyRoot, rooted, rfl⟩ := processBlockHeader_eq headedOk
  refine ⟨bodyRoot, rooted, ?_⟩
  exact header.trans ((payloadInputs_processExecutionPayloadBid bid).latestBlockHeader.trans
    (payloadInputs_processWithdrawals withdrawnOk).latestBlockHeader)

end EthLib.Consensus
