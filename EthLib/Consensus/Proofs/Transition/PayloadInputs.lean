module

public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.ParentPayload

/-!
# Proofs: what the checks of a payload and of a bid read

The checks of a payload and of a bid read a few fields of the state.

They read the slot, the genesis time, the RANDAO mixes and the block roots.

They also read the latest payload header and the latest block header.

From Gloas they read the latest block hash and the latest bid.

From Fulu the header step also reads the proposer lookahead, so these fields include it.

Most steps of a block keep all of these fields, when they succeed.

The withdrawals keep them, and from Gloas so do the requests of a parent payload.

The sync aggregate and the vote on the deposit contract keep them, and from Gloas the operations.

A full parent changes only the latest block hash among them, and the header step only the header.

So from Gloas the parent step keeps the proposer that the header step reads.

The RANDAO step changes only the mixes, and the bid step only the latest bid.

So from Gloas a block leaves its own bid as the latest bid.

The latest block hash after the block is then the parent hash of that bid.

At every fork a block leaves its own header as the latest header, and names the header before it.

From Gloas a block that succeeds also runs an operations step that succeeds.

From Capella to Fulu a block that succeeds runs header, withdrawal and payload steps that succeed.

Before Gloas a block that succeeds first runs a header step that succeeds, on the state before it.
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

From Gloas they have one latest block hash and one latest bid.

From Fulu they have one proposer lookahead, which the header step reads. -/
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
  proposerLookahead : after.proposerLookahead = state.proposerLookahead

theorem PayloadInputs.refl (state : BeaconState preset fork) : PayloadInputs state state :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem PayloadInputs.trans {first second third : BeaconState preset fork}
    (one : PayloadInputs first second) (two : PayloadInputs second third) :
    PayloadInputs first third :=
  ⟨two.slot.trans one.slot, two.genesisTime.trans one.genesisTime,
    two.randaoMixes.trans one.randaoMixes, two.blockRoots.trans one.blockRoots,
    two.latestExecutionPayloadHeader.trans one.latestExecutionPayloadHeader,
    two.latestBlockHeader.trans one.latestBlockHeader,
    two.latestBlockHash.trans one.latestBlockHash,
    two.latestExecutionPayloadBid.trans one.latestExecutionPayloadBid,
    two.proposerLookahead.trans one.proposerLookahead⟩

/-- A fold whose every step keeps the inputs of a payload keeps them. -/
theorem PayloadInputs.foldlM {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (kept : ∀ s x s', step s x = .ok s' → PayloadInputs s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : PayloadInputs state after :=
  foldlM_ok_invariant (PayloadInputs state) (fun _ _ _ before ok => before.trans (kept _ _ _ ok))
    (PayloadInputs.refl state) computed

/-! ## Mutators -/

theorem payloadInputs_setValidatorAt {position : Nat} {validator : Validator}
    (set : state.setValidatorAt position validator = .ok after) : PayloadInputs state after := by
  obtain ⟨_, rfl⟩ := setValidatorAt_ok set
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem payloadInputs_setValidator {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after) : PayloadInputs state after :=
  payloadInputs_setValidatorAt (by rwa [← setValidator_eq_setValidatorAt])

theorem payloadInputs_setBalance {index : ValidatorIndex} {balance : Gwei}
    (set : state.setBalance index balance = .ok after) : PayloadInputs state after := by
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact PayloadInputs.refl _
  refine (payloadInputs_initiateValidatorExit exitedOk).trans <|
    ((payloadInputs_setValidator markedOk).trans ?_).trans <|
    (payloadInputs_decreaseBalance loweredOk).trans <|
    (payloadInputs_increaseBalance raisedOk).trans <|
    (payloadInputs_increaseBalance lastOk).trans cancelled
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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
    exact (payloadInputs_setBalance set).trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases queued
    exact PayloadInputs.refl _

theorem payloadInputs_queueConsolidation {electra : .pectra ≤ fork}
    {sourceIndex : ValidatorIndex} {source : Validator} {targetIndex : ValidatorIndex}
    (computed :
      queueConsolidation config state electra sourceIndex source targetIndex = .ok after) :
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
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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
    | (cases computed; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem payloadInputs_processBuilderExitRequest {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    PayloadInputs state after := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · exact PayloadInputs.refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem payloadInputs_settleParentPayment
    (computed : settleParentPayment state gloas = .ok after) : PayloadInputs state after := by
  rw [settleParentPayment_eq computed]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The payment and the requests of a full parent keep the inputs of a payload.

Only its last step records a latest block hash. -/
private theorem payloadInputs_parentSteps {requests : ExecutionRequests preset fork}
    {settled deposited withdrawn consolidated builderDeposited exited : BeaconState preset fork}
    (settledOk : settleParentPayment state gloas = .ok settled)
    (depositsOk : requests.deposits.data.toList.foldlM
      (processDepositRequest · (Nat.le_trans (by decide) gloas) ·) settled = .ok deposited)
    (withdrawalsOk : requests.withdrawals.data.toList.foldlM
      (processWithdrawalRequest config · (Nat.le_trans (by decide) gloas) ·) deposited =
      .ok withdrawn)
    (consolidationsOk : requests.consolidations.data.toList.foldlM
      (processConsolidationRequest config · (Nat.le_trans (by decide) gloas) ·) withdrawn =
      .ok consolidated)
    (buildersOk : (requests.builderDeposits gloas).data.toList.foldlM
      (processBuilderDepositRequest config checks · gloas ·) consolidated = .ok builderDeposited)
    (exitsOk : (requests.builderExits gloas).data.toList.foldlM
      (processBuilderExitRequest config · gloas ·) builderDeposited = .ok exited)
    {bits : Vector Bool preset.SLOTS_PER_HISTORICAL_ROOT.toNat} {hash : Hash32} :
    PayloadInputs state { { exited with
      executionPayloadAvailability := fun _ => ⟨bits⟩
      latestBlockHash := fun _ => hash } with latestBlockHash := state.latestBlockHash } := by
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
    kept.latestExecutionPayloadBid, kept.proposerLookahead⟩

/-- A full parent changes only the latest block hash among the inputs of a payload.

Its payment and its requests keep them, and it then records the hash of the latest bid. -/
theorem payloadInputs_applyParentExecutionPayload {requests : ExecutionRequests preset fork}
    (computed : applyParentExecutionPayload config checks state gloas requests = .ok after) :
    PayloadInputs state { after with latestBlockHash := state.latestBlockHash } := by
  obtain ⟨_, _, _, _, _, _, _, settledOk, depositsOk, withdrawalsOk, consolidationsOk, buildersOk,
    exitsOk, -, rfl⟩ := applyParentExecutionPayload_ok computed
  exact payloadInputs_parentSteps settledOk depositsOk withdrawalsOk consolidationsOk buildersOk
    exitsOk

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
  rcases processParentExecutionPayload_ok computed with ⟨-, -, rfl⟩ |
    ⟨-, _, _, _, _, _, _, bits, settledOk, depositsOk, withdrawalsOk, consolidationsOk, buildersOk,
      exitsOk, -, rfl⟩
  · exact PayloadInputs.refl _
  · exact payloadInputs_parentSteps settledOk depositsOk withdrawalsOk consolidationsOk buildersOk
      exitsOk

/-- From Gloas, the parent step keeps the proposer of the slot of the state.

From Fulu that proposer is read from the proposer lookahead.

It sits at the position of the slot in its epoch. -/
theorem getBeaconProposerIndex_processParentExecutionPayload
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    getBeaconProposerIndex after = getBeaconProposerIndex state := by
  have kept := payloadInputs_processParentExecutionPayload computed
  have slot : after.slot = state.slot := kept.slot
  have lookahead : after.proposerLookahead = state.proposerLookahead := kept.proposerLookahead
  have fulu : .fusaka ≤ fork := Nat.le_trans (by decide) gloas
  simp only [getBeaconProposerIndex, fulu, ↓reduceDIte, slot, lookahead]

/-! ## Withdrawals -/

/-- A withdrawal changes a balance, and none of the inputs of a payload. -/
theorem payloadInputs_applyWithdrawal {withdrawal : Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) : PayloadInputs state after := by
  rw [applyWithdrawal_eq computed]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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
    split <;> split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have four : PayloadInputs finished after := by
    unfold updateNextWithdrawalValidatorIndex at last
    obtain ⟨_, _, last⟩ := bind_ok_iff.mp last
    dsimp only at last
    split at last
    · cases last
    · cases last
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · cases final
        exact PayloadInputs.refl _
    have flags : ∀ (current : Bool) (participation : EpochParticipation preset fork),
        PayloadInputs state (setEpochParticipation state current participation) := by
      intro current participation
      unfold setEpochParticipation
      split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact (flags _ _).trans ((payloadInputs_increaseBalance raisedOk).trans last)
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
  have kept := recordPendingAttestation_ok recorded
  split at kept <;>
  · obtain ⟨_, rest⟩ := kept
    rw [← rest]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## A block before Gloas -/

/-- Before Gloas, a block step that succeeds passes the header step, on the state that it runs on.

From Gloas the parent payload step runs first, and the header step runs on the state after it. -/
theorem processBlock_header_of_lt_gloas (before : fork < .glamsterdam)
    {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ∃ headed, processBlockHeader state block = .ok headed := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  unfold processBlock at computed
  split at computed
  · simp only [processBlockAltair, notGloas, ↓reduceDIte, pure_bind, bind_ok_iff] at computed
    obtain ⟨headed, headedOk, -⟩ := computed
    exact ⟨headed, headedOk⟩
  · simp only [bind_ok_iff] at computed
    obtain ⟨headed, headedOk, -⟩ := computed
    exact ⟨headed, headedOk⟩

/-! ## A block from Capella to Fulu -/

/-- From Capella to Fulu, a block step that succeeds runs its header, withdrawal and payload steps.

The header step runs on the state before the block.

Each later step runs on the state that the step before it returns.

The withdrawal step reads the payload of the block. -/
theorem processBlock_steps_of_lt_gloas (capella : .shapella ≤ fork) (before : fork < .glamsterdam)
    {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ∃ headed withdrawn paid,
      processBlockHeader state block = .ok headed ∧
      processWithdrawals headed capella
        (fun _ => block.body.executionPayload ⟨Nat.le_trans (by decide) capella, before⟩) =
        .ok withdrawn ∧
      processExecutionPayload config engine withdrawn block.body
        ⟨Nat.le_trans (by decide) capella, before⟩ = .ok paid := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) capella
  have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) capella
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp only [processBlock, altair, ↓reduceDIte, processBlockAltair, notGloas, bellatrix,
    processBlockExecution, capella, pure_bind, bind_ok_iff] at computed
  -- Before Gloas no parent step comes first, and from Capella the withdrawals precede the payload.
  obtain ⟨headed, headedOk, paid, ⟨withdrawn, withdrawnOk, paidOk⟩, -⟩ := computed
  exact ⟨headed, withdrawn, paid, headedOk, withdrawnOk, paidOk⟩

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
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at recordedOk
    subst recordedOk
    exact PayloadInputs.refl _

/-- A payload before Gloas keeps the RANDAO mixes. -/
theorem randaoMixes_processExecutionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  rfl

/-- The execution part of a block keeps the mixes. -/
theorem randaoMixes_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    exact (payloadInputs_processExecutionPayloadBid bid).randaoMixes.trans
      (payloadInputs_processWithdrawals withdrawnOk).randaoMixes
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact (randaoMixes_processExecutionPayload paid).trans
      (payloadInputs_processWithdrawals withdrawnOk).randaoMixes
  · dsimp only at computed
    split at computed
    · exact randaoMixes_processExecutionPayload computed
    · cases computed
      rfl

/-- From Gloas, a block that succeeds runs each of its steps, each on the state of the last one.

The parent payload runs first, then the header, the withdrawals, the bid and the RANDAO reveal.

Before Heze the vote on the deposit contract follows, and from Heze no step runs in its place.

The operations and the sync aggregate come last.

The operations read the slot of the parent from the latest block header before the block. -/
theorem processBlock_gloas_ok (gloas : .glamsterdam ≤ fork) {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ∃ parented headed withdrawn bidded revealed voted operated, ∃ payload,
      processParentExecutionPayload config checks state gloas block.body = .ok parented ∧
      processBlockHeader parented block = .ok headed ∧
      processWithdrawals headed (Nat.le_trans (by decide) gloas) payload = .ok withdrawn ∧
      processExecutionPayloadBid config checks withdrawn gloas
        (block.body.signedExecutionPayloadBid gloas) = .ok bidded ∧
      processRandao config checks bidded block.body = .ok revealed ∧
      (∀ before : fork < .hegota, processEth1Data before revealed block.body = .ok voted) ∧
      (.hegota ≤ fork → voted = revealed) ∧
      processOperations config checks voted block.body state.latestBlockHeader.slot =
        .ok operated ∧
      processSyncAggregate config checks operated (Nat.le_trans (by decide) gloas)
        (block.body.syncAggregate (Nat.le_trans (by decide) gloas)) = .ok after := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) gloas
  have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) gloas
  simp only [processBlock, altair, ↓reduceDIte, processBlockAltair, gloas, bellatrix,
    processBlockExecution, bind_ok_iff] at computed
  obtain ⟨parented, parentOk, headed, headedOk, bidded, ⟨withdrawn, withdrawnOk, biddedOk⟩,
    revealed, revealedOk, voted, votedOk, operated, operatedOk, synced⟩ := computed
  refine ⟨parented, headed, withdrawn, bidded, revealed, voted, operated, _, parentOk, headedOk,
    withdrawnOk, biddedOk, revealedOk, fun before => ?_, fun heze => ?_, operatedOk, synced⟩
  · simpa only [before, ↓reduceDIte] using votedOk
  · have dropped : ¬fork < .hegota := Nat.not_lt_of_le heze
    simp only [dropped, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at votedOk
    exact votedOk.symm

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
  obtain ⟨parented, headed, withdrawn, bidded, revealed, voted, _, _, parentOk, headedOk,
    withdrawnOk, biddedOk, revealedOk, votedOk, kept, operatedOk, synced⟩ :=
    processBlock_gloas_ok gloas computed
  have randao := payloadInputs_processRandao revealedOk
  have voting : PayloadInputs revealed voted := by
    by_cases before : fork < .hegota
    · exact payloadInputs_processEth1Data (votedOk before)
    · rw [kept (Nat.le_of_not_lt before)]
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
  obtain ⟨-, -, -, -, -, voted, operated, -, -, -, -, -, -, -, -, operatedOk, -⟩ :=
    processBlock_gloas_ok gloas computed
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

/-- The operations of a block keep the latest block header, at every fork.

Before Gloas the deposits and, from Electra, the requests of the execution layer run too. -/
private theorem latestBlockHeader_processOperations {body : BeaconBlockBody preset fork}
    {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    after.latestBlockHeader = state.latestBlockHeader := by
  have fold {α ε : Type} {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
      (kept : ∀ s x t, step s x = .ok t → t.latestBlockHeader = s.latestBlockHeader)
      {s t : BeaconState preset fork} {items : List α} (ok : items.foldlM step s = .ok t) :
      t.latestBlockHeader = s.latestBlockHeader :=
    foldlM_ok_invariant (fun t => t.latestBlockHeader = s.latestBlockHeader)
      (fun _ _ _ before ok => (kept _ _ _ ok).trans before) rfl ok
  by_cases gloas : .glamsterdam ≤ fork
  · exact (payloadInputs_processOperations gloas computed).latestBlockHeader
  simp only [processOperations, gloas, ↓reduceDIte, bind_ok_iff, ensure_ok_iff,
    ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposers, _, attesters, _, attestations, _, deposits, exited, exits,
    changed, changes, requests⟩ := computed
  have changesKept : changed.latestBlockHeader = exited.latestBlockHeader := by
    unfold processBlsToExecutionChanges at changes
    split at changes
    · rw [← Array.foldlM_toList] at changes
      exact fold (fun _ _ _ ok => (payloadInputs_processBlsToExecutionChange ok).latestBlockHeader)
        changes
    · cases changes
      rfl
  have requestsKept : after.latestBlockHeader = changed.latestBlockHeader := by
    split at requests
    · simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at requests
      obtain ⟨_, deposited, _, withdrawn, consolidated⟩ := requests
      exact (fold (fun _ _ _ ok =>
        (payloadInputs_processConsolidationRequest ok).latestBlockHeader) consolidated).trans <|
        (fold (fun _ _ _ ok =>
          (payloadInputs_processWithdrawalRequest ok).latestBlockHeader) withdrawn).trans <|
        fold (fun _ _ _ ok => (payloadInputs_processDepositRequest ok).latestBlockHeader) deposited
    · cases requests
      rfl
  exact requestsKept.trans <| changesKept.trans <|
    (fold (fun _ _ _ ok => (payloadInputs_processVoluntaryExit ok).latestBlockHeader)
      exits).trans <|
    (fold (fun _ _ _ ok => by
      obtain ⟨_, _, _, _, applied⟩ := processDeposit_ok ok
      exact (frame_applyDeposit applied).latestBlockHeader) deposits).trans <|
    (fold (fun _ _ _ ok => (payloadInputs_processAttestation ok).latestBlockHeader)
      attestations).trans <|
    (fold (fun _ _ _ ok => (payloadInputs_processAttesterSlashing ok).latestBlockHeader)
      attesters).trans <|
    fold (fun _ _ _ ok => (payloadInputs_processProposerSlashing ok).latestBlockHeader) proposers

/-- The execution part of a block keeps the latest block header. -/
private theorem latestBlockHeader_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    after.latestBlockHeader = state.latestBlockHeader := by
  have payload {before after : BeaconState preset fork}
      {during : .bellatrix ≤ fork ∧ fork < .glamsterdam}
      (ok : processExecutionPayload config engine before body during = .ok after) :
      after.latestBlockHeader = before.latestBlockHeader := by
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
    rfl
  unfold processBlockExecution at computed
  split at computed
  · obtain ⟨_, withdrawn, bid⟩ := bind_ok_iff.mp computed
    exact (payloadInputs_processExecutionPayloadBid bid).latestBlockHeader.trans
      (payloadInputs_processWithdrawals withdrawn).latestBlockHeader
  · split at computed
    · obtain ⟨_, withdrawn, executed⟩ := bind_ok_iff.mp computed
      exact (payload executed).trans (payloadInputs_processWithdrawals withdrawn).latestBlockHeader
    · dsimp only at computed
      split at computed
      · exact payload computed
      · cases computed
        rfl

/-- A block runs its header step on a state with the slot and latest header of the state before it.

Only the parent payload of a block can come first, from Gloas, and it keeps both.

No later step changes the latest block header, so the result has the one that the header step set.
-/
private theorem processBlock_header_split {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ∃ parented headed, parented.slot = state.slot ∧
      parented.latestBlockHeader = state.latestBlockHeader ∧
      processBlockHeader parented block = .ok headed ∧
      after.latestBlockHeader = headed.latestBlockHeader := by
  by_cases gloas : .glamsterdam ≤ fork
  · obtain ⟨parented, headed, withdrawn, _, _, parentOk, headedOk, withdrawnOk, bid, -, header, -,
      -⟩ := processBlock_steps gloas computed
    have kept := payloadInputs_processParentExecutionPayload parentOk
    exact ⟨parented, headed, kept.slot, kept.latestBlockHeader, headedOk,
      header.trans ((payloadInputs_processExecutionPayloadBid bid).latestBlockHeader.trans
        (payloadInputs_processWithdrawals withdrawnOk).latestBlockHeader)⟩
  · unfold processBlock at computed
    split at computed
    · simp only [processBlockAltair, gloas, ↓reduceDIte, pure_bind, bind_ok_iff] at computed
      obtain ⟨headed, headedOk, executed, executedOk, revealed, revealedOk, voted, votedOk,
        operated, operatedOk, synced⟩ := computed
      have executedKept : executed.latestBlockHeader = headed.latestBlockHeader := by
        split at executedOk
        · exact latestBlockHeader_processBlockExecution executedOk
        · cases executedOk
          rfl
      have votedKept : voted.latestBlockHeader = revealed.latestBlockHeader := by
        split at votedOk
        · exact (payloadInputs_processEth1Data votedOk).latestBlockHeader
        · cases votedOk
          rfl
      exact ⟨state, headed, rfl, rfl, headedOk,
        (payloadInputs_processSyncAggregate synced).latestBlockHeader.trans <|
          (latestBlockHeader_processOperations operatedOk).trans <| votedKept.trans <|
          (payloadInputs_processRandao revealedOk).latestBlockHeader.trans executedKept⟩
    · simp only [bind_ok_iff] at computed
      obtain ⟨headed, headedOk, revealed, revealedOk, voted, votedOk, operatedOk⟩ := computed
      exact ⟨state, headed, rfl, rfl, headedOk,
        (latestBlockHeader_processOperations operatedOk).trans <|
          (payloadInputs_processEth1Data votedOk).latestBlockHeader.trans
            (payloadInputs_processRandao revealedOk).latestBlockHeader⟩

/-- At every fork, a block leaves its header as the latest block header.

The header holds the slot, the proposer and the parent root of the block, and the root of its body.

Its state root is zero. -/
theorem latestBlockHeader_processBlock {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ∃ bodyRoot, Serialization.Ssz.SszType.hashTreeRoot block.body = .ok bodyRoot ∧
      after.latestBlockHeader =
        { slot := block.slot, proposerIndex := block.proposerIndex,
          parentRoot := block.parentRoot, stateRoot := Vector.replicate 32 0, bodyRoot } := by
  obtain ⟨_, _, -, -, headedOk, header⟩ := processBlock_header_split computed
  obtain ⟨bodyRoot, rooted, rfl⟩ := processBlockHeader_eq headedOk
  exact ⟨bodyRoot, rooted, header⟩

/-- At every fork, a block names the latest block header before it as its parent.

The block is at the slot of the state, after the slot of that header.

Its parent root is the root of that header. -/
theorem processBlock_parentRoot {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    block.slot = state.slot ∧ state.latestBlockHeader.slot < block.slot ∧
      Serialization.Ssz.SszType.hashTreeRoot state.latestBlockHeader = .ok block.parentRoot := by
  obtain ⟨_, _, slot, header, headedOk, -⟩ := processBlock_header_split computed
  obtain ⟨atSlot, newer, -, parent, -⟩ := processBlockHeader_checks headedOk
  rw [header] at newer parent
  exact ⟨atSlot.trans slot, newer, parent⟩

end EthLib.Consensus
