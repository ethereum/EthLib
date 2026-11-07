module

public import EthLib.Consensus.Proofs.Builders
public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Consensus.Proofs.Transition.Requests
public import EthLib.Consensus.Transition.ParentPayload

/-!
# Proofs: the parent payload

An empty parent leaves the state as it is when the block carries no request.

It rejects a block that carries a request.

A full parent records its block hash, and marks its slot as having a payload.

The payment of its builder empties at most one pending payment.

A full parent keeps the latest bid, when it applies.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork} {gloas : .glamsterdam ≤ fork}

/-- An empty parent leaves the state as it is when the block carries no request. -/
theorem processParentExecutionPayload_of_empty {body : BeaconBlockBody preset fork}
    (empty : (body.signedExecutionPayloadBid gloas).message.parentBlockHash ≠
      (state.latestExecutionPayloadBid gloas).blockHash)
    (noRequest : (body.parentExecutionRequests gloas).isEmpty gloas = true) :
    processParentExecutionPayload config checks state gloas body = .ok state := by
  simp [processParentExecutionPayload, empty, noRequest, ensure, bind, Except.bind, pure,
    Except.pure]

/-- An empty parent rejects a block that carries a request. -/
theorem processParentExecutionPayload_of_empty_requests {body : BeaconBlockBody preset fork}
    (empty : (body.signedExecutionPayloadBid gloas).message.parentBlockHash ≠
      (state.latestExecutionPayloadBid gloas).blockHash)
    (requests : (body.parentExecutionRequests gloas).isEmpty gloas = false) :
    processParentExecutionPayload config checks state gloas body =
      .error .parentRequestsNotEmpty := by
  simp [processParentExecutionPayload, empty, requests, ensure, bind, Except.bind]

/-- A full parent makes the hash of its bid the latest block hash. -/
theorem applyParentExecutionPayload_latestBlockHash {requests : ExecutionRequests preset fork}
    (computed : applyParentExecutionPayload config checks state gloas requests = .ok after) :
    after.latestBlockHash gloas = (state.latestExecutionPayloadBid gloas).blockHash := by
  simp only [applyParentExecutionPayload, bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  rfl

/-- A full parent marks its slot as having a payload.

The bit of its slot, modulo the length of the record, is set. -/
theorem applyParentExecutionPayload_available {requests : ExecutionRequests preset fork}
    (computed : applyParentExecutionPayload config checks state gloas requests = .ok after) :
    (after.executionPayloadAvailability gloas).bits[
      (state.latestBlockHeader.slot % preset.SLOTS_PER_HISTORICAL_ROOT).toNat]? = some true := by
  simp only [applyParentExecutionPayload, bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  rename_i written
  exact getElem?_writeCircular (liftAccessor_ok.mp written)

/-- The payment of the parent's builder changes no pending payment but the one it settles.

That one is at the position of the parent's slot, when the parent is of this epoch or the last. -/
theorem settleParentPayment_payments
    (computed : settleParentPayment state gloas = .ok after) (index : Nat)
    (inRange : index < 2 * preset.SLOTS_PER_EPOCH.toNat)
    (other : (parentPaymentPosition state).map UInt64.toNat ≠ some index) :
    (after.builderPendingPayments gloas)[index] = (state.builderPendingPayments gloas)[index] := by
  unfold settleParentPayment at computed
  split at computed
  · rename_i position settled
    obtain ⟨_, payments, _⟩ := settleBuilderPayment_spec (liftAccessor_ok.mp computed)
    rw [settled] at other
    simp only [Option.map_some, ne_eq, Option.some.injEq] at other
    simp only [payments]
    exact Serialization.Ssz.RootedVector.getElem_set_ne _ _ _ _ other
  · dsimp only at computed
    split at computed <;> cases computed <;> rfl

/-! ## The latest bid -/

private theorem setValidator_latestExecutionPayloadBid {index : ValidatorIndex}
    {validator : Validator} (set : state.setValidator index validator = .ok after) :
    after.latestExecutionPayloadBid = state.latestExecutionPayloadBid := by
  obtain ⟨_, rfl⟩ := setValidator_ok set
  rfl

private theorem setBalance_latestExecutionPayloadBid {index : ValidatorIndex} {balance : Gwei}
    (set : state.setBalance index balance = .ok after) :
    after.latestExecutionPayloadBid = state.latestExecutionPayloadBid := by
  obtain ⟨_, rfl⟩ := setBalance_ok set
  rfl

private theorem exitQueue_latestExecutionPayloadBid {exitBalance : Gwei} {exitEpoch : Epoch}
    (computed : exitQueue config state exitBalance = .ok (after, exitEpoch)) :
    after.latestExecutionPayloadBid = state.latestExecutionPayloadBid := by
  unfold exitQueue at computed
  split at computed
  · simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := computed
    rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, rfl, _⟩ := computed
    rfl

private theorem initiateValidatorExit_latestExecutionPayloadBid {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) :
    after.latestExecutionPayloadBid = state.latestExecutionPayloadBid := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok computed
  · rfl
  · exact (setValidator_latestExecutionPayloadBid set).trans
      (exitQueue_latestExecutionPayloadBid queue)

private theorem processDepositRequest_latestExecutionPayloadBid {electra : .pectra ≤ fork}
    {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    after.latestExecutionPayloadBid = state.latestExecutionPayloadBid := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  rfl

private theorem requestPartialWithdrawal_latestExecutionPayloadBid {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    after.latestExecutionPayloadBid = state.latestExecutionPayloadBid := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churned
    obtain ⟨_, _, _, _, _, _, churned⟩ := churned
    cases churned
    rfl
  · cases computed
    rfl

private theorem processWithdrawalRequest_latestExecutionPayloadBid {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    after.latestExecutionPayloadBid = state.latestExecutionPayloadBid := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; rfl)
    | exact initiateValidatorExit_latestExecutionPayloadBid (liftAccessor_ok.mp computed)
    | exact requestPartialWithdrawal_latestExecutionPayloadBid computed

private theorem switchToCompoundingValidator_latestExecutionPayloadBid {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    after.latestExecutionPayloadBid = state.latestExecutionPayloadBid := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨_, _, _, set, queued⟩ := computed
  refine Eq.trans ?_ (setValidator_latestExecutionPayloadBid set)
  simp only [queueExcessActiveBalance, bind_ok_iff] at queued
  obtain ⟨_, _, queued⟩ := queued
  split at queued
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
    obtain ⟨_, _, _, _, _, set, rfl⟩ := queued
    dsimp only
    exact setBalance_latestExecutionPayloadBid set
  · cases queued
    rfl

private theorem queueConsolidation_latestExecutionPayloadBid {electra : .pectra ≤ fork}
    {sourcePosition : Nat} {source : Validator} {targetIndex : ValidatorIndex}
    (computed :
      queueConsolidation config state electra sourcePosition source targetIndex = .ok after) :
    after.latestExecutionPayloadBid = state.latestExecutionPayloadBid := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure] at computed
  obtain ⟨⟨_, _⟩, churned, _, _, _, set, _, _, computed⟩ := computed
  simp only [Except.ok.injEq] at computed
  subst computed
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at churned
  obtain ⟨_, _, _, _, _, _, churned⟩ := churned
  cases churned
  exact (setValidator_latestExecutionPayloadBid set).trans rfl

private theorem processConsolidationRequest_latestExecutionPayloadBid {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    after.latestExecutionPayloadBid = state.latestExecutionPayloadBid := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; rfl)
    | exact switchToCompoundingValidator_latestExecutionPayloadBid (liftAccessor_ok.mp computed)
    | exact queueConsolidation_latestExecutionPayloadBid computed

private theorem processBuilderDepositRequest_latestExecutionPayloadBid
    {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    after.latestExecutionPayloadBid = state.latestExecutionPayloadBid := by
  unfold processBuilderDepositRequest addBuilderToRegistry at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; rfl)

private theorem processBuilderExitRequest_latestExecutionPayloadBid
    {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    after.latestExecutionPayloadBid = state.latestExecutionPayloadBid := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · rfl
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    rfl

private theorem settleParentPayment_latestExecutionPayloadBid
    (computed : settleParentPayment state gloas = .ok after) :
    after.latestExecutionPayloadBid = state.latestExecutionPayloadBid := by
  unfold settleParentPayment at computed
  split at computed
  · have settled := liftAccessor_ok.mp computed
    unfold settleBuilderPayment at settled
    split at settled
    · cases settled
      rfl
    · cases settled
  · simp only at computed
    split at computed <;> cases computed <;> rfl

/-- The steps of a fold that each keep the latest bid keep it. -/
private theorem foldlM_latestExecutionPayloadBid {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (kept : ∀ s x s', step s x = .ok s' →
      s'.latestExecutionPayloadBid = s.latestExecutionPayloadBid)
    {items : List α} (computed : items.foldlM step state = .ok after) :
    after.latestExecutionPayloadBid = state.latestExecutionPayloadBid :=
  foldlM_ok_invariant (fun s => s.latestExecutionPayloadBid = state.latestExecutionPayloadBid)
    (fun _ _ _ before ok => (kept _ _ _ ok).trans before) rfl computed

/-- A full parent keeps the latest bid.

Its payment and its requests leave the bid as it was. -/
theorem applyParentExecutionPayload_latestExecutionPayloadBid
    {requests : ExecutionRequests preset fork}
    (computed : applyParentExecutionPayload config checks state gloas requests = .ok after) :
    after.latestExecutionPayloadBid = state.latestExecutionPayloadBid := by
  unfold applyParentExecutionPayload at computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, settled, settledOk, requested, requestedOk, _, _, rfl⟩ :=
    computed
  unfold processParentRequests at requestedOk
  simp only [bind_ok_iff, ← Array.foldlM_toList] at requestedOk
  obtain ⟨_, depositsOk, _, withdrawalsOk, _, consolidationsOk, _, buildersOk, exitsOk⟩ :=
    requestedOk
  dsimp only
  refine Eq.trans ?_ (settleParentPayment_latestExecutionPayloadBid settledOk)
  refine Eq.trans ?_ (foldlM_latestExecutionPayloadBid
    (fun _ _ _ ok => processDepositRequest_latestExecutionPayloadBid ok) depositsOk)
  refine Eq.trans ?_ (foldlM_latestExecutionPayloadBid
    (fun _ _ _ ok => processWithdrawalRequest_latestExecutionPayloadBid ok) withdrawalsOk)
  refine Eq.trans ?_ (foldlM_latestExecutionPayloadBid
    (fun _ _ _ ok => processConsolidationRequest_latestExecutionPayloadBid ok) consolidationsOk)
  refine Eq.trans ?_ (foldlM_latestExecutionPayloadBid
    (fun _ _ _ ok => processBuilderDepositRequest_latestExecutionPayloadBid ok) buildersOk)
  exact foldlM_latestExecutionPayloadBid
    (fun _ _ _ ok => processBuilderExitRequest_latestExecutionPayloadBid ok) exitsOk

end EthLib.Consensus
