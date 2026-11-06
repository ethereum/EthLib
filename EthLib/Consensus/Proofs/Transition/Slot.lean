module

public import EthLib.Consensus.Proofs.Transition.BuilderRequests
public import EthLib.Consensus.Proofs.Transition.Execution
public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.ParentPayload
public import EthLib.Consensus.Proofs.Transition.Payload
public import EthLib.Consensus.Proofs.Transition.Requests
public import EthLib.Consensus.Proofs.Transition.SyncAggregate
public import EthLib.Consensus.Proofs.Transition.Withdrawals

/-!
# Proofs: a block keeps the slot of the state

No step of a block moves the slot of the state, at any fork.

A valid block runs on the state advanced to its slot, which is later than the slot before.

So the state after a valid block sits at the slot of the block.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-! ## Withdrawals -/

theorem applyWithdrawal_slot {withdrawal : Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) : after.slot = state.slot := by
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, set⟩ := computed
    exact setBuilder_slot set
  · exact (frame_decreaseBalance computed).slot

theorem updateNextWithdrawalIndex_slot {withdrawals : Array Withdrawal}
    (computed : updateNextWithdrawalIndex state withdrawals = .ok after) :
    after.slot = state.slot := by
  unfold updateNextWithdrawalIndex at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    rfl
  · cases computed
    rfl

theorem updateNextWithdrawalValidatorIndex_slot {capella : .shapella ≤ fork}
    {withdrawals : Array Withdrawal}
    (computed : updateNextWithdrawalValidatorIndex state capella withdrawals = .ok after) :
    after.slot = state.slot := by
  unfold updateNextWithdrawalValidatorIndex at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · cases computed
  · cases computed
    rfl

theorem updateNextWithdrawalBuilderIndex_slot {gloas : .glamsterdam ≤ fork} {count : Nat}
    (computed : updateNextWithdrawalBuilderIndex state gloas count = .ok after) :
    after.slot = state.slot := by
  unfold updateNextWithdrawalBuilderIndex at computed
  dsimp only at computed
  split at computed
  · cases computed
    rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    rfl

theorem applyExpectedWithdrawals_slot {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    after.slot = state.slot := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, swept, sweptOk, last⟩ := computed
  have one : applied.slot = state.slot := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact foldlM_ok_invariant (fun s : BeaconState preset fork => s.slot = state.slot)
      (fun _ _ _ same step => (applyWithdrawal_slot step).trans same) rfl appliedOk
  have three : swept.slot = indexed.slot := by
    split at sweptOk
    · rw [updateNextWithdrawalBuilderIndex_slot sweptOk]
      split <;> rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at sweptOk
      rw [← sweptOk]
      split <;> rfl
  rw [updateNextWithdrawalValidatorIndex_slot last, three, updateNextWithdrawalIndex_slot indexedOk,
    one]

theorem processWithdrawals_slot {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) :
    after.slot = state.slot := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, applied⟩ := computed
      exact applyExpectedWithdrawals_slot applied
    · cases computed
      rfl
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact applyExpectedWithdrawals_slot applied

theorem processBlsToExecutionChange_slot {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    after.slot = state.slot := by
  obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact setValidator_slot set

/-! ## The execution payload -/

theorem processExecutionPayload_slot {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    after.slot = state.slot := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  rfl

/-! ## Operations -/

theorem processAttestation_slot {attestation : Attestation preset fork} {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    after.slot = state.slot := by
  by_cases altair : Fork.altair ≤ fork
  · simp only [processAttestation, altair, ↓reduceDIte] at computed
    unfold processAttestationAltair at computed
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := computed
    have last : after.slot = raised.slot := by
      split at final
      · rw [recordPaymentWeight_eq final]
      · cases final
        rfl
    rw [last, (frame_increaseBalance raisedOk).slot]
    unfold setEpochParticipation
    split <;> rfl
  · exact (frame_processAttestation (Nat.lt_of_not_le altair) computed).slot

theorem addValidatorToRegistry_slot {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    after.slot = state.slot := by
  unfold addValidatorToRegistry at computed
  split at computed
  · unfold addValidatorToRegistryAltair at computed
    simp only [liftAccessor_ok, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
    rfl
  · split at computed
    · cases computed
      rfl
    · cases computed

theorem applyPendingDeposit_slot {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    after.slot = state.slot := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      rfl
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact addValidatorToRegistry_slot computed
    · cases computed
      rfl
  · exact (frame_increaseBalance (liftAccessor_ok.mp computed)).slot

theorem applyDepositElectra_slot {electra : .pectra ≤ fork} {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei} {signature : BLSSignature}
    (computed : applyDepositElectra config checks state electra pubkey withdrawalCredentials
      amount signature = .ok after) :
    after.slot = state.slot := by
  unfold applyDepositElectra at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, added, pushed⟩ := computed
      obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
      exact (addValidatorToRegistry_slot added :)
    · cases computed
      rfl
  · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
    rfl

theorem applyDeposit_slot {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    after.slot = state.slot := by
  unfold applyDeposit at computed
  split at computed
  · exact applyDepositElectra_slot computed
  · exact applyPendingDeposit_slot computed

theorem processDeposit_slot {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    after.slot = state.slot := by
  obtain ⟨_, _, _, _, applied⟩ := processDeposit_ok computed
  exact (applyDeposit_slot applied :)

/-! ## Requests of the execution layer -/

theorem computeExitEpochAndUpdateChurn_slot {electra : .pectra ≤ fork} {exitBalance : Gwei}
    {epoch : Epoch}
    (computed :
      computeExitEpochAndUpdateChurn config state electra exitBalance = .ok (after, epoch)) :
    after.slot = state.slot := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  rfl

theorem computeConsolidationEpochAndUpdateChurn_slot {electra : .pectra ≤ fork} {balance : Gwei}
    {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (after, epoch)) :
    after.slot = state.slot := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  rfl

theorem switchToCompoundingValidator_slot {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    after.slot = state.slot := by
  simp only [switchToCompoundingValidator, queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨_, _, _, set, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, setB, rfl⟩ := computed
    exact (setBalance_slot setB).trans (setValidator_slot set)
  · cases computed
    exact setValidator_slot set

theorem processDepositRequest_slot {electra : .pectra ≤ fork} {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    after.slot = state.slot := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  rfl

theorem processWithdrawalRequest_slot {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    after.slot = state.slot := by
  unfold processWithdrawalRequest requestPartialWithdrawal at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; rfl)
    | exact (frame_initiateValidatorExit (liftAccessor_ok.mp computed)).slot
    | skip
  all_goals
    rename_i pair churned _ _ _ _ _ _
    cases computed
    exact computeExitEpochAndUpdateChurn_slot (after := pair.1) (epoch := pair.2)
      (liftAccessor_ok.mp churned)

theorem queueConsolidation_slot {electra : .pectra ≤ fork} {sourcePosition : Nat}
    {source : Validator} {targetIndex : ValidatorIndex}
    (computed :
      queueConsolidation config state electra sourcePosition source targetIndex = .ok after) :
    after.slot = state.slot := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨⟨_, _⟩, churned, computed⟩ := computed
  simp only [Except.ok.injEq] at computed
  obtain ⟨_, _, _, set, _, _, rfl⟩ := computed
  exact (setValidator_slot set).trans (computeConsolidationEpochAndUpdateChurn_slot churned)

theorem processConsolidationRequest_slot {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    after.slot = state.slot := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; rfl)
    | exact switchToCompoundingValidator_slot (liftAccessor_ok.mp computed)
    | exact queueConsolidation_slot computed

theorem processOperations_slot {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    after.slot = state.slot := by
  have fold {α : Type} {step : BeaconState preset fork → α → Except TransitionError _}
      (keeps : ∀ s x s', step s x = .ok s' → s'.slot = s.slot) {items : List α}
      {start finish : BeaconState preset fork} (folded : items.foldlM step start = .ok finish) :
      finish.slot = start.slot :=
    foldlM_ok_invariant (fun s : BeaconState preset fork => s.slot = start.slot)
      (fun _ _ _ same ok => (keeps _ _ _ ok).trans same) rfl folded
  unfold processOperations at computed
  split at computed
  · unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, proposers, proposersOk, attesters,
      attestersOk, attested, attestedOk, exited, exitsOk, changed, changesOk, paid⟩ := computed
    rw [fold (fun _ _ _ ok => by rw [processPayloadAttestation_eq ok]) paid,
      fold (fun _ _ _ ok => processBlsToExecutionChange_slot ok) changesOk,
      fold (fun _ _ _ ok => (frame_processVoluntaryExit ok).slot) exitsOk,
      fold (fun _ _ _ ok => processAttestation_slot ok) attestedOk,
      fold (fun _ _ _ ok => (frame_processAttesterSlashing ok).slot) attestersOk,
      fold (fun _ _ _ ok => (frame_processProposerSlashing ok).slot) proposersOk]
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, proposers, proposersOk, attesters, attestersOk, attested, attestedOk,
    deposited, depositedOk, exited, exitsOk, changed, changesOk, requestsOk⟩ := computed
  have last : after.slot = changed.slot := by
    split at requestsOk
    · simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at requestsOk
      obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := requestsOk
      rw [fold (fun _ _ _ ok => processConsolidationRequest_slot ok) consolidationsOk,
        fold (fun _ _ _ ok => processWithdrawalRequest_slot ok) withdrawalsOk,
        fold (fun _ _ _ ok => processDepositRequest_slot ok) depositsOk]
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      rw [requestsOk]
  have changes : changed.slot = exited.slot := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact fold (fun _ _ _ ok => processBlsToExecutionChange_slot ok) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      rw [changesOk]
  rw [last, changes, fold (fun _ _ _ ok => (frame_processVoluntaryExit ok).slot) exitsOk,
    fold (fun _ _ _ ok => processDeposit_slot ok) depositedOk,
    fold (fun _ _ _ ok => processAttestation_slot ok) attestedOk,
    fold (fun _ _ _ ok => (frame_processAttesterSlashing ok).slot) attestersOk,
    fold (fun _ _ _ ok => (frame_processProposerSlashing ok).slot) proposersOk]

/-! ## The parent payload and the execution part of a block -/

theorem processBuilderDepositRequest_slot {gloas : .glamsterdam ≤ fork}
    {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    after.slot = state.slot := by
  unfold processBuilderDepositRequest addBuilderToRegistry BeaconState.putBuilder at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first | (cases computed; done) | (cases computed; rfl)

theorem processBuilderExitRequest_slot {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    after.slot = state.slot := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · rfl
  · simp only [initiateBuilderExit, bind_ok_iff, liftArith, mapError_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    exact setBuilder_slot set

theorem settleParentPayment_slot {gloas : .glamsterdam ≤ fork}
    (computed : settleParentPayment state gloas = .ok after) : after.slot = state.slot := by
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

theorem processParentExecutionPayload_slot {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    after.slot = state.slot := by
  have fold {α : Type} {step : BeaconState preset fork → α → Except TransitionError _}
      (keeps : ∀ s x s', step s x = .ok s' → s'.slot = s.slot) {items : List α}
      {start finish : BeaconState preset fork} (folded : items.foldlM step start = .ok finish) :
      finish.slot = start.slot :=
    foldlM_ok_invariant (fun s : BeaconState preset fork => s.slot = start.slot)
      (fun _ _ _ same ok => (keeps _ _ _ ok).trans same) rfl folded
  unfold processParentExecutionPayload at computed
  dsimp only at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    rfl
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, applied⟩ := computed
  unfold applyParentExecutionPayload at applied
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at applied
  obtain ⟨_, _, _, _, _, _, _, _, settled, settledOk, requested, requestedOk, _, _, rfl⟩ :=
    applied
  unfold processParentRequests at requestedOk
  simp only [bind_ok_iff, ← Array.foldlM_toList] at requestedOk
  obtain ⟨_, depositsOk, _, withdrawalsOk, _, consolidationsOk, _, builderDepositsOk, exitsOk⟩ :=
    requestedOk
  change requested.slot = state.slot
  rw [fold (fun _ _ _ ok => processBuilderExitRequest_slot ok) exitsOk,
    fold (fun _ _ _ ok => processBuilderDepositRequest_slot ok) builderDepositsOk,
    fold (fun _ _ _ ok => processConsolidationRequest_slot ok) consolidationsOk,
    fold (fun _ _ _ ok => processWithdrawalRequest_slot ok) withdrawalsOk,
    fold (fun _ _ _ ok => processDepositRequest_slot ok) depositsOk,
    settleParentPayment_slot settledOk]

theorem processExecutionPayloadBid_slot {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    after.slot = state.slot := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok computed
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    rfl
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at recordedOk
    subst recordedOk
    rfl

theorem processBlockExecution_slot {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    after.slot = state.slot := by
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨withdrawn, withdrawnOk, bid⟩ := computed
    exact (processExecutionPayloadBid_slot bid).trans (processWithdrawals_slot withdrawnOk)
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨withdrawn, withdrawnOk, paid⟩ := computed
    exact (processExecutionPayload_slot paid).trans (processWithdrawals_slot withdrawnOk)
  · dsimp only at computed
    split at computed
    · exact processExecutionPayload_slot computed
    · cases computed
      rfl

/-! ## The sync aggregate -/

theorem processSyncAggregate_slot {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    after.slot = state.slot := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  refine foldlM_ok_invariant (fun s : BeaconState preset fork => s.slot = state.slot)
    (fun _ _ _ same step => ?_) rfl folded
  unfold applySyncReward at step
  split at step
  · simp only [bind_ok_iff, liftAccessor_ok] at step
    obtain ⟨_, raised, _, _, paid⟩ := step
    rw [(frame_increaseBalance paid).slot, (frame_increaseBalance raised).slot, same]
  · rw [(frame_decreaseBalance (liftAccessor_ok.mp step)).slot, same]

/-! ## Blocks -/

/-- No block moves the slot of the state that it runs on. -/
theorem processBlock_slot {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    after.slot = state.slot := by
  by_cases altair : Fork.altair ≤ fork
  · simp only [processBlock, altair, ↓reduceDIte] at computed
    unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid, paidOk, headed, headedOk, computed⟩ := computed
    -- From Gloas the payload of the parent runs before the header.
    have paidSlot : paid.slot = state.slot := by
      split at paidOk
      · exact processParentExecutionPayload_slot paidOk
      · cases paidOk
        rfl
    obtain ⟨executed, executedOk, revealed, revealedOk, voted, votedOk, operated, operatedOk,
      synced⟩ := computed
    -- From Bellatrix the execution part runs between the header and the RANDAO reveal.
    have executedSlot : executed.slot = headed.slot := by
      split at executedOk
      · exact processBlockExecution_slot executedOk
      · cases executedOk
        rfl
    -- Heze drops the vote on the deposit contract.
    have votedSlot : voted.slot = revealed.slot := by
      split at votedOk
      · exact (frame_processEth1Data votedOk).slot
      · cases votedOk
        rfl
    rw [processSyncAggregate_slot synced, processOperations_slot operatedOk, votedSlot,
      (frame_processRandao revealedOk).slot, executedSlot, (frame_processBlockHeader headedOk).slot,
      paidSlot]
  · simp only [processBlock, altair, ↓reduceDIte, bind_ok_iff] at computed
    obtain ⟨headed, headedOk, revealed, revealedOk, voted, votedOk, operated⟩ := computed
    rw [processOperations_slot operated, (frame_processEth1Data votedOk).slot,
      (frame_processRandao revealedOk).slot, (frame_processBlockHeader headedOk).slot]

/-- A valid block runs on a state at an earlier slot, and leaves the state at its own slot. -/
theorem stateTransition_slot {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    state.slot < signed.message.slot ∧ after.slot = signed.message.slot := by
  obtain ⟨advanced, slotsOk, advancedSlot, -, blockOk, -⟩ := stateTransition_ok computed
  refine ⟨?_, (processBlock_slot blockOk).trans advancedSlot⟩
  unfold processSlots at slotsOk
  simp only [bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, later, _⟩ := slotsOk
  exact later

end EthLib.Consensus
