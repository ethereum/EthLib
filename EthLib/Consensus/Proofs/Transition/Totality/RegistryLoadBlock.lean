module

public import EthLib.Consensus.Proofs.Transition.Totality.RegistryLoad

/-!
# Proofs: a block raises the validators plus the pending deposits by a bounded amount

A block adds validators and pending deposits through three kinds of operations only.

Before Heze a block carries deposits of the deposit contract.

Before Electra each such deposit adds a validator or tops one up, so it adds at most one.

From Electra a deposit with a new key adds a validator and a pending deposit, so at most two.

A deposit with a known key only adds a pending deposit.

From Fulu a block must carry no such deposit, and from Gloas it applies none.

From Electra a block also runs requests of the execution layer.

In Electra and Fulu they come from the payload of the block itself.

From Gloas they come from the payload of its parent.

[EIP-6110] adds the deposit requests, and each adds at most one pending deposit.

A consolidation request adds at most one, when it switches a validator to compounding credentials.

A withdrawal request and every other operation of a block add no validator and no pending deposit.

So a block raises the count by at most its deposits, twice from Electra, plus those requests.

[EIP-6110]: https://eips.ethereum.org/EIPS/eip-6110#consensus-layer
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-- The number of deposits of the deposit contract that a block applies, before Gloas. -/
def blockDepositCount (body : BeaconBlockBody preset fork) : Nat :=
  if before : fork < .glamsterdam then
    (body.deposits (Nat.lt_trans before (by decide))).data.size
  else 0

/-- The number of deposit requests plus consolidation requests that a block runs.

In Electra and Fulu they are the requests of its own payload.

From Gloas they are the requests of the payload of its parent. -/
def blockRequestCount (body : BeaconBlockBody preset fork) : Nat :=
  if electra : .pectra ≤ fork ∧ fork < .glamsterdam then
    (body.executionRequests electra).deposits.data.size +
      (body.executionRequests electra).consolidations.data.size
  else if gloas : .glamsterdam ≤ fork then
    (body.parentExecutionRequests gloas).deposits.data.size +
      (body.parentExecutionRequests gloas).consolidations.data.size
  else 0

/-- The most that a block can raise the validators plus the pending deposits.

It counts each deposit once, or twice from Electra.

It also counts each deposit request and each consolidation request. -/
def blockLoadBound (body : BeaconBlockBody preset fork) : Nat :=
  (if .pectra ≤ fork then 2 else 1) * blockDepositCount body + blockRequestCount body

/-! ## Steps that keep the count -/

/-- Unchanged sizes of the registry and the balances, and an unchanged queue, keep the count. -/
private theorem loadKept_of_sameSizes (sizes : SameSizes state after)
    (queue : after.pendingDeposits = state.pendingDeposits) : LoadKept state after :=
  ⟨sizes.1, queue⟩

/-- A write to a validator keeps the count. -/
private theorem loadKept_setValidator {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after) : LoadKept state after := by
  refine loadKept_of_sameSizes (sameSizes_setValidator set) ?_
  obtain ⟨_, rfl⟩ := setValidator_ok set
  rfl

/-- Slashing a validator keeps the count. -/
private theorem loadKept_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    LoadKept state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, exitedOk, -, -, markedOk, -, -, -, loweredOk, -, -,
    raisedOk, lastOk, rfl⟩ := slashValidator_ok computed
  refine (loadKeptLaws.initiateValidatorExit exitedOk).trans <|
    (loadKept_setValidator markedOk).trans <| LoadKept.trans LoadKept.of_validators <|
    (loadKeptLaws.decreaseBalance loweredOk).trans <|
    (loadKeptLaws.increaseBalance raisedOk).trans <|
    (loadKeptLaws.increaseBalance lastOk).trans ?_
  split
  · exact LoadKept.of_validators
  · exact LoadKept.refl _

/-- A proposer slashing keeps the count. -/
private theorem loadKept_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    LoadKept state after := by
  have sizes := sameSizes_processProposerSlashing computed
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact loadKept_of_sameSizes sizes (loadKept_slashValidator slashed).2

/-- An attester slashing keeps the count. -/
private theorem loadKept_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    LoadKept state after := by
  have sizes := sameSizes_processAttesterSlashing computed
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  refine loadKept_of_sameSizes sizes ?_
  refine foldlM_ok_invariant (fun step => step.1.pendingDeposits = state.pendingDeposits)
    (fun step _ next before ok => ?_)
    (show (state, false).1.pendingDeposits = state.pendingDeposits from rfl) folded
  obtain ⟨middle, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact (loadKept_slashValidator slashed).2.trans before
  · simp only [pure, Except.pure, Except.ok.injEq] at ok
    exact ok ▸ before

/-- An attestation keeps the count. -/
private theorem loadKept_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    LoadKept state after := by
  refine loadKept_of_sameSizes (sameSizes_processAttestation computed) ?_
  unfold processAttestation at computed
  split at computed
  · unfold processAttestationAltair at computed
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := computed
    have last : after.pendingDeposits = raised.pendingDeposits := by
      split at final
      · rw [recordPaymentWeight_eq final]
      · cases final
        rfl
    refine last.trans ((loadKeptLaws.increaseBalance raisedOk).2.trans ?_)
    unfold setEpochParticipation
    split <;> rfl
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
  have kept := recordPendingAttestation_ok recorded
  split at kept
  all_goals
    obtain ⟨_, rest⟩ := kept
    rw [← rest]

/-- The churn of exits keeps the count. -/
private theorem loadKept_computeExitEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {exitBalance : Gwei} {epoch : Epoch}
    (computed :
      computeExitEpochAndUpdateChurn config state electra exitBalance = .ok (after, epoch)) :
    LoadKept state after := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact LoadKept.of_validators

/-- The churn of consolidations keeps the count. -/
private theorem loadKept_computeConsolidationEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {balance : Gwei} {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (after, epoch)) :
    LoadKept state after := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact LoadKept.of_validators

/-- A partial withdrawal that a request queues keeps the count. -/
private theorem loadKept_requestPartialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    LoadKept state after := by
  refine loadKept_of_sameSizes (sameSizes_requestPartialWithdrawal computed) ?_
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    exact (loadKept_computeExitEpochAndUpdateChurn churned).2
  · cases computed
    rfl

/-- A withdrawal request keeps the count. -/
private theorem loadKept_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    LoadKept state after := by
  refine loadKept_of_sameSizes (sameSizes_processWithdrawalRequest computed) ?_
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; rfl)
    | exact (loadKeptLaws.initiateValidatorExit (liftAccessor_ok.mp computed)).2
    | exact (loadKept_requestPartialWithdrawal computed).2

/-- A consolidation of two validators keeps the count. -/
private theorem loadKept_queueConsolidation {electra : .pectra ≤ fork}
    {sourceIndex : ValidatorIndex} {source : Validator} {targetIndex : ValidatorIndex}
    (computed :
      queueConsolidation config state electra sourceIndex source targetIndex = .ok after) :
    LoadKept state after := by
  refine loadKept_of_sameSizes (sameSizes_queueConsolidation computed) ?_
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    Uint64.addChecked_ok_iff, pure, Except.pure] at computed
  obtain ⟨⟨_, _⟩, churned, _, _, _, set, _, _, computed⟩ := computed
  simp only [Except.ok.injEq] at computed
  subst computed
  exact (loadKept_setValidator set).2.trans
    (loadKept_computeConsolidationEpochAndUpdateChurn churned).2

/-- A withdrawal keeps the count. -/
private theorem loadKept_applyWithdrawal {withdrawal : Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) : LoadKept state after := by
  refine loadKept_of_sameSizes (sameSizes_applyWithdrawal computed) ?_
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, set⟩ := computed
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    rfl
  · exact (loadKeptLaws.decreaseBalance computed).2

/-- The expected withdrawals keep the count. -/
private theorem loadKept_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    LoadKept state after := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : LoadKept state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact LoadKept.foldlM (fun _ _ _ ok => loadKept_applyWithdrawal ok) appliedOk
  have indexedStep : LoadKept applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      exact LoadKept.of_validators
    · cases indexedOk
      exact LoadKept.refl _
  have queued : ∀ kept : BeaconState preset fork,
      LoadKept kept (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals kept gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else kept) := by
    intro kept
    split <;> exact LoadKept.of_validators
  have partials : ∀ kept : BeaconState preset fork,
      LoadKept kept (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals kept electra expected.processedPartialWithdrawalsCount
      else kept) := by
    intro kept
    split <;> exact LoadKept.of_validators
  have swept : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → LoadKept kept finished := by
    intro kept ok
    split at ok
    · unfold updateNextWithdrawalBuilderIndex at ok
      dsimp only at ok
      split at ok
      · cases ok
        exact LoadKept.of_validators
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
        obtain ⟨_, _, rfl⟩ := ok
        exact LoadKept.of_validators
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ LoadKept.refl _
  have lastStep : LoadKept finished after := by
    unfold updateNextWithdrawalValidatorIndex at last
    simp only [bind_ok_iff] at last
    obtain ⟨_, _, last⟩ := last
    split at last
    · cases last
    · cases last
      exact LoadKept.of_validators
  exact one.trans <| indexedStep.trans <| (queued _).trans <| (partials _).trans <|
    (swept _ sweptOk).trans lastStep

/-- The withdrawals of a block keep the count. -/
private theorem loadKept_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) : LoadKept state after := by
  refine loadKept_of_sameSizes (sameSizes_processWithdrawals computed) ?_
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, applied⟩ := computed
      exact (loadKept_applyExpectedWithdrawals applied).2
    · cases computed
      rfl
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact (loadKept_applyExpectedWithdrawals applied).2

/-- The execution part of a block keeps the count. -/
private theorem loadKept_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    LoadKept state after := by
  have payload {s t : BeaconState preset fork}
      {execution : .bellatrix ≤ fork ∧ fork < .glamsterdam}
      (ok : processExecutionPayload config engine s body execution = .ok t) : LoadKept s t := by
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
    exact LoadKept.of_validators
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    obtain ⟨_, rfl⟩ := processExecutionPayloadBid_eq bid
    exact (loadKept_processWithdrawals withdrawnOk).trans LoadKept.of_validators
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact (loadKept_processWithdrawals withdrawnOk).trans (payload paid)
  · dsimp only at computed
    split at computed
    · exact payload computed
    · cases computed
      exact LoadKept.refl _

/-! ## Steps that raise the count -/

/-- A fold raises the count by at most its length times the bound of each of its steps. -/
private theorem foldlM_registryLoad_le {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)} {bound : Nat}
    (each : ∀ s x s', step s x = .ok s' → registryLoad s' ≤ registryLoad s + bound) :
    ∀ (items : List α) {state after : BeaconState preset fork},
      items.foldlM step state = .ok after →
        registryLoad after ≤ registryLoad state + bound * items.length
  | [], _, _, computed => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp
  | _ :: rest, _, _, computed => by
    simp only [List.foldlM, bind_ok_iff] at computed
    obtain ⟨_, first, tail⟩ := computed
    have one := each _ _ _ first
    have more := foldlM_registryLoad_le each rest tail
    simp only [List.length_cons, Nat.mul_succ]
    omega

/-- A pending deposit added to the queue raises the count by one. -/
private theorem registryLoad_addPendingDeposit {electra : .pectra ≤ fork}
    {deposit : PendingDeposit} (computed : addPendingDeposit state electra deposit = .ok after) :
    registryLoad after = registryLoad state + 1 := by
  simp only [addPendingDeposit, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨pending, appended, rfl⟩ := computed
  simp only [registryLoad, electra, ↓reduceDIte, appendWithinLimit_data appended, Array.size_push]
  omega

/-- A new validator raises the count by one. -/
private theorem registryLoad_addValidatorToRegistry {pubkey withdrawalCredentials amount}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    registryLoad after = registryLoad state + 1 := by
  have size : after.validators.data.size = state.validators.data.size + 1 := by
    rw [addValidatorToRegistry_validators_eq_push computed, Array.size_push]
  have pending : after.pendingDeposits = state.pendingDeposits := by
    unfold addValidatorToRegistry at computed
    split at computed
    · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at computed
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
      rfl
    split at computed
    · cases computed
      rfl
    · cases computed
  unfold registryLoad
  rw [size, pending]
  omega

/-- From Electra a deposit raises the count by at most two. -/
private theorem applyDepositElectra_registryLoad_le {electra : .pectra ≤ fork}
    {pubkey : Cryptography.Bls.BLSPubkey} {withdrawalCredentials : Bytes32} {amount : Gwei}
    {signature : Cryptography.Bls.BLSSignature}
    (computed : applyDepositElectra config checks state electra pubkey withdrawalCredentials
      amount signature = .ok after) :
    registryLoad after ≤ registryLoad state + 2 := by
  unfold applyDepositElectra at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, added, pushed⟩ := computed
      have one := registryLoad_addValidatorToRegistry added
      have two := registryLoad_addPendingDeposit pushed
      omega
    · cases computed
      omega
  · have one := registryLoad_addPendingDeposit (liftAccessor_ok.mp computed)
    omega

/-- Before Electra a deposit raises the count by at most one. -/
private theorem applyPendingDeposit_registryLoad_le (early : ¬ .pectra ≤ fork)
    {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    registryLoad after ≤ registryLoad state + 1 := by
  have size := (applyPendingDeposit_validators_size_le_and_mem computed).1
  simp only [registryLoad, early, ↓reduceDIte]
  omega

/-- A deposit of a block raises the count by at most one, and from Electra by at most two. -/
private theorem processDeposit_registryLoad_le {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    registryLoad after ≤ registryLoad state + (if .pectra ≤ fork then 2 else 1) := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  have indexed : LoadKept state { state with eth1DepositIndex := fun _ => next } :=
    LoadKept.of_validators
  rw [← indexed.registryLoad_eq]
  unfold applyDeposit at applied
  split at applied
  · rename_i electra
    simp only [electra, ↓reduceIte]
    exact applyDepositElectra_registryLoad_le applied
  · rename_i early
    simp only [early, ↓reduceIte]
    exact applyPendingDeposit_registryLoad_le early applied

/-- A deposit request raises the count by at most one. -/
private theorem processDepositRequest_registryLoad_le {electra : .pectra ≤ fork}
    {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    registryLoad after ≤ registryLoad state + 1 := by
  obtain ⟨pushed, validators, -⟩ := processDepositRequest_ok computed
  simp only [registryLoad, electra, ↓reduceDIte, pushed, validators, Array.size_push]
  omega

/-- Queueing the excess balance of a validator raises the count by at most one. -/
private theorem queueExcessActiveBalance_registryLoad_le {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : queueExcessActiveBalance state electra index = .ok after) :
    registryLoad after ≤ registryLoad state + 1 := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, pending, appended, _, set, rfl⟩ := computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    simp only [registryLoad, electra, ↓reduceDIte, appendWithinLimit_data appended,
      Array.size_push, BeaconState.putBalance]
    omega
  · cases computed
    omega

/-- A switch to compounding credentials raises the count by at most one. -/
private theorem switchToCompoundingValidator_registryLoad_le {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    registryLoad after ≤ registryLoad state + 1 := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨_, _, _, set, queued⟩ := computed
  have one := (loadKept_setValidator set).registryLoad_eq
  have two := queueExcessActiveBalance_registryLoad_le queued
  omega

/-- A consolidation request raises the count by at most one. -/
private theorem processConsolidationRequest_registryLoad_le {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    registryLoad after ≤ registryLoad state + 1 := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; omega)
    | exact switchToCompoundingValidator_registryLoad_le (liftAccessor_ok.mp computed)
    | exact Nat.le_trans (Nat.le_of_eq (loadKept_queueConsolidation computed).registryLoad_eq)
        (Nat.le_add_right _ _)

/-- In Electra and Fulu a payload raises the count by at most its requests.

Only its deposit and consolidation requests count. -/
private theorem processExecutionRequests_registryLoad_le {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    registryLoad after ≤ registryLoad state +
      ((body.executionRequests electra).deposits.data.size +
        (body.executionRequests electra).consolidations.data.size) := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  have one := foldlM_registryLoad_le
    (fun _ _ _ ok => processDepositRequest_registryLoad_le ok) _ depositsOk
  have two := (LoadKept.foldlM (fun _ _ _ ok => loadKept_processWithdrawalRequest ok)
    withdrawalsOk).registryLoad_eq
  have three := foldlM_registryLoad_le
    (fun _ _ _ ok => processConsolidationRequest_registryLoad_le ok) _ consolidationsOk
  simp only [Array.length_toList, Nat.one_mul] at one three
  omega

/-- From Gloas the parent payload raises the count by at most its requests.

Only its deposit and consolidation requests count. -/
private theorem processParentExecutionPayload_registryLoad_le {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    registryLoad after ≤ registryLoad state +
      ((body.parentExecutionRequests gloas).deposits.data.size +
        (body.parentExecutionRequests gloas).consolidations.data.size) := by
  rcases processParentExecutionPayload_ok computed with ⟨-, -, rfl⟩ |
    ⟨-, settled, _, _, _, _, exited, _, settledOk, depositsOk, withdrawalsOk, consolidationsOk,
      buildersOk, exitsOk, -, final⟩
  · omega
  have zero : LoadKept state settled := by
    rw [settleParentPayment_eq settledOk]
    exact LoadKept.of_validators
  have one := foldlM_registryLoad_le
    (fun _ _ _ ok => processDepositRequest_registryLoad_le ok) _ depositsOk
  have two := (LoadKept.foldlM (fun _ _ _ ok => loadKept_processWithdrawalRequest ok)
    withdrawalsOk).registryLoad_eq
  have three := foldlM_registryLoad_le
    (fun _ _ _ ok => processConsolidationRequest_registryLoad_le ok) _ consolidationsOk
  have four := (LoadKept.foldlM (fun _ _ _ ok => by
    obtain ⟨_, rfl⟩ := processBuilderDepositRequest_builders ok
    exact LoadKept.of_validators) buildersOk).registryLoad_eq
  have five := (LoadKept.foldlM (fun _ _ _ ok => by
    obtain ⟨_, rfl⟩ := processBuilderExitRequest_builders ok
    exact LoadKept.of_validators) exitsOk).registryLoad_eq
  have six : LoadKept exited after := by
    rw [final]
    exact LoadKept.of_validators
  have seven := zero.registryLoad_eq
  have eight := six.registryLoad_eq
  simp only [Array.length_toList, Nat.one_mul] at one three
  omega

/-- The operations raise the count by at most the deposits, twice from Electra, and the requests.

From Gloas they keep the count. -/
private theorem processOperations_registryLoad_le {body : BeaconBlockBody preset fork}
    {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    registryLoad after ≤ registryLoad state +
      (if .glamsterdam ≤ fork then 0 else
        (if .pectra ≤ fork then 2 else 1) * blockDepositCount body + blockRequestCount body) := by
  unfold processOperations at computed
  split at computed
  · rename_i gloas
    unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
    have same := (LoadKept.foldlM (fun _ _ _ ok => loadKept_processProposerSlashing ok)
      proposersOk).trans <|
      (LoadKept.foldlM (fun _ _ _ ok => loadKept_processAttesterSlashing ok) attestersOk).trans <|
      (LoadKept.foldlM (fun _ _ _ ok => loadKept_processAttestation ok) attestedOk).trans <|
      (LoadKept.foldlM (fun _ _ _ ok => loadKeptLaws.processVoluntaryExit ok) exitsOk).trans <|
      (LoadKept.foldlM (fun _ _ _ ok => loadKeptLaws.processBlsToExecutionChange ok)
        changesOk).trans <|
      LoadKept.foldlM (fun _ _ _ ok => by
        rw [processPayloadAttestation_eq ok]
        exact LoadKept.refl _) paid
    simp only [gloas, ↓reduceIte]
    exact Nat.le_of_eq same.registryLoad_eq
  rename_i gloas
  have early : fork < .hegota := Nat.lt_trans (Nat.lt_of_not_le gloas) (by decide)
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, exited,
    exitsOk, changed, changesOk, requestsOk⟩ := computed
  have before := (LoadKept.foldlM (fun _ _ _ ok => loadKept_processProposerSlashing ok)
    proposersOk).trans <|
    (LoadKept.foldlM (fun _ _ _ ok => loadKept_processAttesterSlashing ok) attestersOk).trans <|
    LoadKept.foldlM (fun _ _ _ ok => loadKept_processAttestation ok) attestedOk
  have deposited := foldlM_registryLoad_le
    (fun _ _ _ ok => processDeposit_registryLoad_le ok) _ depositedOk
  have exits := (LoadKept.foldlM (fun _ _ _ ok => loadKeptLaws.processVoluntaryExit ok)
    exitsOk).registryLoad_eq
  have changes : LoadKept exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact LoadKept.foldlM (fun _ _ _ ok => loadKeptLaws.processBlsToExecutionChange ok) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ LoadKept.refl _
  have requested : registryLoad after ≤ registryLoad changed + blockRequestCount body := by
    split at requestsOk
    · rename_i electra
      have range : Fork.pectra ≤ fork ∧ fork < .glamsterdam := ⟨electra, Nat.lt_of_not_le gloas⟩
      have bound := processExecutionRequests_registryLoad_le requestsOk
      simp only [blockRequestCount, range, and_self, ↓reduceDIte]
      exact bound
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      subst requestsOk
      omega
  have one := before.registryLoad_eq
  have two := changes.registryLoad_eq
  have preGloas : fork < .glamsterdam := Nat.lt_of_not_le gloas
  simp only [gloas, ↓reduceIte, blockDepositCount, preGloas, ↓reduceDIte]
  simp only [Array.length_toList] at deposited
  generalize (if Fork.pectra ≤ fork then 2 else 1) = perDeposit at *
  omega

/-- From Gloas the steps before the operations raise the count by at most the parent requests.

Before Gloas they keep the count. -/
private theorem operationsInput_registryLoad_le {block : BeaconBlock preset fork}
    {input : BeaconState preset fork}
    (started : OperationsInput config checks engine state block input) :
    registryLoad input ≤ registryLoad state +
      (if .glamsterdam ≤ fork then blockRequestCount block.body else 0) := by
  obtain ⟨parented, headed, executed, revealed, paidOk, headerOk, executionOk, randaoOk,
    eth1Ok⟩ := started
  have paid : registryLoad parented ≤ registryLoad state +
      (if .glamsterdam ≤ fork then blockRequestCount block.body else 0) := by
    split at paidOk
    · rename_i gloas
      have notElectra : ¬ (Fork.pectra ≤ fork ∧ fork < .glamsterdam) :=
        fun range => Nat.not_le_of_lt range.2 gloas
      have bound := processParentExecutionPayload_registryLoad_le paidOk
      simp only [gloas, ↓reduceIte, blockRequestCount, notElectra, ↓reduceDIte]
      exact bound
    · cases paidOk
      omega
  have header : LoadKept parented headed := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headerOk
    exact LoadKept.of_validators
  have execution : LoadKept headed executed := by
    split at executionOk
    · exact loadKept_processBlockExecution executionOk
    · cases executionOk
      exact LoadKept.refl _
  have randao : LoadKept executed revealed := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq randaoOk
    exact LoadKept.of_validators
  have eth1 : LoadKept revealed input := by
    split at eth1Ok
    · obtain ⟨_, _, rest⟩ := processEth1Data_eq eth1Ok
      rw [← rest]
      exact LoadKept.of_validators
    · cases eth1Ok
      exact LoadKept.refl _
  have rest := (header.trans (execution.trans (randao.trans eth1))).registryLoad_eq
  omega

/-- A block raises the validators plus the pending deposits by at most its bound, at every fork.
-/
theorem processBlock_registryLoad_le {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    registryLoad after ≤ registryLoad state + blockLoadBound block.body := by
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput computed
  have one := operationsInput_registryLoad_le started
  have two := processOperations_registryLoad_le operated
  have three : LoadKept last after := by
    split at synced
    · exact loadKeptLaws.processSyncAggregate synced
    · cases synced
      exact LoadKept.refl _
  have four := three.registryLoad_eq
  unfold blockLoadBound
  by_cases gloas : .glamsterdam ≤ fork
  · have none : blockDepositCount block.body = 0 := by
      unfold blockDepositCount
      rw [dite_eq_right_iff]
      exact fun below => absurd below (Nat.not_lt.mpr gloas)
    simp only [gloas, ↓reduceIte] at one two
    rw [none, Nat.mul_zero]
    omega
  · simp only [gloas, ↓reduceIte] at one two
    omega

/-- A signed block raises the count by at most the same bound as its block. -/
theorem applySignedBlock_registryLoad_le {signed : SignedBeaconBlock preset fork}
    {validateResult : Bool}
    (computed : applySignedBlock config checks engine state signed validateResult = .ok after) :
    registryLoad after ≤ registryLoad state + blockLoadBound signed.message.body := by
  exact processBlock_registryLoad_le (applySignedBlock_ok computed).2.1

end EthLib.Consensus
