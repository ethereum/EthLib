module

public import EthLib.Consensus.Proofs.Transition.RegistryIdentity
public import EthLib.Consensus.Proofs.Transition.Committees
public import EthLib.Consensus.Proofs.Transition.Genesis
public import EthLib.Consensus.Proofs.Transition.Trace
public import EthLib.Consensus.Proofs.SyncCommittee

/-!
# Registry provenance of sync committees

A successful draw reads each public key from the validator registry.

The block and epoch proofs traverse the concrete operations to retain the two committee fields.

Registry identity transports membership across those operations, including new validator admissions.

Altair initializes both committees, and epoch rotation samples the next one again.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- Every key in a successful committee draw belongs to the registry used for the draw. -/
private theorem getNextSyncCommittee_keys {committee : SyncCommittee preset}
    (ok : getNextSyncCommittee state = .ok committee) :
    ∀ key ∈ committee.pubkeys.toList, key ∈ validatorKeys state := by
  obtain ⟨indices, _, reads, _⟩ := getNextSyncCommittee_eq_ok_iff.mp ok
  intro key member
  obtain ⟨i, inside, equal⟩ := List.getElem_of_mem member
  obtain ⟨validator, found, keyEq⟩ := reads ⟨i, by simpa using inside⟩
  have inRegistry := mem_of_getValidator found
  apply List.mem_map.mpr
  refine ⟨validator, by simpa using inRegistry, ?_⟩
  exact keyEq.symm.trans (by simpa using equal)

/-- Both committees contain only keys in the state's registry. -/
private def SyncCommitteeKeys (state : BeaconState preset fork) : Prop :=
  ∀ altair : .altair ≤ fork,
    (∀ key ∈ (state.currentSyncCommittee altair).value.pubkeys.toList,
      key ∈ validatorKeys state) ∧
    (∀ key ∈ (state.nextSyncCommittee altair).value.pubkeys.toList,
      key ∈ validatorKeys state)

private def SameSyncCommittees (state after : BeaconState preset fork) : Prop :=
  after.currentSyncCommittee = state.currentSyncCommittee ∧
    after.nextSyncCommittee = state.nextSyncCommittee

private theorem SameSyncCommittees.refl (state : BeaconState preset fork) :
    SameSyncCommittees state state := ⟨rfl, rfl⟩

private theorem SameSyncCommittees.trans {a b c : BeaconState preset fork}
    (ab : SameSyncCommittees a b) (bc : SameSyncCommittees b c) : SameSyncCommittees a c :=
  ⟨bc.1.trans ab.1, bc.2.trans ab.2⟩

private theorem SameSyncCommittees.foldlM {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (keeps : ∀ s x t, step s x = .ok t → SameSyncCommittees s t) {items : List α}
    (ok : items.foldlM step state = .ok after) : SameSyncCommittees state after :=
  foldlM_ok_invariant (SameSyncCommittees state)
    (fun _ _ _ before computed => before.trans (keeps _ _ _ computed))
    (.refl state) ok

namespace SameSyncCommittees

private theorem setValidatorAt {position : Nat} {validator : Validator}
    (ok : state.setValidatorAt position validator = .ok after) :
    SameSyncCommittees state after := by
  obtain ⟨_, rfl⟩ := setValidatorAt_ok ok
  exact ⟨rfl, rfl⟩

private theorem setValidator {index : ValidatorIndex} {validator : Validator}
    (ok : state.setValidator index validator = .ok after) : SameSyncCommittees state after :=
  setValidatorAt (by rwa [← setValidator_eq_setValidatorAt])

private theorem setBalance {index : ValidatorIndex} {balance : Gwei}
    (ok : state.setBalance index balance = .ok after) : SameSyncCommittees state after := by
  obtain ⟨_, rfl⟩ := setBalance_ok ok
  exact ⟨rfl, rfl⟩

private theorem increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (ok : Consensus.increaseBalance state index delta = .ok after) :
    SameSyncCommittees state after := by
  obtain ⟨_, set⟩ := increaseBalance_ok ok
  exact setBalance set

private theorem decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (ok : Consensus.decreaseBalance state index delta = .ok after) :
    SameSyncCommittees state after := by
  obtain ⟨_, set⟩ := decreaseBalance_ok ok
  exact setBalance set

private theorem initiateValidatorExit {index : ValidatorIndex}
    (ok : Consensus.initiateValidatorExit config state index = .ok after) :
    SameSyncCommittees state after := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok ok
  · exact .refl _
  · obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
    have kept := setValidator set
    exact kept

private theorem addValidatorToRegistry {key : BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (ok : Consensus.addValidatorToRegistry state key credentials amount = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.addValidatorToRegistry at ok
  split at ok
  · simp only [addValidatorToRegistryAltair, bind_ok_iff, liftAccessor_ok,
      pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := ok
    exact ⟨rfl, rfl⟩
  · split at ok <;> cases ok
    exact ⟨rfl, rfl⟩

private theorem applyPendingDeposit {deposit : PendingDeposit}
    (ok : Consensus.applyPendingDeposit config checks state deposit = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.applyPendingDeposit at ok
  split at ok
  · split at ok
    · cases ok; exact .refl _
    simp only [bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · exact addValidatorToRegistry ok
    · cases ok; exact .refl _
  · simp only [liftAccessor_ok, bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact increaseBalance ok

private theorem applyDeposit {key : BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    {signature : BLSSignature}
    (ok : Consensus.applyDeposit config checks state key credentials amount signature =
      .ok after) : SameSyncCommittees state after := by
  unfold Consensus.applyDeposit at ok
  split at ok
  · unfold applyDepositElectra at ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, added, queued⟩ := ok
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq queued
        exact (addValidatorToRegistry added).trans ⟨rfl, rfl⟩
      · cases ok; exact .refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp ok)
      exact ⟨rfl, rfl⟩
  · exact applyPendingDeposit ok

private theorem processDeposit {before : fork < .hegota} {deposit : Deposit}
    (ok : Consensus.processDeposit config checks before state deposit = .ok after) :
    SameSyncCommittees state after := by
  obtain ⟨_, _, _, _, credited⟩ := processDeposit_ok ok
  have kept := applyDeposit credited
  exact kept

private theorem slashValidator {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : Consensus.slashValidator config state index whistleblower = .ok after) :
    SameSyncCommittees state after := by
  obtain ⟨_, _, _, marked, _, _, slashings, _, _, _, _, last, exited, _, _, set,
    _, _, _, lowered, _, _, raised, paid, rfl⟩ := slashValidator_ok ok
  have first := (initiateValidatorExit exited).trans (setValidator set)
  have second : SameSyncCommittees marked last := by
    have kept := (decreaseBalance lowered).trans ((increaseBalance raised).trans
      (increaseBalance paid))
    exact kept
  have kept := first.trans second
  split <;> exact kept

private theorem processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (ok : Consensus.processDepositRequest state electra request = .ok after) :
    SameSyncCommittees state after := by
  obtain ⟨_, recorded⟩ := recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [Consensus.processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit,
    bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  exact ⟨rfl, rfl⟩

private theorem requestPartialWithdrawal {electra : .pectra ≤ fork} {index : ValidatorIndex}
    {validator : Validator} {amount owed : Gwei}
    (ok : Consensus.requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) : SameSyncCommittees state after := by
  simp only [Consensus.requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure]
    at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
    simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churned
    obtain ⟨_, _, _, _, _, _, churned⟩ := churned
    cases churned
    exact ⟨rfl, rfl⟩
  · cases ok; exact .refl _

private theorem processWithdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : Consensus.processWithdrawalRequest config state electra request = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.processWithdrawalRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact .refl _)
    | exact initiateValidatorExit (liftAccessor_ok.mp ok)
    | exact requestPartialWithdrawal ok

private theorem queueExcessActiveBalance {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.queueExcessActiveBalance state electra index = .ok after) :
    SameSyncCommittees state after := by
  simp only [Consensus.queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
    have kept := setBalance set
    exact kept
  · cases ok; exact .refl _

private theorem switchToCompoundingValidator {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.switchToCompoundingValidator state electra index = .ok after) :
    SameSyncCommittees state after := by
  simp only [Consensus.switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, _, _, set, queued⟩ := ok
  exact (setValidator set).trans (queueExcessActiveBalance queued)

private theorem queueConsolidation {electra : .pectra ≤ fork}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (ok : Consensus.queueConsolidation config state electra sourceIndex source targetIndex =
      .ok after) : SameSyncCommittees state after := by
  simp only [Consensus.queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, pure, Except.pure] at ok
  obtain ⟨⟨_, _⟩, churned, _, _, _, set, _, _, ok⟩ := ok
  cases ok
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at churned
  obtain ⟨_, _, _, _, _, _, churned⟩ := churned
  cases churned
  have kept := setValidator set
  exact kept

private theorem processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (ok : Consensus.processConsolidationRequest config state electra request = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact .refl _)
    | exact switchToCompoundingValidator (liftAccessor_ok.mp ok)
    | exact queueConsolidation ok

private theorem processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (ok : Consensus.processExecutionRequests config state body electra = .ok after) :
    SameSyncCommittees state after := by
  simp only [Consensus.processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := ok
  exact (foldlM (fun _ _ _ ok => processDepositRequest ok) deposits).trans
    ((foldlM (fun _ _ _ ok => processWithdrawalRequest ok) withdrawals).trans
      (foldlM (fun _ _ _ ok => processConsolidationRequest ok) consolidations))

private theorem processBuilderDepositRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderDepositRequest}
    (ok : Consensus.processBuilderDepositRequest config checks state gloas request = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.processBuilderDepositRequest addBuilderToRegistry at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first | (cases ok; done) | (cases ok; exact ⟨rfl, rfl⟩)

private theorem processBuilderExitRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (ok : Consensus.processBuilderExitRequest config state gloas request = .ok after) :
    SameSyncCommittees state after := by
  rcases processBuilderExitRequest_cases ok with rfl | ⟨_, _, _, _, _, exited⟩
  · exact .refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact ⟨rfl, rfl⟩

private theorem processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (ok : Consensus.processParentExecutionPayload config checks state gloas body = .ok after) :
    SameSyncCommittees state after := by
  rcases processParentExecutionPayload_ok ok with ⟨-, -, rfl⟩ |
    ⟨-, settled, _, _, _, _, _, _, settledOk, depositsOk, withdrawalsOk, consolidationsOk,
      buildersOk, exitsOk, -, rfl⟩
  · exact .refl _
  · have first : SameSyncCommittees state settled := by
      rw [settleParentPayment_eq settledOk]
      exact ⟨rfl, rfl⟩
    have kept := first.trans <|
      (foldlM (fun _ _ _ ok => processDepositRequest ok) depositsOk).trans <|
      (foldlM (fun _ _ _ ok => processWithdrawalRequest ok) withdrawalsOk).trans <|
      (foldlM (fun _ _ _ ok => processConsolidationRequest ok) consolidationsOk).trans <|
      (foldlM (fun _ _ _ ok => processBuilderDepositRequest ok) buildersOk).trans <|
      foldlM (fun _ _ _ ok => processBuilderExitRequest ok) exitsOk
    exact kept

private theorem applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (ok : Consensus.applyExpectedWithdrawals state capella expected = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.applyExpectedWithdrawals at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := ok
  have one : SameSyncCommittees state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact foldlM (fun _ _ _ ok => by rw [applyWithdrawal_eq ok]; exact ⟨rfl, rfl⟩) appliedOk
  have two : SameSyncCommittees applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · obtain ⟨_, _, built⟩ := bind_ok_iff.mp indexedOk
      cases built
      exact ⟨rfl, rfl⟩
    · cases indexedOk; exact .refl _
  have three : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → SameSyncCommittees kept finished := by
    intro kept ok
    split at ok
    · unfold updateNextWithdrawalBuilderIndex at ok
      dsimp only at ok
      split at ok
      · cases ok; exact .refl _
      · obtain ⟨_, _, built⟩ := bind_ok_iff.mp ok
        cases built
        exact ⟨rfl, rfl⟩
    · cases ok; exact .refl _
  have queued : SameSyncCommittees indexed (if electra : .pectra ≤ fork then
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
    split <;> split <;> exact ⟨rfl, rfl⟩
  have four : SameSyncCommittees finished after := by
    unfold updateNextWithdrawalValidatorIndex at last
    obtain ⟨_, _, last⟩ := bind_ok_iff.mp last
    dsimp only at last
    split at last
    · cases last
    · cases last; exact ⟨rfl, rfl⟩
  exact one.trans (two.trans (queued.trans ((three _ sweptOk).trans four)))

private theorem processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (ok : Consensus.processWithdrawals state capella payload = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.processWithdrawals at ok
  split at ok
  · split at ok
    · obtain ⟨_, _, applied⟩ := bind_ok_iff.mp ok
      exact applyExpectedWithdrawals (liftAccessor_ok.mp applied)
    · cases ok; exact .refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, applied⟩ := ok
    exact applyExpectedWithdrawals applied

private theorem processProposerSlashing {slashing : ProposerSlashing}
    (ok : Consensus.processProposerSlashing config checks state slashing = .ok after) :
    SameSyncCommittees state after := by
  simp only [Consensus.processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact slashValidator slashed

private theorem slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (ok : Consensus.slashIfSlashable config step index = .ok next) :
    SameSyncCommittees step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [Consensus.slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact slashValidator slashed
  · cases ok; exact .refl _

private theorem processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (ok : Consensus.processAttesterSlashing config checks state slashing = .ok after) :
    SameSyncCommittees state after := by
  simp only [Consensus.processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  exact foldlM_ok_invariant (fun step => SameSyncCommittees state step.1)
    (fun _ _ _ before ok => before.trans (slashIfSlashable ok))
    (show SameSyncCommittees state (state, false).1 from .refl state) folded

private theorem processAttestation {attestation : Attestation preset fork} {parentSlot : Slot}
    (ok : Consensus.processAttestation config checks state parentSlot attestation = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.processAttestation at ok
  split at ok
  · unfold processAttestationAltair at ok
    simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := ok
    have last : SameSyncCommittees raised after := by
      split at final
      · rw [recordPaymentWeight_eq final]; exact ⟨rfl, rfl⟩
      · cases final; exact .refl _
    have flags : ∀ (current : Bool) (participation : EpochParticipation preset fork),
        SameSyncCommittees state (setEpochParticipation state current participation) := by
      intro current participation
      unfold setEpochParticipation
      split <;> exact ⟨rfl, rfl⟩
    exact (flags _ _).trans ((increaseBalance raisedOk).trans last)
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := ok
  have kept := recordPendingAttestation_ok recorded
  split at kept <;>
  · obtain ⟨_, rest⟩ := kept
    rw [← rest]
    exact ⟨rfl, rfl⟩

private theorem processVoluntaryExit {signed : SignedVoluntaryExit}
    (ok : Consensus.processVoluntaryExit config checks state signed = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.processVoluntaryExit at ok
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ok
  exact initiateValidatorExit exited

private theorem processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (ok : Consensus.processBlsToExecutionChange config checks state signed = .ok after) :
    SameSyncCommittees state after := by
  obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  exact setValidator set

private theorem processOperations {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (ok : Consensus.processOperations config checks state body parentSlot = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.processOperations at ok
  split at ok
  · unfold processOperationsGloas at ok
    simp only [bind_ok_iff, ← Array.foldlM_toList] at ok
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposers, _, attesters, _,
      attestations, _, exits, _, changes, paid⟩ := ok
    exact (foldlM (fun _ _ _ ok => processProposerSlashing ok) proposers).trans <|
      (foldlM (fun _ _ _ ok => processAttesterSlashing ok) attesters).trans <|
      (foldlM (fun _ _ _ ok => processAttestation ok) attestations).trans <|
      (foldlM (fun _ _ _ ok => processVoluntaryExit ok) exits).trans <|
      (foldlM (fun _ _ _ ok => processBlsToExecutionChange ok) changes).trans <|
      foldlM (fun _ _ _ ok => by rw [processPayloadAttestation_eq ok]; exact .refl _) paid
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, _, _, _, _, proposers, _, attesters, _, attestations, _, deposits, exited,
    exits, changed, changesOk, requestsOk⟩ := ok
  have changes : SameSyncCommittees exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact foldlM (fun _ _ _ ok => processBlsToExecutionChange ok) changesOk
    · cases changesOk; exact .refl _
  have requests : SameSyncCommittees changed after := by
    split at requestsOk
    · exact processExecutionRequests requestsOk
    · cases requestsOk; exact .refl _
  exact (foldlM (fun _ _ _ ok => processProposerSlashing ok) proposers).trans <|
    (foldlM (fun _ _ _ ok => processAttesterSlashing ok) attesters).trans <|
    (foldlM (fun _ _ _ ok => processAttestation ok) attestations).trans <|
    (foldlM (fun _ _ _ ok => processDeposit ok) deposits).trans <|
    (foldlM (fun _ _ _ ok => processVoluntaryExit ok) exits).trans <| changes.trans requests

private theorem processSyncAggregate {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    (ok : Consensus.processSyncAggregate config checks state altair aggregate = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.processSyncAggregate at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := ok
  rw [← Array.foldlM_toList] at folded
  refine foldlM (fun _ _ _ ok => ?_) folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    exact (increaseBalance raised).trans (increaseBalance paid)
  · exact decreaseBalance (liftAccessor_ok.mp ok)

private theorem processExecutionPayload {body : BeaconBlockBody preset fork}
    {engine : ExecutionEngine preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (ok : Consensus.processExecutionPayload config engine state body bellatrix = .ok after) :
    SameSyncCommittees state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
  exact ⟨rfl, rfl⟩

private theorem processExecutionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (ok : Consensus.processExecutionPayloadBid config checks state gloas signed = .ok after) :
    SameSyncCommittees state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok ok
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact ⟨rfl, rfl⟩
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at recordedOk
    subst recordedOk
    exact ⟨rfl, rfl⟩

private theorem processBlockExecution {body : BeaconBlockBody preset fork}
    {engine : ExecutionEngine preset fork} {bellatrix : .bellatrix ≤ fork}
    (ok : Consensus.processBlockExecution config checks engine state body bellatrix = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.processBlockExecution at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawn, bid⟩ := ok
    exact (processWithdrawals withdrawn).trans (processExecutionPayloadBid bid)
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, withdrawn, paid⟩ := ok
    exact (processWithdrawals withdrawn).trans (processExecutionPayload paid)
  · dsimp only at ok
    split at ok
    · exact processExecutionPayload ok
    · cases ok; exact .refl _

private theorem processBlockHeader {block : BeaconBlock preset fork}
    (ok : Consensus.processBlockHeader state block = .ok after) :
    SameSyncCommittees state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq ok
  exact ⟨rfl, rfl⟩

private theorem processRandao {body : BeaconBlockBody preset fork}
    (ok : Consensus.processRandao config checks state body = .ok after) :
    SameSyncCommittees state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq ok
  exact ⟨rfl, rfl⟩

private theorem processEth1Data {before : fork < .hegota} {body : BeaconBlockBody preset fork}
    (ok : Consensus.processEth1Data before state body = .ok after) :
    SameSyncCommittees state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq ok
  rw [← rest]
  exact ⟨rfl, rfl⟩

private theorem processBlock {block : BeaconBlock preset fork}
    {engine : ExecutionEngine preset fork}
    (ok : Consensus.processBlock config checks engine state block = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.processBlock at ok
  split at ok
  · unfold processBlockAltair at ok
    simp only [bind_ok_iff] at ok
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, _, operatedOk, synced⟩ := ok
    have paidStep : SameSyncCommittees state paid := by
      split at paidOk
      · exact processParentExecutionPayload paidOk
      · cases paidOk; exact .refl _
    have execution : SameSyncCommittees headed executed := by
      split at executedOk
      · exact processBlockExecution executedOk
      · cases executedOk; exact .refl _
    have vote : SameSyncCommittees revealed voted := by
      split at votedOk
      · exact processEth1Data votedOk
      · cases votedOk; exact .refl _
    exact paidStep.trans <| (processBlockHeader headedOk).trans <| execution.trans <|
      (processRandao revealedOk).trans <| vote.trans <|
      (processOperations operatedOk).trans (processSyncAggregate synced)
  simp only [bind_ok_iff] at ok
  obtain ⟨_, header, _, randao, _, eth1, operations⟩ := ok
  exact (processBlockHeader header).trans <| (processRandao randao).trans <|
    (processEth1Data eth1).trans (processOperations operations)

private theorem applyDeltas {rewards penalties : Array Gwei} {index : Nat}
    (ok : Consensus.applyDeltas rewards penalties state index = .ok after) :
    SameSyncCommittees state after := by
  simp only [Consensus.applyDeltas, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, raised, lowered⟩ := ok
  exact (increaseBalance raised).trans (decreaseBalance lowered)

private theorem applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (ok : Consensus.applyAllDeltas state deltas = .ok after) : SameSyncCommittees state after :=
  foldlM (fun _ _ _ ok => applyDeltas ok) ok

private theorem processRewardsAndPenalties
    (ok : Consensus.processRewardsAndPenalties config state = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.processRewardsAndPenalties at ok
  split at ok
  · cases ok; exact .refl _
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, _, _, applied⟩ := ok
    exact foldlM (fun _ _ _ ok => applyAllDeltas ok) applied
  · obtain ⟨_, _, applied⟩ := bind_ok_iff.mp ok
    exact applyAllDeltas applied

private theorem updateRegistryEntry {index : Nat}
    (ok : Consensus.updateRegistryEntry config state index = .ok after) :
    SameSyncCommittees state after := by
  simp only [Consensus.updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, marked, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact (setValidatorAt marked).trans (initiateValidatorExit exited)
  · cases ok; exact setValidatorAt marked

private theorem activateValidator {index : ValidatorIndex}
    (ok : Consensus.activateValidator state index = .ok after) :
    SameSyncCommittees state after := by
  simp only [Consensus.activateValidator, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, set⟩ := ok
  exact setValidator set

private theorem updateRegistryEntryElectra {activationEpoch : Epoch} {index : Nat}
    (ok : Consensus.updateRegistryEntryElectra config activationEpoch state index = .ok after) :
    SameSyncCommittees state after := by
  simp only [Consensus.updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, set⟩ := ok
    exact setValidatorAt set
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact initiateValidatorExit exited
  split at ok
  · exact setValidatorAt (liftAccessor_ok.mp ok)
  · cases ok; exact .refl _

private theorem processRegistryUpdates
    (ok : Consensus.processRegistryUpdates config state = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.processRegistryUpdates at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact foldlM (fun _ _ _ ok => updateRegistryEntryElectra ok) ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, updated, activated⟩ := ok
  exact (foldlM (fun _ _ _ ok => updateRegistryEntry ok) updated).trans
    (foldlM (fun _ _ _ ok => activateValidator ok) activated)

private theorem applySlashingPenalty {total adjusted : Gwei} {index : Nat}
    (ok : Consensus.applySlashingPenalty state total adjusted index = .ok after) :
    SameSyncCommittees state after := by
  simp only [Consensus.applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · obtain ⟨_, _, ok⟩ := bind_ok_iff.mp ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, _, _, _, _, lowered⟩ := ok
      exact decreaseBalance lowered
    · cases ok; exact .refl _
  · cases ok; exact .refl _

private theorem applySlashingPenaltyElectra {perIncrement : Gwei} {index : Nat}
    (ok : Consensus.applySlashingPenaltyElectra state perIncrement index = .ok after) :
    SameSyncCommittees state after := by
  simp only [Consensus.applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · obtain ⟨_, _, ok⟩ := bind_ok_iff.mp ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, _, _, lowered⟩ := ok
      exact decreaseBalance lowered
    · cases ok; exact .refl _
  · cases ok; exact .refl _

private theorem processSlashings (ok : Consensus.processSlashings state = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.processSlashings at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, ok⟩ := ok
  split at ok
  · obtain ⟨_, _, applied⟩ := bind_ok_iff.mp ok
    exact foldlM (fun _ _ _ ok => applySlashingPenaltyElectra ok) applied
  · exact foldlM (fun _ _ _ ok => applySlashingPenalty ok) ok

private theorem processEffectiveBalanceUpdates
    (ok : Consensus.processEffectiveBalanceUpdates state = .ok after) :
    SameSyncCommittees state after := by
  apply foldlM (fun _ _ _ ok => ?_) ok
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, set⟩ := ok
  exact setValidatorAt set

private theorem passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      Consensus.passPendingDeposits config checks stop nextEpoch available state processed count
        postponed deposits = .ok pass → SameSyncCommittees state pass.1.state
  | [], _, _, _, _, _, ok => by
    cases ok; exact .refl _
  | deposit :: rest, state, processed, count, postponed, pass, ok => by
    unfold Consensus.passPendingDeposits at ok
    simp only [bind, Except.bind, pure, Except.pure] at ok
    split at ok
    · cases ok; exact .refl _
    split at ok
    · cases ok
    split at ok
    · split at ok
      · cases ok
      rename_i credited
      split at ok
      · cases ok
      cases ok
      exact (applyPendingDeposit credited).trans (passPendingDeposits (deposits := rest) ‹_›)
    split at ok
    · split at ok
      · cases ok
      cases ok
      exact passPendingDeposits (deposits := rest) ‹_›
    split at ok
    · cases ok
    split at ok
    · cases ok; exact .refl _
    split at ok
    · cases ok
    rename_i credited
    split at ok
    · cases ok
    cases ok
    exact (applyPendingDeposit credited).trans (passPendingDeposits (deposits := rest) ‹_›)

private theorem passPendingConsolidations {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      Consensus.passPendingConsolidations nextEpoch state consolidations = .ok result →
      SameSyncCommittees state result.1
  | [], _, _, ok => by
    cases ok; exact .refl _
  | consolidation :: rest, state, result, ok => by
    simp only [Consensus.passPendingConsolidations, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨source, _, ok⟩ := ok
    split at ok
    · obtain ⟨⟨passed, read⟩, passedOk, ok⟩ := bind_ok_iff.mp ok
      cases ok
      exact passPendingConsolidations (result := (passed, read)) passedOk
    split at ok
    · cases ok; exact .refl _
    simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, lowered, loweredOk, raised, raisedOk, ⟨passed, read⟩, passedOk, ok⟩ := ok
    cases ok
    exact ((decreaseBalance loweredOk).trans (increaseBalance raisedOk)).trans
      (passPendingConsolidations (result := (passed, read)) passedOk)

private theorem processPendingDeposits {electra : .pectra ≤ fork}
    (ok : Consensus.processPendingDeposits config checks state electra = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.processPendingDeposits at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals exact passPendingDeposits ‹_›

private theorem processPendingConsolidations {electra : .pectra ≤ fork}
    (ok : Consensus.processPendingConsolidations state electra = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.processPendingConsolidations at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals exact passPendingConsolidations ‹_›

private theorem processInactivityUpdates {altair : .altair ≤ fork}
    (ok : Consensus.processInactivityUpdates config state altair = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.processInactivityUpdates at ok
  split at ok
  · cases ok; exact .refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, rfl⟩ := ok
    exact ⟨rfl, rfl⟩

private theorem processEth1DataReset {before : fork < .hegota}
    (ok : Consensus.processEth1DataReset before state = .ok after) :
    SameSyncCommittees state after := by
  simp only [Consensus.processEth1DataReset, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok <;> cases ok <;> exact ⟨rfl, rfl⟩

private theorem processSlashingsReset (ok : Consensus.processSlashingsReset state = .ok after) :
    SameSyncCommittees state after := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq ok
  exact ⟨rfl, rfl⟩

private theorem processRandaoMixesReset (ok : Consensus.processRandaoMixesReset state = .ok after) :
    SameSyncCommittees state after := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq ok
  exact ⟨rfl, rfl⟩

private theorem processHistoricalRootsUpdate
    (ok : Consensus.processHistoricalRootsUpdate state = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.processHistoricalRootsUpdate at ok
  split at ok
  · cases ok
  simp only [bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, rfl⟩ := ok
    exact ⟨rfl, rfl⟩
  · cases ok; exact .refl _

private theorem processHistoricalSummariesUpdate {capella : .shapella ≤ fork}
    (ok : Consensus.processHistoricalSummariesUpdate state capella = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.processHistoricalSummariesUpdate at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals exact ⟨rfl, rfl⟩

private theorem processJustificationAndFinalization
    (ok : Consensus.processJustificationAndFinalization state = .ok after) :
    SameSyncCommittees state after := by
  rcases processJustificationAndFinalization_ok ok with rfl | ⟨_, _, _, weighed⟩
  · exact .refl _
  · simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok,
      pure, Except.pure, Except.ok.injEq] at weighed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := weighed
    exact ⟨rfl, rfl⟩

private theorem queuePreActivation {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.queuePreActivation state electra index = .ok after) :
    SameSyncCommittees state after := by
  simp only [Consensus.queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, set₁, _, set₂, rfl⟩ := ok
  have kept := (setBalance set₁).trans (setValidator set₂)
  exact kept

private theorem queueCompoundingExcess {electra : .pectra ≤ fork} {index : Nat}
    (ok : Consensus.queueCompoundingExcess state electra index = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.queueCompoundingExcess at ok
  split at ok
  · split at ok
    · exact queueExcessActiveBalance (liftAccessor_ok.mp ok)
    · cases ok; exact .refl _
  · cases ok; exact .refl _

end SameSyncCommittees

private theorem SyncCommitteeKeys.transfer (holds : SyncCommitteeKeys state)
    (same : SameSyncCommittees state after) (keys : RegistryIdentity state after) :
    SyncCommitteeKeys after := by
  intro altair
  obtain ⟨current, next⟩ := holds altair
  constructor
  · intro key member
    rw [same.1] at member
    exact keys.kept.subset (current key member)
  · intro key member
    rw [same.2] at member
    exact keys.kept.subset (next key member)

namespace SyncCommitteeKeys

/-- Genesis initialization returns only a pre-Altair state, which has no sync committees. -/
private theorem genesis {g : ForkedBeaconState preset}
    (genesis : Genesis (config := config) (checks := checks) g) : SyncCommitteeKeys g.state := by
  obtain ⟨_, _, _, ok⟩ := genesis
  obtain ⟨before, _⟩ := initializeBeaconStateFromEth1_ok ok
  intro altair
  exact (Nat.not_le_of_lt before altair).elim

/-- Altair initializes both committees by a successful draw from the resulting registry. -/
private theorem upgradeToAltair {pre : BeaconState preset .phase0}
    {post : BeaconState preset .altair}
    (ok : Consensus.upgradeToAltair config pre = .ok post) : SyncCommitteeKeys post := by
  simp only [Consensus.upgradeToAltair, bind_ok_iff, liftAccessor_ok,
    pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨translated, _, committee, drawn, rfl⟩ := ok
  intro _
  exact ⟨getNextSyncCommittee_keys drawn, getNextSyncCommittee_keys drawn⟩

/-- Rotation retains the previous next committee and draws the new next one from the registry. -/
private theorem processSyncCommitteeUpdates {altair : .altair ≤ fork}
    (holds : SyncCommitteeKeys state)
    (ok : Consensus.processSyncCommitteeUpdates state altair = .ok after) :
    SyncCommitteeKeys after := by
  simp only [Consensus.processSyncCommitteeUpdates, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨next, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨committee, drawn, rfl⟩ := ok
    intro _
    exact ⟨(holds altair).2, getNextSyncCommittee_keys drawn⟩
  · cases ok
    exact holds

/-- An epoch keeps committee provenance through registry changes, rotation and the new draw.

Every stage but the committee update keeps both committees and the key prefix of the registry. -/
private theorem processEpoch (holds : SyncCommitteeKeys state)
    (ok : Consensus.processEpoch config checks state = .ok after) : SyncCommitteeKeys after := by
  -- Before Altair there are no sync committees, so the provenance holds trivially.
  by_cases altair : Fork.altair ≤ fork
  case neg => exact fun altair' => absurd altair' altair
  refine (processEpoch_trace ok).transport (fun s t => SyncCommitteeKeys s → SyncCommitteeKeys t)
    (fun _ => id) (fun one two => two ∘ one) ?_ holds
  intro k _ a b computed held
  have edge := EpochStage.action_cases.mp computed
  cases k <;> simp only [EpochStage.Edge, altair, ↓reduceDIte] at edge
  case justification =>
    exact held.transfer (SameSyncCommittees.processJustificationAndFinalization edge)
      (.of_validators (by rw [(processJustificationAndFinalization_keeps edge).2.2.2.2.2.1]))
  case inactivity =>
    exact held.transfer (SameSyncCommittees.processInactivityUpdates edge)
      (frame_processInactivityUpdates edge).toFrame.registryIdentity
  case rewards =>
    exact held.transfer (SameSyncCommittees.processRewardsAndPenalties edge)
      (frame_processRewardsAndPenalties edge).toFrame.registryIdentity
  case registry =>
    exact held.transfer (SameSyncCommittees.processRegistryUpdates edge)
      (frame_processRegistryUpdates edge).toFrame.registryIdentity
  case slashings =>
    exact held.transfer (SameSyncCommittees.processSlashings edge)
      (frame_processSlashings edge).toFrame.registryIdentity
  case eth1Reset =>
    split at edge
    · exact held.transfer (SameSyncCommittees.processEth1DataReset edge)
        (frame_processEth1DataReset edge).toFrame.registryIdentity
    · exact edge ▸ held
  case pendingDeposits =>
    split at edge
    · exact held.transfer (SameSyncCommittees.processPendingDeposits edge)
        (frame_processPendingDeposits edge).toFrame.registryIdentity
    · exact edge ▸ held
  case pendingConsolidations =>
    split at edge
    · exact held.transfer (SameSyncCommittees.processPendingConsolidations edge)
        (frame_processPendingConsolidations edge).toFrame.registryIdentity
    · exact edge ▸ held
  case payments =>
    split at edge
    · rw [processBuilderPendingPayments_eq edge]
      exact held.transfer ⟨rfl, rfl⟩ .of_validators
    · exact edge ▸ held
  case effectiveBalances =>
    exact held.transfer (SameSyncCommittees.processEffectiveBalanceUpdates edge)
      (frame_processEffectiveBalanceUpdates edge).toFrame.registryIdentity
  case slashingsReset =>
    exact held.transfer (SameSyncCommittees.processSlashingsReset edge)
      (frame_processSlashingsReset edge).toFrame.registryIdentity
  case randaoReset =>
    exact held.transfer (SameSyncCommittees.processRandaoMixesReset edge)
      (frame_processRandaoMixesReset edge).toFrame.registryIdentity
  case history =>
    split at edge
    · exact held.transfer (SameSyncCommittees.processHistoricalSummariesUpdate edge)
        (frame_processHistoricalSummariesUpdate edge).toFrame.registryIdentity
    · exact held.transfer (SameSyncCommittees.processHistoricalRootsUpdate edge)
        (frame_processHistoricalRootsUpdate edge).toFrame.registryIdentity
  case participation =>
    subst edge
    exact held.transfer ⟨rfl, rfl⟩ .of_validators
  case syncCommittees => exact processSyncCommitteeUpdates held edge
  case proposerLookahead =>
    split at edge
    · simp only [processProposerLookahead, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at edge
      obtain ⟨_, _, _, _, rfl⟩ := edge
      exact held.transfer ⟨rfl, rfl⟩ .of_validators
    · exact edge ▸ held
  case ptcWindow =>
    split at edge
    · simp only [processPtcWindow, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at edge
      obtain ⟨_, _, _, _, rfl⟩ := edge
      exact held.transfer ⟨rfl, rfl⟩ .of_validators
    · exact edge ▸ held

/-- A slot updates committees only through the epoch transition. -/
private theorem advanceSlot (holds : SyncCommitteeKeys state)
    (ok : Consensus.advanceSlot config checks state = .ok after) : SyncCommitteeKeys after := by
  obtain ⟨next, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have cachedKeys : SyncCommitteeKeys cached := by rw [cachedEq]; exact holds
  have epochKeys : SyncCommitteeKeys epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact processEpoch cachedKeys epochedOk
    · cases epochedOk; exact cachedKeys
  exact epochKeys

/-- Blocks preserve the committees and retain all existing validator keys. -/
private theorem processBlock {block : BeaconBlock preset fork}
    {engine : ExecutionEngine preset fork} (holds : SyncCommitteeKeys state)
    (ok : Consensus.processBlock config checks engine state block = .ok after) :
    SyncCommitteeKeys after :=
  holds.transfer (SameSyncCommittees.processBlock ok) (frame_processBlock ok).registryIdentity

private theorem carryFields {post : Fork} (upgrade : fork < post)
    (before : post < .glamsterdam) (altair : .altair ≤ fork)
    (holds : SyncCommitteeKeys state) :
    SyncCommitteeKeys (Consensus.carryFields config post state upgrade before) := by
  intro _
  simpa [Consensus.carryFields, altair, validatorKeys, carryRooted]
    using holds altair

private theorem upgradeToElectra {pre : BeaconState preset .dencun}
    {post : BeaconState preset .pectra} (holds : SyncCommitteeKeys pre)
    (ok : Consensus.upgradeToElectra config pre = .ok post) : SyncCommitteeKeys post := by
  simp only [Consensus.upgradeToElectra, bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, queued, compounded⟩ := ok
  have same := (SameSyncCommittees.foldlM
    (fun _ _ _ ok => SameSyncCommittees.queuePreActivation ok) queued).trans
    (SameSyncCommittees.foldlM (fun _ _ _ ok => SameSyncCommittees.queueCompoundingExcess ok)
      compounded)
  have keys := ((BlockFrame.foldlM (fun _ _ _ ok => frame_queuePreActivation ok) queued).trans
    (BlockFrame.foldlM (fun _ _ _ ok => frame_queueCompoundingExcess ok)
      compounded)).toFrame.registryIdentity
  apply transfer ?_ same keys
  have carried := carryFields (config := config) (post := .pectra)
    (by decide) (by decide) (by decide) holds
  exact carried

/-- Each upgrade either samples the first committees or carries their keys into the new registry. -/
private theorem upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (holds : SyncCommitteeKeys pre.state)
    (ok : Consensus.upgradeNext config checks pre = .ok post) :
    SyncCommitteeKeys post.val.state := by
  obtain ⟨fork, state⟩ := pre
  cases fork
  case phase0 =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    exact upgradeToAltair upgraded
  case altair | bellatrix | shapella =>
    simp only [Consensus.upgradeNext, pure, Except.pure, Except.ok.injEq] at ok
    subst ok
    exact carryFields (by dsimp; decide) (by dsimp; decide) (by decide) holds
  case dencun =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    exact upgradeToElectra holds upgraded
  case pectra =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [Consensus.upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
    obtain ⟨_, _, rfl⟩ := upgraded
    have carried := carryFields (config := config) (post := .fusaka)
      (by dsimp; decide) (by decide) (by dsimp; decide) holds
    exact carried
  case fusaka =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [Consensus.upgradeToGloas, bind_ok_iff] at upgraded
    obtain ⟨_, _, _, _, onboarded⟩ := upgraded
    obtain ⟨⟨_, _, rfl⟩, _⟩ := onboardBuildersFromPendingDeposits_spec onboarded
    intro _
    exact holds (by dsimp; decide)
  case glamsterdam =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    intro _
    exact holds (by dsimp; decide)
  all_goals simp only [Consensus.upgradeNext] at ok; cases ok

end SyncCommitteeKeys

/-- Block operations retain the current sync committee, including when they admit validators. -/
theorem processOperations_currentSyncCommittee {body : BeaconBlockBody preset fork}
    {parentSlot : Slot} (altair : .altair ≤ fork)
    (ok : processOperations config checks state body parentSlot = .ok after) :
    after.currentSyncCommittee altair = state.currentSyncCommittee altair :=
  congrFun (SameSyncCommittees.processOperations ok).1 altair

/-- Block execution retains the current sync committee. -/
theorem processBlockExecution_currentSyncCommittee {body : BeaconBlockBody preset fork}
    {engine : ExecutionEngine preset fork} {bellatrix : .bellatrix ≤ fork}
    (altair : .altair ≤ fork)
    (ok : processBlockExecution config checks engine state body bellatrix = .ok after) :
    after.currentSyncCommittee altair = state.currentSyncCommittee altair :=
  congrFun (SameSyncCommittees.processBlockExecution ok).1 altair

/-- Every current and next sync committee key in a run from genesis belongs to its registry. -/
theorem Run.syncCommittee_keys {g x : ForkedBeaconState preset} (run : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g) (altair : .altair ≤ x.fork) :
    (∀ key ∈ (x.state.currentSyncCommittee altair).value.pubkeys.toList,
      key ∈ validatorKeys x.state) ∧
    (∀ key ∈ (x.state.nextSyncCommittee altair).value.pubkeys.toList,
      key ∈ validatorKeys x.state) := by
  have holds : SyncCommitteeKeys x.state := by
    clear altair
    induction run with
    | nil => exact SyncCommitteeKeys.genesis genesis
    | snoc _ step ih =>
      cases step with
      | slot ok =>
        obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
        exact processUpgrades_induction (property := fun post => SyncCommitteeKeys post.state)
          (forked := ⟨_, advanced⟩)
          (fun before ok => SyncCommitteeKeys.upgradeNext before ok)
          (SyncCommitteeKeys.advanceSlot ih slotOk) upgrades
      | block engine signed _ ok =>
        exact SyncCommitteeKeys.processBlock ih (applySignedBlock_ok ok).2.1
  exact holds altair

end EthLib.Consensus
