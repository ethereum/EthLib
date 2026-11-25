module

public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.Committees
public import EthLib.Consensus.Proofs.Transition.Genesis
public import EthLib.Consensus.Proofs.Transition.Trace
public import EthLib.Consensus.Proofs.SyncCommittee
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
import EthLib.Consensus.Proofs.Transition.RunKept

/-!
# Registry provenance of sync committees

A successful draw reads each public key from the validator registry.

The block and epoch proofs traverse the concrete operations to retain the two committee fields.

The registry keys only grow by appending, so membership survives those operations and admissions.

Altair initializes both committees, and epoch rotation samples the next one again.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- Every drawn key has a validator with an assigned activation epoch. -/
private theorem getNextSyncCommittee_keys {committee : SyncCommittee preset}
    (ok : getNextSyncCommittee state = .ok committee) :
    ∀ key ∈ committee.pubkeys.toList, ∃ (i : Nat) (v : Validator),
      state.validators.data[i]? = some v ∧ v.pubkey = key ∧
        v.activationEpoch ≠ FAR_FUTURE_EPOCH ∧
        v.activationEpoch.toNat ≤ (getCurrentEpoch state).toNat + 1 := by
  obtain ⟨indices, drawn, reads, _⟩ := getNextSyncCommittee_eq_ok_iff.mp ok
  intro key member
  obtain ⟨i, inside, equal⟩ := List.getElem_of_mem member
  obtain ⟨validator, found, keyEq⟩ := reads ⟨i, by simpa using inside⟩
  obtain ⟨_, candidatesOk, selected⟩ := getNextSyncCommitteeIndices_checked drawn
  have member := selected _
    (by simpa using indices.getElem_mem (i := i) (by simpa using inside))
  obtain ⟨v, read, isActive⟩ :=
    (mem_iff_of_getActiveValidatorIndicesChecked_ok candidatesOk).mp member
  have same : v = validator := Option.some.inj (read.symm.trans (getValidator_eq_ok_iff.mp found))
  subst v
  refine ⟨_, validator, getValidator_eq_ok_iff.mp found,
    keyEq.symm.trans (by simpa using equal), ?_⟩
  refine ⟨Consensus.Internal.assigned_of_active isActive, ?_⟩
  exact Nat.le_trans (UInt64.le_iff_toNat_le.mp (activationLe_of_active isActive)) (by
    rw [UInt64.toNat_add]
    exact Nat.mod_le _ _)

/-- Both committees contain only keys whose activation epoch has been assigned. -/
private def SyncCommitteeKeys (state : BeaconState preset fork) : Prop :=
  ∀ altair : .altair ≤ fork,
    (∀ key ∈ (state.currentSyncCommittee altair).value.pubkeys.toList,
      ∃ (i : Nat) (v : Validator), state.validators.data[i]? = some v ∧ v.pubkey = key ∧
        v.activationEpoch ≠ FAR_FUTURE_EPOCH ∧
        v.activationEpoch.toNat ≤ (getCurrentEpoch state).toNat + 1) ∧
    (∀ key ∈ (state.nextSyncCommittee altair).value.pubkeys.toList,
      ∃ (i : Nat) (v : Validator), state.validators.data[i]? = some v ∧ v.pubkey = key ∧
        v.activationEpoch ≠ FAR_FUTURE_EPOCH ∧
        v.activationEpoch.toNat ≤ (getCurrentEpoch state).toNat + 1)

private def SameSyncCommittees (state after : BeaconState preset fork) : Prop :=
  after.currentSyncCommittee = state.currentSyncCommittee ∧
    after.nextSyncCommittee = state.nextSyncCommittee ∧
    after.proposerLookahead = state.proposerLookahead

private theorem SameSyncCommittees.refl (state : BeaconState preset fork) :
    SameSyncCommittees state state := ⟨rfl, rfl, rfl⟩

private theorem SameSyncCommittees.trans {a b c : BeaconState preset fork}
    (ab : SameSyncCommittees a b) (bc : SameSyncCommittees b c) : SameSyncCommittees a c :=
  ⟨bc.1.trans ab.1, bc.2.1.trans ab.2.1, bc.2.2.trans ab.2.2⟩

/-- A step keeps the current and next sync committees. -/
private abbrev KeepsCommittees (state after : BeaconState preset fork) : Prop :=
  after.currentSyncCommittee = state.currentSyncCommittee ∧
    after.nextSyncCommittee = state.nextSyncCommittee

private theorem KeepsCommittees.trans {a b c : BeaconState preset fork}
    (ab : KeepsCommittees a b) (bc : KeepsCommittees b c) : KeepsCommittees a c :=
  ⟨bc.1.trans ab.1, bc.2.trans ab.2⟩

private theorem SameSyncCommittees.keeps {a b : BeaconState preset fork}
    (same : SameSyncCommittees a b) : KeepsCommittees a b := ⟨same.1, same.2.1⟩

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
  exact ⟨rfl, rfl, rfl⟩

private theorem setValidator {index : ValidatorIndex} {validator : Validator}
    (ok : state.setValidator index validator = .ok after) : SameSyncCommittees state after :=
  setValidatorAt (by rwa [← setValidator_eq_setValidatorAt])

private theorem setBalance {index : ValidatorIndex} {balance : Gwei}
    (ok : state.setBalance index balance = .ok after) : SameSyncCommittees state after := by
  obtain ⟨_, rfl⟩ := setBalance_ok ok
  exact ⟨rfl, rfl, rfl⟩

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
    exact ⟨rfl, rfl, rfl⟩
  · split at ok <;> cases ok
    exact ⟨rfl, rfl, rfl⟩

private theorem applyPendingDeposit {deposit : PendingDeposit}
    (ok : Consensus.applyPendingDeposit config checks state deposit = .ok after) :
    SameSyncCommittees state after := by
  rcases applyPendingDeposit_cases ok with rfl | ⟨_, ok⟩ | ⟨_, ok⟩
  · exact .refl _
  · exact increaseBalance ok
  · exact addValidatorToRegistry ok

private theorem applyDeposit {key : BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    {signature : BLSSignature}
    (ok : Consensus.applyDeposit config checks state key credentials amount signature =
      .ok after) : SameSyncCommittees state after := by
  rcases applyDeposit_cases ok with rfl | ⟨_, _, _, rfl | added, rfl⟩ | ⟨_, ok⟩
  · exact .refl _
  · exact ⟨rfl, rfl, rfl⟩
  · exact (addValidatorToRegistry added).trans ⟨rfl, rfl, rfl⟩
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
  obtain ⟨-, -, -, _, _, rfl⟩ := processDepositRequest_ok ok
  exact ⟨rfl, rfl, rfl⟩

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
    exact ⟨rfl, rfl, rfl⟩
  · cases ok; exact .refl _

private theorem processWithdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : Consensus.processWithdrawalRequest config state electra request = .ok after) :
    SameSyncCommittees state after := by
  rcases withdrawalRequest_cases ok with rfl | ⟨_, _, _, exited⟩ | ⟨_, _, _, _, withdrawn⟩
  · exact .refl _
  · exact initiateValidatorExit exited
  · exact requestPartialWithdrawal withdrawn

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
  obtain ⟨_, _, _, _, _, _, _, set, _, rfl⟩ := queueConsolidation_steps ok
  have kept := setValidator set
  exact kept

private theorem processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (ok : Consensus.processConsolidationRequest config state electra request = .ok after) :
    SameSyncCommittees state after := by
  rcases consolidationRequest_cases ok with rfl | ⟨_, _, _, switched⟩ | ⟨_, _, _, _, _, queued⟩
  · exact .refl _
  · exact switchToCompoundingValidator switched
  · exact queueConsolidation queued

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
  all_goals first | (cases ok; done) | (cases ok; exact ⟨rfl, rfl, rfl⟩)

private theorem processBuilderExitRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (ok : Consensus.processBuilderExitRequest config state gloas request = .ok after) :
    SameSyncCommittees state after := by
  rcases processBuilderExitRequest_cases ok with rfl | ⟨_, _, _, _, _, exited⟩
  · exact .refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact ⟨rfl, rfl, rfl⟩

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
      exact ⟨rfl, rfl, rfl⟩
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
  apply applyExpectedWithdrawals_of_setters SameSyncCommittees .refl
    (fun one two => one.trans two) (fun step => by
      rw [applyWithdrawal_eq step]
      exact ⟨rfl, rfl, rfl⟩) (computed := ok)
  all_goals exact fun _ _ => ⟨rfl, rfl, rfl⟩

private theorem processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (ok : Consensus.processWithdrawals state capella payload = .ok after) :
    SameSyncCommittees state after :=
  processWithdrawals_of SameSyncCommittees (.refl _) (fun _ => applyExpectedWithdrawals) ok

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
      · rw [recordPaymentWeight_eq final]; exact ⟨rfl, rfl, rfl⟩
      · cases final; exact .refl _
    have flags : ∀ (current : Bool) (participation : EpochParticipation preset fork),
        SameSyncCommittees state (setEpochParticipation state current participation) := by
      intro current participation
      unfold setEpochParticipation
      split <;> exact ⟨rfl, rfl, rfl⟩
    exact (flags _ _).trans ((increaseBalance raisedOk).trans last)
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := ok
  have kept := recordPendingAttestation_ok recorded
  split at kept <;>
  · obtain ⟨_, rest⟩ := kept
    rw [← rest]
    exact ⟨rfl, rfl, rfl⟩

private theorem processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (ok : Consensus.processBlsToExecutionChange config checks state signed = .ok after) :
    SameSyncCommittees state after := by
  obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  exact setValidator set

/-- Block operations keep both committees, one fold of the operations at a time. -/
private theorem processOperations {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (ok : Consensus.processOperations config checks state body parentSlot = .ok after) :
    SameSyncCommittees state after ∧ RegistryLifecycle state after := by
  let R := fun a b : BeaconState preset fork =>
    SameSyncCommittees a b ∧ RegistryLifecycle a b
  have refl (a) : R a a := ⟨.refl a, .refl a⟩
  have trans {a b c} (one : R a b) (two : R b c) : R a c :=
    ⟨one.1.trans two.1, one.2.trans two.2⟩
  have fold {α : Type} {step : BeaconState preset fork → α → Except TransitionError _}
      (each : ∀ a x b, step a x = .ok b → R a b)
      {a b : BeaconState preset fork} {items : List α} (ok : items.foldlM step a = .ok b) :
      R a b := (foldlM_ok_steps R refl (fun one two => trans one two) each ok).1
  obtain ⟨_, _, _, proposersOk, slashingsOk, attestedOk, rest⟩ :=
    processOperations_folds_of R refl (fun one two => trans one two)
      (fun ok => ⟨processDeposit ok, registryLifecycle_processDeposit ok⟩)
      (fun exited => ⟨initiateValidatorExit (processVoluntaryExit_initiates exited),
        registryLifecycle_processVoluntaryExit exited⟩)
      (fun ok => ⟨processBlsToExecutionChange ok, registryLifecycle_processBlsToExecutionChange ok⟩)
      (fun ok => ⟨processExecutionRequests ok, registryLifecycle_processExecutionRequests ok⟩)
      (fun paid => by rw [processPayloadAttestation_eq paid]; exact refl _) ok
  exact trans (fold (fun _ _ _ ok =>
    ⟨processProposerSlashing ok, registryLifecycle_processProposerSlashing ok⟩) proposersOk) <|
    trans (fold (fun _ _ _ ok =>
      ⟨processAttesterSlashing ok, registryLifecycle_processAttesterSlashing ok⟩) slashingsOk) <|
    trans (fold (fun _ _ _ ok =>
      ⟨processAttestation ok, registryLifecycle_processAttestation ok⟩) attestedOk) rest

private theorem processExecutionPayload {body : BeaconBlockBody preset fork}
    {engine : ExecutionEngine preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (ok : Consensus.processExecutionPayload config engine state body bellatrix = .ok after) :
    SameSyncCommittees state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
  exact ⟨rfl, rfl, rfl⟩

private theorem processExecutionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (ok : Consensus.processExecutionPayloadBid config checks state gloas signed = .ok after) :
    SameSyncCommittees state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok ok
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact ⟨rfl, rfl, rfl⟩
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at recordedOk
    subst recordedOk
    exact ⟨rfl, rfl, rfl⟩

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
  exact ⟨rfl, rfl, rfl⟩

private theorem processRandao {body : BeaconBlockBody preset fork}
    (ok : Consensus.processRandao config checks state body = .ok after) :
    SameSyncCommittees state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq ok
  exact ⟨rfl, rfl, rfl⟩

private theorem processEth1Data {before : fork < .hegota} {body : BeaconBlockBody preset fork}
    (ok : Consensus.processEth1Data before state body = .ok after) :
    SameSyncCommittees state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq ok
  rw [← rest]
  exact ⟨rfl, rfl, rfl⟩

/-- A block keeps both committees, through each step of the block.

A block frame does not carry the committees.

So the parent payload and the execution part keep their own short proofs. -/
private theorem processBlock {block : BeaconBlock preset fork}
    {engine : ExecutionEngine preset fork}
    (ok : Consensus.processBlock config checks engine state block = .ok after) :
    SameSyncCommittees state after := by
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput ok
  have head : SameSyncCommittees state input :=
    OperationsInput.step_of SameSyncCommittees .refl (fun one two => one.trans two)
      (fun _ paid => processParentExecutionPayload paid) processBlockHeader
      (fun _ executed => processBlockExecution executed) processRandao
      (fun _ voted => processEth1Data voted) started
  have tail : SameSyncCommittees last after := by
    split at synced
    · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
      exact .refl _
    · cases synced
      exact .refl _
  exact head.trans ((processOperations operated).1.trans tail)

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
  := fun ok => passPendingDeposits_of SameSyncCommittees .refl (fun one two => one.trans two)
    (fun step => applyPendingDeposit step) ok

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
  exact passPendingConsolidations ‹_›

private theorem processInactivityUpdates {altair : .altair ≤ fork}
    (ok : Consensus.processInactivityUpdates config state altair = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.processInactivityUpdates at ok
  split at ok
  · cases ok; exact .refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, rfl⟩ := ok
    exact ⟨rfl, rfl, rfl⟩

private theorem processEth1DataReset {before : fork < .hegota}
    (ok : Consensus.processEth1DataReset before state = .ok after) :
    SameSyncCommittees state after := by
  simp only [Consensus.processEth1DataReset, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok <;> cases ok <;> exact ⟨rfl, rfl, rfl⟩

private theorem processSlashingsReset (ok : Consensus.processSlashingsReset state = .ok after) :
    SameSyncCommittees state after := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq ok
  exact ⟨rfl, rfl, rfl⟩

private theorem processRandaoMixesReset (ok : Consensus.processRandaoMixesReset state = .ok after) :
    SameSyncCommittees state after := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq ok
  exact ⟨rfl, rfl, rfl⟩

private theorem processHistoricalRootsUpdate {before : fork < .shapella}
    (ok : Consensus.processHistoricalRootsUpdate state before = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.processHistoricalRootsUpdate at ok
  simp only [bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, rfl⟩ := ok
    exact ⟨rfl, rfl, rfl⟩
  · cases ok; exact .refl _

private theorem processHistoricalSummariesUpdate {capella : .shapella ≤ fork}
    (ok : Consensus.processHistoricalSummariesUpdate state capella = .ok after) :
    SameSyncCommittees state after := by
  unfold Consensus.processHistoricalSummariesUpdate at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' (split at ok <;> try cases ok)
  all_goals exact ⟨rfl, rfl, rfl⟩

private theorem processJustificationAndFinalization
    (ok : Consensus.processJustificationAndFinalization state = .ok after) :
    SameSyncCommittees state after := by
  rcases processJustificationAndFinalization_ok ok with rfl | ⟨_, _, _, weighed⟩
  · exact .refl _
  · simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok,
      pure, Except.pure, Except.ok.injEq] at weighed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := weighed
    exact ⟨rfl, rfl, rfl⟩

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

private theorem assigned_key_transfer
    (P : Epoch → Prop)
    (keys : validatorKeys state <+: validatorKeys after)
    (life : RegistryLifecycle state after) (key : BLSPubkey)
    (prior : ∃ (i : Nat) (v : Validator),
      state.validators.data[i]? = some v ∧ v.pubkey = key ∧
      v.activationEpoch ≠ FAR_FUTURE_EPOCH ∧ P v.activationEpoch) :
    ∃ (i : Nat) (v : Validator), after.validators.data[i]? = some v ∧ v.pubkey = key ∧
      v.activationEpoch ≠ FAR_FUTURE_EPOCH ∧ P v.activationEpoch := by
  obtain ⟨i, v, found, keyEq, assigned, property⟩ := prior
  obtain ⟨w, read, kept⟩ := life.validators i v found
  have pubkey : w.pubkey = v.pubkey := by
    obtain ⟨suffix, eq⟩ := keys
    have entry : (validatorKeys after)[i]? = (validatorKeys state)[i]? := by
      rw [← eq, List.getElem?_append_left]
      simpa [validatorKeys] using (Array.getElem?_eq_some_iff.mp found).1
    simpa [validatorKeys, List.getElem?_map, found, read] using entry
  exact ⟨i, w, read, pubkey.trans keyEq,
    (fun far => assigned ((kept.activationEpoch assigned).symm.trans far)),
    (kept.activationEpoch assigned) ▸ property⟩

private theorem SyncCommitteeKeys.transfer (holds : SyncCommitteeKeys state)
    (same : after.currentSyncCommittee = state.currentSyncCommittee ∧
      after.nextSyncCommittee = state.nextSyncCommittee)
    (keys : validatorKeys state <+: validatorKeys after)
    (life : RegistryLifecycle state after)
    (forward : (getCurrentEpoch state).toNat ≤ (getCurrentEpoch after).toNat := by
      first | assumption | exact Nat.le_refl _) :
    SyncCommitteeKeys after := by
  intro altair
  obtain ⟨current, next⟩ := holds altair
  constructor
  · intro key member
    rw [same.1] at member
    obtain ⟨i, v, found, keyed, assigned, bounded⟩ :=
      assigned_key_transfer (fun e => e.toNat ≤ (getCurrentEpoch state).toNat + 1)
        keys life key (current key member)
    exact ⟨i, v, found, keyed, assigned, by omega⟩
  · intro key member
    rw [same.2] at member
    obtain ⟨i, v, found, keyed, assigned, bounded⟩ :=
      assigned_key_transfer (fun e => e.toNat ≤ (getCurrentEpoch state).toNat + 1)
        keys life key (next key member)
    exact ⟨i, v, found, keyed, assigned, by omega⟩

/-- A step keeps the provenance of the committees and the slot.

It keeps both sync committees unless the epoch ahead starts a period. -/
private def CommitteeStep (state after : BeaconState preset fork) : Prop :=
  (SyncCommitteeKeys state → SyncCommitteeKeys after) ∧ after.slot = state.slot ∧
    ((getCurrentEpoch state + 1) % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD ≠ 0 →
      KeepsCommittees state after)

private theorem CommitteeStep.refl (state : BeaconState preset fork) : CommitteeStep state state :=
  ⟨id, rfl, fun _ => ⟨rfl, rfl⟩⟩

private theorem CommitteeStep.trans {a b c : BeaconState preset fork}
    (ab : CommitteeStep a b) (bc : CommitteeStep b c) : CommitteeStep a c := by
  refine ⟨bc.1 ∘ ab.1, bc.2.1.trans ab.2.1, fun inside => ?_⟩
  have epoch : getCurrentEpoch b = getCurrentEpoch a := by simp only [getCurrentEpoch, ab.2.1]
  exact (ab.2.2 inside).trans (bc.2.2 (by rw [epoch]; exact inside))

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

/-- A successful rotation computes the epoch ahead without wrapping. -/
private theorem processSyncCommitteeUpdates_epoch {altair : .altair ≤ fork}
    (ok : Consensus.processSyncCommitteeUpdates state altair = .ok after) :
    addChecked (getCurrentEpoch state) 1 = .ok (getCurrentEpoch state + 1) := by
  unfold Consensus.processSyncCommitteeUpdates at ok
  simp only [bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨epoch, epochOk, _⟩ := ok
  rw [liftArith, mapError_ok_iff] at epochOk
  have sum := addChecked_ok_iff.mp epochOk
  have same : epoch = getCurrentEpoch state + 1 :=
    UInt64.toNat_inj.mp (sum.2.trans (toNat_add_of_lt sum.1).symm)
  subst same
  exact epochOk

/-- Rotation keeps the state unless the epoch ahead starts a period. -/
private theorem processSyncCommitteeUpdates_eq_of_inside {altair : .altair ≤ fork}
    (inside : (getCurrentEpoch state + 1) % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD ≠ 0)
    (ok : Consensus.processSyncCommitteeUpdates state altair = .ok after) : after = state :=
  Except.ok.inj (ok.symm.trans
    (processSyncCommitteeUpdates_inside (processSyncCommitteeUpdates_epoch ok) inside))

/-- An epoch stage other than the two updates keeps the committees and the lookahead. -/
private theorem stage_same (altair : .altair ≤ fork) {k : EpochStage}
    (other : k ≠ .syncCommittees) (look : k ≠ .proposerLookahead) {a b : BeaconState preset fork}
    (edge : EpochStage.Edge config checks k a b) : SameSyncCommittees a b := by
  cases k <;> simp only [EpochStage.Edge, altair, ↓reduceDIte] at edge
  case justification => exact (SameSyncCommittees.processJustificationAndFinalization edge)
  case inactivity => exact (SameSyncCommittees.processInactivityUpdates edge)
  case rewards => exact (SameSyncCommittees.processRewardsAndPenalties edge)
  case registry => exact (SameSyncCommittees.processRegistryUpdates edge)
  case slashings => exact (SameSyncCommittees.processSlashings edge)
  case eth1Reset =>
    split at edge
    · exact (SameSyncCommittees.processEth1DataReset edge)
    · subst edge
      exact ⟨rfl, rfl, rfl⟩
  case pendingDeposits =>
    split at edge
    · exact (SameSyncCommittees.processPendingDeposits edge)
    · subst edge
      exact ⟨rfl, rfl, rfl⟩
  case pendingConsolidations =>
    split at edge
    · exact (SameSyncCommittees.processPendingConsolidations edge)
    · subst edge
      exact ⟨rfl, rfl, rfl⟩
  case payments =>
    split at edge
    · rw [processBuilderPendingPayments_eq edge]
      exact ⟨rfl, rfl, rfl⟩
    · subst edge
      exact ⟨rfl, rfl, rfl⟩
  case effectiveBalances => exact (SameSyncCommittees.processEffectiveBalanceUpdates edge)
  case slashingsReset => exact (SameSyncCommittees.processSlashingsReset edge)
  case randaoReset => exact (SameSyncCommittees.processRandaoMixesReset edge)
  case history =>
    split at edge
    · exact (SameSyncCommittees.processHistoricalSummariesUpdate edge)
    · exact (SameSyncCommittees.processHistoricalRootsUpdate edge)
  case participation =>
    subst edge
    exact ⟨rfl, rfl, rfl⟩
  case syncCommittees => exact absurd rfl other
  case proposerLookahead => exact absurd rfl look
  case ptcWindow =>
    split at edge
    · simp only [processPtcWindow, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at edge
      obtain ⟨_, _, _, _, rfl⟩ := edge
      exact ⟨rfl, rfl, rfl⟩
    · subst edge
      exact ⟨rfl, rfl, rfl⟩

/-- Every epoch stage but the committee update keeps both committees. -/
private theorem stage_keeps (altair : .altair ≤ fork) {k : EpochStage}
    (other : k ≠ .syncCommittees) {a b : BeaconState preset fork}
    (edge : EpochStage.Edge config checks k a b) : KeepsCommittees a b := by
  by_cases look : k = .proposerLookahead
  · subst look
    simp only [EpochStage.Edge] at edge
    split at edge
    · simp only [processProposerLookahead, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at edge
      obtain ⟨_, _, _, _, rfl⟩ := edge
      exact ⟨rfl, rfl⟩
    · subst edge
      exact ⟨rfl, rfl⟩
  · exact (stage_same altair other look edge).keeps

/-- Every epoch stage but the lookahead update keeps the lookahead. -/
private theorem stage_lookahead (altair : .altair ≤ fork) {k : EpochStage}
    (look : k ≠ .proposerLookahead) {a b : BeaconState preset fork}
    (edge : EpochStage.Edge config checks k a b) : b.proposerLookahead = a.proposerLookahead := by
  by_cases sync : k = .syncCommittees
  · subst sync
    simp only [EpochStage.Edge, altair, ↓reduceDIte] at edge
    unfold Consensus.processSyncCommitteeUpdates at edge
    simp only [bind, Except.bind, pure, Except.pure] at edge
    repeat' (split at edge <;> try cases edge)
    all_goals rfl
  · exact (stage_same altair sync look edge).2.2

/-- An epoch keeps committee provenance and the slot.

It keeps both committees unless the epoch ahead starts a period.

Every stage but the committee update keeps both committees and the key prefix of the registry. -/
private theorem processEpochStep
    (ok : Consensus.processEpoch config checks state = .ok after) : CommitteeStep state after := by
  -- Before Altair there are no sync committees, so the provenance holds.
  by_cases altair : Fork.altair ≤ fork
  case neg =>
    obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame ok
    exact ⟨fun _ altair' => absurd altair' altair,
      frame.slot.trans (processJustificationAndFinalization_slot justifiedOk),
      fun _ => ⟨funext fun altair' => absurd altair' altair,
        funext fun altair' => absurd altair' altair⟩⟩
  refine (processEpoch_trace ok).transport (fun s t => CommitteeStep s t) CommitteeStep.refl
    (fun one two => one.trans two) ?_
  intro k _ a b computed
  have edge := EpochStage.action_cases.mp computed
  have life := edge.registryLifecycle
  have slot := edge.slot_eq
  have keeps : k ≠ .syncCommittees → KeepsCommittees a b := fun other =>
    stage_keeps altair other edge
  have forward : (getCurrentEpoch a).toNat ≤ (getCurrentEpoch b).toNat := by
    simp only [getCurrentEpoch, slot, Nat.le_refl]
  cases k <;> simp only [EpochStage.Edge, altair, ↓reduceDIte] at edge
  case justification =>
    refine ⟨fun held => ?_, slot, fun _ => keeps nofun⟩
    exact held.transfer (And.imp_right And.left
      (SameSyncCommittees.processJustificationAndFinalization edge))
      (by
        simp only [validatorKeys, (processJustificationAndFinalization_keeps edge).2.2.2.2.2.1]
        exact List.prefix_refl _) life
  case inactivity =>
    refine ⟨fun held => ?_, slot, fun _ => keeps nofun⟩
    exact held.transfer (And.imp_right And.left (SameSyncCommittees.processInactivityUpdates edge))
      (frame_processInactivityUpdates edge).pubkeysPrefix life
  case rewards =>
    refine ⟨fun held => ?_, slot, fun _ => keeps nofun⟩
    exact held.transfer (And.imp_right And.left
      (SameSyncCommittees.processRewardsAndPenalties edge))
      (frame_processRewardsAndPenalties edge).pubkeysPrefix life
  case registry =>
    refine ⟨fun held => ?_, slot, fun _ => keeps nofun⟩
    exact held.transfer (And.imp_right And.left (SameSyncCommittees.processRegistryUpdates edge))
      (frame_processRegistryUpdates edge).pubkeysPrefix life
  case slashings =>
    refine ⟨fun held => ?_, slot, fun _ => keeps nofun⟩
    exact held.transfer (And.imp_right And.left (SameSyncCommittees.processSlashings edge))
      (frame_processSlashings edge).pubkeysPrefix life
  case eth1Reset =>
    split at edge
    · refine ⟨fun held => ?_, slot, fun _ => keeps nofun⟩
      exact held.transfer (And.imp_right And.left (SameSyncCommittees.processEth1DataReset edge))
        (frame_processEth1DataReset edge).pubkeysPrefix life
    · subst edge
      exact CommitteeStep.refl _
  case pendingDeposits =>
    split at edge
    · refine ⟨fun held => ?_, slot, fun _ => keeps nofun⟩
      exact held.transfer (And.imp_right And.left (SameSyncCommittees.processPendingDeposits edge))
        (frame_processPendingDeposits edge).pubkeysPrefix life
    · subst edge
      exact CommitteeStep.refl _
  case pendingConsolidations =>
    split at edge
    · refine ⟨fun held => ?_, slot, fun _ => keeps nofun⟩
      exact held.transfer (And.imp_right And.left
        (SameSyncCommittees.processPendingConsolidations edge))
        (frame_processPendingConsolidations edge).pubkeysPrefix life
    · subst edge
      exact CommitteeStep.refl _
  case payments =>
    split at edge
    · have kept := keeps nofun
      rw [processBuilderPendingPayments_eq edge] at kept ⊢
      exact ⟨fun held => held.transfer ⟨rfl, rfl⟩ (List.prefix_refl _) (.of_data rfl), rfl,
        fun _ => kept⟩
    · subst edge
      exact CommitteeStep.refl _
  case effectiveBalances =>
    refine ⟨fun held => ?_, slot, fun _ => keeps nofun⟩
    exact held.transfer (And.imp_right And.left
      (SameSyncCommittees.processEffectiveBalanceUpdates edge))
      (frame_processEffectiveBalanceUpdates edge).pubkeysPrefix life
  case slashingsReset =>
    refine ⟨fun held => ?_, slot, fun _ => keeps nofun⟩
    exact held.transfer (And.imp_right And.left (SameSyncCommittees.processSlashingsReset edge))
      (frame_processSlashingsReset edge).pubkeysPrefix life
  case randaoReset =>
    refine ⟨fun held => ?_, slot, fun _ => keeps nofun⟩
    exact held.transfer (And.imp_right And.left (SameSyncCommittees.processRandaoMixesReset edge))
      (frame_processRandaoMixesReset edge).pubkeysPrefix life
  case history =>
    split at edge
    · refine ⟨fun held => ?_, slot, fun _ => keeps nofun⟩
      exact held.transfer (And.imp_right And.left
        (SameSyncCommittees.processHistoricalSummariesUpdate edge))
        (frame_processHistoricalSummariesUpdate edge).pubkeysPrefix life
    · refine ⟨fun held => ?_, slot, fun _ => keeps nofun⟩
      exact held.transfer (And.imp_right And.left
        (SameSyncCommittees.processHistoricalRootsUpdate edge))
        (frame_processHistoricalRootsUpdate edge).pubkeysPrefix life
  case participation =>
    subst edge
    exact ⟨fun held => held.transfer ⟨rfl, rfl⟩ (List.prefix_refl _) life, slot,
      fun _ => keeps nofun⟩
  case syncCommittees =>
    exact ⟨fun held => processSyncCommitteeUpdates held edge, slot,
      fun inside => by
        rw [processSyncCommitteeUpdates_eq_of_inside inside edge]
        exact ⟨rfl, rfl⟩⟩
  case proposerLookahead =>
    split at edge
    · simp only [processProposerLookahead, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at edge
      obtain ⟨_, _, _, _, rfl⟩ := edge
      exact ⟨fun held => held.transfer ⟨rfl, rfl⟩ (List.prefix_refl _) life, slot,
        fun _ => keeps nofun⟩
    · subst edge
      exact CommitteeStep.refl _
  case ptcWindow =>
    split at edge
    · simp only [processPtcWindow, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at edge
      obtain ⟨_, _, _, _, rfl⟩ := edge
      exact ⟨fun held => held.transfer ⟨rfl, rfl⟩ (List.prefix_refl _) life, slot,
        fun _ => keeps nofun⟩
    · subst edge
      exact CommitteeStep.refl _

/-- An epoch keeps committee provenance through registry changes, rotation and the new draw.

Every stage but the committee update keeps both committees and the key prefix of the registry. -/
private theorem processEpoch (holds : SyncCommitteeKeys state)
    (ok : Consensus.processEpoch config checks state = .ok after) : SyncCommitteeKeys after :=
  (processEpochStep ok).1 holds

/-- A remainder of an epoch is zero exactly when it is zero for the integers. -/
private theorem epoch_mod_iff (epoch period : UInt64) :
    epoch % period = 0 ↔ epoch.toNat % period.toNat = 0 := by
  constructor
  · intro zero
    simpa only [UInt64.toNat_mod, UInt64.toNat_zero] using congrArg UInt64.toNat zero
  · intro zero
    apply UInt64.toNat_inj.mp
    simpa only [UInt64.toNat_mod, UInt64.toNat_zero] using zero

/-- A run of epoch stages without the committee update keeps both committees and the slot. -/
private theorem stages_keep (altair : .altair ≤ fork) {stages : List EpochStage}
    (absent : EpochStage.syncCommittees ∉ stages) {a b : BeaconState preset fork}
    (trace : EpochTrace (EpochStage.action config checks) stages a b) :
    b.slot = a.slot ∧ KeepsCommittees a b :=
  trace.transport (fun a b => b.slot = a.slot ∧ KeepsCommittees a b)
    (fun _ => ⟨rfl, rfl, rfl⟩)
    (by
      intro _ _ _ ab bc
      exact ⟨bc.1.trans ab.1, KeepsCommittees.trans ab.2 bc.2⟩)
    (fun k member _ _ computed =>
      have edge := EpochStage.action_cases.mp computed
      ⟨edge.slot_eq,
        stage_keeps altair (fun same => absurd (by rw [← same]; exact member) absent) edge⟩)

/-- An epoch that ends a period of sync committees makes the next committee the current one. -/
private theorem processEpoch_boundary (altair : .altair ≤ fork)
    (boundary : (getCurrentEpoch state + 1) % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD = 0)
    (ok : Consensus.processEpoch config checks state = .ok after) :
    after.currentSyncCommittee altair = state.nextSyncCommittee altair := by
  have trace := processEpoch_trace ok
  have shape : EpochStage.epochStages = (EpochStage.prefixStages ++ EpochStage.middleStages ++
      [.participation]) ++ (.syncCommittees :: [.proposerLookahead, .ptcWindow]) := rfl
  rw [shape] at trace
  obtain ⟨mid, early, rest⟩ := EpochTrace.append_iff.mp trace
  cases rest with
  | cons update later =>
    have first := stages_keep altair (by simp [EpochStage.prefixStages, EpochStage.middleStages])
      early
    have last := stages_keep altair (by simp) later
    have edge := EpochStage.action_cases.mp update
    simp only [EpochStage.Edge, altair, ↓reduceDIte] at edge
    have epoch : getCurrentEpoch mid = getCurrentEpoch state := by
      simp only [getCurrentEpoch, first.1]
    have rotated := processSyncCommitteeUpdates_current (processSyncCommitteeUpdates_epoch edge)
      (by rw [epoch]; exact boundary) edge
    exact (congrFun last.2.1 altair).trans (rotated.trans (congrFun first.2.2 altair))

/-- A slot updates committees only through the epoch transition.

The epoch stays, and the committees with it, or the epoch ahead starts the next one.

An epoch that does not start a period keeps both committees.

An epoch that starts a period makes the next committee current. -/
private theorem advanceSlotStep (ok : Consensus.advanceSlot config checks state = .ok after) :
    (SyncCommitteeKeys state → SyncCommitteeKeys after) ∧
      ((getCurrentEpoch after).toNat = (getCurrentEpoch state).toNat ∧ KeepsCommittees state after ∨
        (getCurrentEpoch after).toNat = (getCurrentEpoch state).toNat + 1 ∧
          ((getCurrentEpoch after).toNat % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat ≠ 0 →
            KeepsCommittees state after) ∧
          ((getCurrentEpoch after).toNat % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat = 0 →
            ∀ altair : .altair ≤ fork,
              after.currentSyncCommittee altair = state.nextSyncCommittee altair)) := by
  have later := (runKept_advanceSlot ok).later
  obtain ⟨next, cached, epoched, nextVal, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have cachedEpoch : getCurrentEpoch cached = getCurrentEpoch state := by
    rw [cachedEq]
    rfl
  have cachedKeeps : KeepsCommittees state cached := by
    rw [cachedEq]
    exact ⟨rfl, rfl⟩
  refine ⟨fun holds => ?_, ?_⟩
  · have cachedKeys : SyncCommitteeKeys cached := by rw [cachedEq]; exact holds
    have epochKeys : SyncCommitteeKeys epoched := by
      unfold epochIfLast at epochedOk
      split at epochedOk
      · exact processEpoch cachedKeys epochedOk
      · cases epochedOk; exact cachedKeys
    apply epochKeys.transfer (after := { epoched with slot := next })
      ⟨rfl, rfl⟩ (List.prefix_refl _) (.of_data rfl) ?_
    have epochedSlot : epoched.slot = state.slot := by
      unfold epochIfLast at epochedOk
      split at epochedOk
      · obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochedOk
        rw [frame.slot, processJustificationAndFinalization_slot justifiedOk, cachedEq]
      · cases epochedOk; rw [cachedEq]
    simpa only [getCurrentEpoch, epochedSlot, UInt64.le_iff_toNat_le] using later
  · have stateEpoch := getCurrentEpoch_toNat state
    unfold epochIfLast at epochedOk
    split at epochedOk
    · rename_i last
      have divides := Nat.dvd_of_mod_eq_zero ((epoch_mod_iff _ _).mp last)
      have nextEpoch : (getCurrentEpoch
          ({ epoched with slot := next } : BeaconState preset fork)).toNat =
            (getCurrentEpoch state).toNat + 1 := by
        rw [getCurrentEpoch_toNat, stateEpoch]
        show next.toNat / _ = _
        rw [nextVal]
        rw [nextVal] at divides
        exact Nat.succ_div_of_dvd divides
      have bound := (getCurrentEpoch
        ({ epoched with slot := next } : BeaconState preset fork)).toNat_lt
      have plus : getCurrentEpoch cached + 1 =
          getCurrentEpoch ({ epoched with slot := next } : BeaconState preset fork) := by
        apply UInt64.toNat_inj.mp
        have cachedNat := congrArg UInt64.toNat cachedEpoch
        rw [toNat_add_of_lt (by simp only [UInt64.toNat_one]; omega), UInt64.toNat_one]
        omega
      refine .inr ⟨nextEpoch, fun inside => ?_, fun boundary altair => ?_⟩
      · rw [← plus] at inside
        exact cachedKeeps.trans
          ((processEpochStep epochedOk).2.2 fun zero => inside ((epoch_mod_iff _ _).mp zero))
      · rw [← plus] at boundary
        exact (processEpoch_boundary altair ((epoch_mod_iff _ _).mpr boundary) epochedOk).trans
          (congrFun cachedKeeps.2 altair)
    · rename_i notLast
      cases epochedOk
      refine .inl ⟨?_, cachedKeeps⟩
      have indivisible : ¬ preset.SLOTS_PER_EPOCH.toNat ∣ next.toNat := fun divides =>
        notLast ((epoch_mod_iff _ _).mpr (Nat.mod_eq_zero_of_dvd divides))
      rw [getCurrentEpoch_toNat, stateEpoch]
      show next.toNat / _ = _
      rw [nextVal]
      rw [nextVal] at indivisible
      exact Nat.succ_div_of_not_dvd indivisible

/-- A slot updates committees only through the epoch transition. -/
private theorem advanceSlot (holds : SyncCommitteeKeys state)
    (ok : Consensus.advanceSlot config checks state = .ok after) : SyncCommitteeKeys after :=
  (advanceSlotStep ok).1 holds

/-- Blocks preserve the committees and retain all existing validator keys. -/
private theorem processBlock {block : BeaconBlock preset fork}
    {engine : ExecutionEngine preset fork} (holds : SyncCommitteeKeys state)
    (ok : Consensus.processBlock config checks engine state block = .ok after) :
    SyncCommitteeKeys after :=
  holds.transfer ((SameSyncCommittees.processBlock ok).imp_right And.left)
    (frame_processBlock ok).pubkeysPrefix
    (registryLifecycle_processBlock ok)
    (by simp only [getCurrentEpoch, (frame_processBlock ok).slot, Nat.le_refl])

private theorem carryFields {post : Fork} (upgrade : fork < post)
    (before : post < .glamsterdam) (altair : .altair ≤ fork)
    (holds : SyncCommitteeKeys state) :
    SyncCommitteeKeys (Consensus.carryFields config post state upgrade before) := by
  intro _
  simpa [Consensus.carryFields, altair, validatorKeys, carryRooted, getCurrentEpoch]
    using holds altair

private theorem carryFields_committees {post : Fork} (upgrade : fork < post)
    (before : post < .glamsterdam) (altair : .altair ≤ fork) (a : .altair ≤ post) :
    ((Consensus.carryFields config post state upgrade before).currentSyncCommittee
      a).value.pubkeys.toList =
      (state.currentSyncCommittee altair).value.pubkeys.toList ∧
    ((Consensus.carryFields config post state upgrade before).nextSyncCommittee
      a).value.pubkeys.toList =
      (state.nextSyncCommittee altair).value.pubkeys.toList := by
  simp [Consensus.carryFields, altair]

private theorem upgradeToElectra {checks : SignatureChecks} {pre : BeaconState preset .dencun}
    {post : BeaconState preset .pectra}
    (ok : Consensus.upgradeToElectra config pre = .ok post) :
    (SyncCommitteeKeys pre → SyncCommitteeKeys post) ∧
      ∀ (a : .altair ≤ Fork.pectra) (a' : .altair ≤ Fork.dencun),
      (post.currentSyncCommittee a).value.pubkeys.toList =
        (pre.currentSyncCommittee a').value.pubkeys.toList ∧
      (post.nextSyncCommittee a).value.pubkeys.toList =
        (pre.nextSyncCommittee a').value.pubkeys.toList := by
  have life := registryLifecycle_upgradeNext (pre := ⟨.dencun, pre⟩)
    (config := config) (checks := checks)
    (post := ⟨⟨.pectra, post⟩, by change Fork.dencun < Fork.pectra; decide⟩)
    (by simp [Consensus.upgradeNext, ok, Functor.map, Except.map])
  simp only [Consensus.upgradeToElectra, bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, queued, compounded⟩ := ok
  have same := (SameSyncCommittees.foldlM
    (fun _ _ _ ok => SameSyncCommittees.queuePreActivation ok) queued).trans
    (SameSyncCommittees.foldlM (fun _ _ _ ok => SameSyncCommittees.queueCompoundingExcess ok)
      compounded)
  have keys := ((BlockFrame.foldlM (fun _ _ _ ok => frame_queuePreActivation ok) queued).trans
    (BlockFrame.foldlM (fun _ _ _ ok => frame_queueCompoundingExcess ok)
      compounded)).pubkeysPrefix
  refine ⟨fun holds => ?_, fun a a' => ?_⟩
  · apply transfer ?_ (same.imp_right And.left) keys ?_ ?_
    · exact carryFields (config := config) (post := .pectra)
        (by decide) (by decide) (by decide) holds
    · exact ⟨life.size_le, life.validators⟩
    · have frame := (BlockFrame.foldlM (fun _ _ _ ok => frame_queuePreActivation ok) queued).trans
        (BlockFrame.foldlM (fun _ _ _ ok => frame_queueCompoundingExcess ok) compounded)
      simp only [getCurrentEpoch, frame.slot, Nat.le_refl]
  · rw [congrFun same.1 a, congrFun same.2.1 a]
    exact carryFields_committees (config := config) (post := .pectra) (by decide) (by decide) a' a

/-- Each upgrade either samples the first committees or carries their keys into the new registry.

It also keeps the keys of both committees, at every upgrade from Altair. -/
private theorem upgradeNextStep {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (ok : Consensus.upgradeNext config checks pre = .ok post) :
    (SyncCommitteeKeys pre.state → SyncCommitteeKeys post.val.state) ∧
      ∀ (a : .altair ≤ post.val.fork) (a' : .altair ≤ pre.fork),
        (post.val.state.currentSyncCommittee a).value.pubkeys.toList =
          (pre.state.currentSyncCommittee a').value.pubkeys.toList ∧
        (post.val.state.nextSyncCommittee a).value.pubkeys.toList =
          (pre.state.nextSyncCommittee a').value.pubkeys.toList := by
  obtain ⟨fork, state⟩ := pre
  cases fork
  case phase0 =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    exact ⟨fun _ => upgradeToAltair upgraded,
      fun _ a' => absurd a' (by change ¬ Fork.altair ≤ Fork.phase0; decide)⟩
  case altair | bellatrix | shapella =>
    simp only [Consensus.upgradeNext, pure, Except.pure, Except.ok.injEq] at ok
    subst ok
    exact ⟨fun holds => carryFields (by dsimp; decide) (by dsimp; decide) (by decide) holds,
      fun a a' => carryFields_committees (by dsimp; decide) (by dsimp; decide) a' a⟩
  case dencun =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    have electra := upgradeToElectra (checks := checks) upgraded
    exact ⟨electra.1, electra.2⟩
  case pectra =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [Consensus.upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
    obtain ⟨_, _, rfl⟩ := upgraded
    exact ⟨fun holds => carryFields (config := config) (post := .fusaka)
      (by decide) (by decide) (by decide) holds,
      fun a a' => carryFields_committees (config := config) (post := .fusaka)
        (by change Fork.pectra < Fork.fusaka; decide) (by decide) a' a⟩
  case fusaka =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [Consensus.upgradeToGloas, bind_ok_iff] at upgraded
    obtain ⟨_, _, _, _, onboarded⟩ := upgraded
    obtain ⟨⟨_, _, rfl⟩, _⟩ := onboardBuildersFromPendingDeposits_spec onboarded
    exact ⟨fun holds _ => holds (by dsimp; decide), fun _ _ => ⟨rfl, rfl⟩⟩
  case glamsterdam =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    obtain rfl := upgradeToHeze_ok_iff.mp upgraded
    exact ⟨fun holds _ => holds (by dsimp; decide), fun _ _ => ⟨rfl, rfl⟩⟩
  all_goals simp only [Consensus.upgradeNext] at ok; cases ok

/-- Each upgrade either samples the first committees or carries their keys into the new registry. -/
private theorem upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (holds : SyncCommitteeKeys pre.state)
    (ok : Consensus.upgradeNext config checks pre = .ok post) :
    SyncCommitteeKeys post.val.state :=
  (upgradeNextStep ok).1 holds

end SyncCommitteeKeys

/-- Block operations retain the current sync committee, including when they admit validators. -/
theorem processOperations_currentSyncCommittee {body : BeaconBlockBody preset fork}
    {parentSlot : Slot} (altair : .altair ≤ fork)
    (ok : processOperations config checks state body parentSlot = .ok after) :
    after.currentSyncCommittee altair = state.currentSyncCommittee altair :=
  congrFun (SameSyncCommittees.processOperations ok).1.1 altair

/-- Block operations retain assigned activation epochs for every current sync committee key. -/
theorem processOperations_syncCommittee_activation_assigned
    {body : BeaconBlockBody preset fork} {parentSlot : Slot} (altair : .altair ≤ fork)
    (holds : ∀ key ∈ (state.currentSyncCommittee altair).value.pubkeys.toList,
      ∃ (i : Nat) (v : Validator), state.validators.data[i]? = some v ∧ v.pubkey = key ∧
        v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (ok : processOperations config checks state body parentSlot = .ok after) :
    ∀ key ∈ (after.currentSyncCommittee altair).value.pubkeys.toList,
      ∃ (i : Nat) (v : Validator), after.validators.data[i]? = some v ∧ v.pubkey = key ∧
        v.activationEpoch ≠ FAR_FUTURE_EPOCH := by
  intro key member
  rw [processOperations_currentSyncCommittee altair ok] at member
  obtain ⟨i, v, found, keyed, assigned, _⟩ := assigned_key_transfer (fun _ => True)
    (frame_processOperations ok).pubkeysPrefix
    (SameSyncCommittees.processOperations ok).2 key (by
      obtain ⟨i, v, found, keyed, assigned⟩ := holds key member
      exact ⟨i, v, found, keyed, assigned, trivial⟩)
  exact ⟨i, v, found, keyed, assigned⟩

/-- Block execution retains the current sync committee. -/
theorem processBlockExecution_currentSyncCommittee {body : BeaconBlockBody preset fork}
    {engine : ExecutionEngine preset fork} {bellatrix : .bellatrix ≤ fork}
    (altair : .altair ≤ fork)
    (ok : processBlockExecution config checks engine state body bellatrix = .ok after) :
    after.currentSyncCommittee altair = state.currentSyncCommittee altair :=
  congrFun (SameSyncCommittees.processBlockExecution ok).1 altair

/-- A block retains the current sync committee. -/
theorem processBlock_currentSyncCommittee {block : BeaconBlock preset fork}
    {engine : ExecutionEngine preset fork} (altair : .altair ≤ fork)
    (ok : processBlock config checks engine state block = .ok after) :
    after.currentSyncCommittee altair = state.currentSyncCommittee altair :=
  congrFun (SameSyncCommittees.processBlock ok).1 altair

/-- A block leaves the proposer lookahead unchanged. -/
theorem processBlock_proposerLookahead {block : BeaconBlock preset fork}
    {engine : ExecutionEngine preset fork}
    (ok : processBlock config checks engine state block = .ok after) :
    after.proposerLookahead = state.proposerLookahead :=
  (SameSyncCommittees.processBlock ok).2.2

/-- A run of epoch stages without the lookahead update keeps the slot and the lookahead. -/
private theorem stages_lookahead (altair : .altair ≤ fork) {stages : List EpochStage}
    (absent : EpochStage.proposerLookahead ∉ stages) {a b : BeaconState preset fork}
    (trace : EpochTrace (EpochStage.action config checks) stages a b) :
    b.slot = a.slot ∧ b.proposerLookahead = a.proposerLookahead :=
  trace.transport (fun a b => b.slot = a.slot ∧ b.proposerLookahead = a.proposerLookahead)
    (fun _ => ⟨rfl, rfl⟩)
    (by
      intro _ _ _ ab bc
      exact ⟨bc.1.trans ab.1, bc.2.trans ab.2⟩)
    (fun k member _ _ computed =>
      have edge := EpochStage.action_cases.mp computed
      ⟨edge.slot_eq,
        SyncCommitteeKeys.stage_lookahead altair
          (fun same => absurd (by rw [← same]; exact member) absent) edge⟩)

/-- From Fulu, an epoch draws its new last epoch of proposers from a state just before the draw.

That state has the slot and the lookahead of the epoch's start.

Only the window update follows it, so the registry of the epoch's end is its registry. -/
theorem processEpoch_lookahead_cut (fulu : .fusaka ≤ fork)
    (ok : Consensus.processEpoch config checks state = .ok after) :
    ∃ (m looked : BeaconState preset fork), m.slot = state.slot ∧
      m.proposerLookahead = state.proposerLookahead ∧
      processProposerLookahead m fulu = .ok looked ∧
      after.validators.data = m.validators.data ∧
      after.proposerLookahead = looked.proposerLookahead ∧ after.slot = state.slot := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) fulu
  have trace := processEpoch_trace ok
  have shape : EpochStage.epochStages = (EpochStage.prefixStages ++ EpochStage.middleStages ++
      [.participation, .syncCommittees]) ++ [.proposerLookahead, .ptcWindow] := rfl
  rw [shape] at trace
  obtain ⟨m, early, rest⟩ := EpochTrace.append_iff.mp trace
  have kept := stages_lookahead altair
    (by simp [EpochStage.prefixStages, EpochStage.middleStages]) early
  obtain _ | ⟨draw, rest⟩ := rest
  obtain _ | ⟨window, done⟩ := rest
  cases done
  have drawEdge := EpochStage.action_cases.mp draw
  have windowEdge := EpochStage.action_cases.mp window
  have slot := windowEdge.slot_eq.trans (drawEdge.slot_eq.trans kept.1)
  simp only [EpochStage.Edge, fulu, ↓reduceDIte] at drawEdge
  refine ⟨m, _, kept.1, kept.2, drawEdge, ?_⟩
  have shape := drawEdge
  simp only [processProposerLookahead, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at shape
  obtain ⟨_, _, _, _, rfl⟩ := shape
  simp only [EpochStage.Edge] at windowEdge
  split at windowEdge
  · simp only [processPtcWindow, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at windowEdge
    obtain ⟨_, _, _, _, rfl⟩ := windowEdge
    exact ⟨rfl, rfl, slot⟩
  · subst windowEdge
    exact ⟨rfl, rfl, slot⟩

/-- Block execution leaves the proposer lookahead unchanged. -/
theorem processBlockExecution_proposerLookahead {body : BeaconBlockBody preset fork}
    {engine : ExecutionEngine preset fork} {bellatrix : .bellatrix ≤ fork}
    (ok : processBlockExecution config checks engine state body bellatrix = .ok after) :
    after.proposerLookahead = state.proposerLookahead :=
  (SameSyncCommittees.processBlockExecution ok).2.2

/-- Attestations leave the proposer lookahead unchanged. -/
theorem processAttestation_proposerLookahead {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (ok : processAttestation config checks state parentSlot attestation = .ok after) :
    after.proposerLookahead = state.proposerLookahead :=
  (SameSyncCommittees.processAttestation ok).2.2

/-- Every sync committee key activates by the next epoch of the state that holds it. -/
theorem Run.syncCommittee_activation_bounded {g x : ForkedBeaconState preset}
    (run : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g) (altair : .altair ≤ x.fork) :
    (∀ key ∈ (x.state.currentSyncCommittee altair).value.pubkeys.toList,
      ∃ (i : Nat) (v : Validator), x.state.validators.data[i]? = some v ∧ v.pubkey = key ∧
        v.activationEpoch ≠ FAR_FUTURE_EPOCH ∧
        v.activationEpoch.toNat ≤ (getCurrentEpoch x.state).toNat + 1) ∧
    (∀ key ∈ (x.state.nextSyncCommittee altair).value.pubkeys.toList,
      ∃ (i : Nat) (v : Validator), x.state.validators.data[i]? = some v ∧ v.pubkey = key ∧
        v.activationEpoch ≠ FAR_FUTURE_EPOCH ∧
        v.activationEpoch.toNat ≤ (getCurrentEpoch x.state).toNat + 1) := by
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

/-- Every sync committee key in a run from genesis has an assigned activation epoch. -/
theorem Run.syncCommittee_activation_assigned {g x : ForkedBeaconState preset}
    (run : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g) (altair : .altair ≤ x.fork) :
    (∀ key ∈ (x.state.currentSyncCommittee altair).value.pubkeys.toList,
      ∃ (i : Nat) (v : Validator), x.state.validators.data[i]? = some v ∧ v.pubkey = key ∧
        v.activationEpoch ≠ FAR_FUTURE_EPOCH) ∧
    (∀ key ∈ (x.state.nextSyncCommittee altair).value.pubkeys.toList,
      ∃ (i : Nat) (v : Validator), x.state.validators.data[i]? = some v ∧ v.pubkey = key ∧
        v.activationEpoch ≠ FAR_FUTURE_EPOCH) := by
  obtain ⟨current, next⟩ := run.syncCommittee_activation_bounded genesis altair
  constructor
  · intro key member
    obtain ⟨i, v, found, keyed, assigned, _⟩ := current key member
    exact ⟨i, v, found, keyed, assigned⟩
  · intro key member
    obtain ⟨i, v, found, keyed, assigned, _⟩ := next key member
    exact ⟨i, v, found, keyed, assigned⟩

/-- Every current and next sync committee key in a run from genesis belongs to its registry. -/
theorem Run.syncCommittee_keys {g x : ForkedBeaconState preset} (run : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g) (altair : .altair ≤ x.fork) :
    (∀ key ∈ (x.state.currentSyncCommittee altair).value.pubkeys.toList,
      key ∈ validatorKeys x.state) ∧
    (∀ key ∈ (x.state.nextSyncCommittee altair).value.pubkeys.toList,
      key ∈ validatorKeys x.state) := by
  have project (key) (found : ∃ (i : Nat) (v : Validator),
      x.state.validators.data[i]? = some v ∧ v.pubkey = key ∧
      v.activationEpoch ≠ FAR_FUTURE_EPOCH) : key ∈ validatorKeys x.state := by
    obtain ⟨i, v, read, rfl, _⟩ := found
    exact List.mem_map.mpr ⟨v, by simpa using Array.mem_of_getElem? read, rfl⟩
  obtain ⟨current, next⟩ := run.syncCommittee_activation_assigned genesis altair
  exact ⟨fun key member => project key (current key member),
    fun key member => project key (next key member)⟩

/-- The epoch of a state. -/
private abbrev epochOf (state : ForkedBeaconState preset) : Nat :=
  (getCurrentEpoch state.state).toNat

/-- The keys of the current sync committee of a state. -/
private abbrev curKeys (state : ForkedBeaconState preset) (altair : .altair ≤ state.fork) :=
  (state.state.currentSyncCommittee altair).value.pubkeys.toList

/-- The keys of the next sync committee of a state. -/
private abbrev nxtKeys (state : ForkedBeaconState preset) (altair : .altair ≤ state.fork) :=
  (state.state.nextSyncCommittee altair).value.pubkeys.toList

/-- The upgrades due at a slot keep the keys of both sync committees. -/
private theorem processUpgrades_committees {forked after : ForkedBeaconState preset}
    (upgrades : processUpgrades config checks forked = .ok after)
    (altair' : .altair ≤ forked.fork) (altair : .altair ≤ after.fork) :
    curKeys after altair = curKeys forked altair' ∧
      nxtKeys after altair = nxtKeys forked altair' := by
  have kept := processUpgrades_induction (config := config) (checks := checks)
    (property := fun post => forked.fork ≤ post.fork ∧ ∀ a : .altair ≤ post.fork,
        curKeys post a = curKeys forked altair' ∧ nxtKeys post a = nxtKeys forked altair')
    (fun {pre post} holds next => by
      have later : forked.fork ≤ post.val.fork := Nat.le_trans holds.1 (Nat.le_of_lt post.property)
      refine ⟨later, fun a => ?_⟩
      have moved := (SyncCommitteeKeys.upgradeNextStep next).2 a (Nat.le_trans altair' holds.1)
      have prior := holds.2 (Nat.le_trans altair' holds.1)
      exact ⟨moved.1.trans prior.1, moved.2.trans prior.2⟩)
    (forked := forked) ⟨Nat.le_refl _, fun _ => ⟨rfl, rfl⟩⟩ upgrades
  exact kept.2 altair

/-- A slot with its upgrades keeps the keys of both sync committees inside a period.

When it starts the next period, the keys of the current committee are the next ones before. -/
private theorem advanceSlotAcross_committees {forked after : ForkedBeaconState preset}
    (ok : advanceSlotAcross config checks forked = .ok after)
    (altair : .altair ≤ after.fork) (altair' : .altair ≤ forked.fork) :
    (epochOf after = epochOf forked ∧
      curKeys after altair = curKeys forked altair' ∧
      nxtKeys after altair = nxtKeys forked altair') ∨
    (epochOf after = epochOf forked + 1 ∧
      (epochOf after % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat ≠ 0 →
        curKeys after altair = curKeys forked altair' ∧
          nxtKeys after altair = nxtKeys forked altair') ∧
      (epochOf after % preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat = 0 →
        curKeys after altair = nxtKeys forked altair')) := by
  obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
  have epoch : getCurrentEpoch after.state = getCurrentEpoch advanced := by
    simp only [getCurrentEpoch, processUpgrades_slot upgrades]
  have epochNat : epochOf after = (getCurrentEpoch advanced).toNat := congrArg UInt64.toNat epoch
  have moved := processUpgrades_committees upgrades altair' altair
  rw [epochNat]
  rcases (SyncCommitteeKeys.advanceSlotStep slotOk).2 with ⟨same, keeps⟩ | ⟨plus, inside, boundary⟩
  · exact .inl ⟨same, moved.1.trans (by simp only [curKeys, keeps.1]),
      moved.2.trans (by simp only [nxtKeys, keeps.2])⟩
  · refine .inr ⟨plus, fun h => ?_, fun h => ?_⟩
    · have kept := inside h
      exact ⟨moved.1.trans (by simp only [curKeys, kept.1]),
        moved.2.trans (by simp only [nxtKeys, kept.2])⟩
    · exact moved.1.trans (by simp only [curKeys, nxtKeys, boundary h altair'])

/-- Along a step, the keys of the committees follow the periods of the epochs.

Inside a period they stay, and the first epoch of the next period makes the next keys current. -/
private theorem committees_step {α : Type} {period ex em el : Nat}
    {cx nx cm nm cl nl : List α} (low : ex ≤ em)
    (step : (el = em ∧ cl = cm ∧ nl = nm) ∨
      (el = em + 1 ∧ (el % period ≠ 0 → cl = cm ∧ nl = nm) ∧ (el % period = 0 → cl = nm)))
    (prior : (em / max 1 period = ex / max 1 period → cm = cx ∧ nm = nx) ∧
      (period ≠ 0 → em / max 1 period = ex / max 1 period + 1 → cm = nx)) :
    (el / max 1 period = ex / max 1 period → cl = cx ∧ nl = nx) ∧
      (period ≠ 0 → el / max 1 period = ex / max 1 period + 1 → cl = nx) := by
  rcases step with ⟨rfl, rfl, rfl⟩ | ⟨rfl, inside, boundary⟩
  · exact prior
  rcases Nat.eq_zero_or_pos period with zero | positive
  · subst zero
    refine ⟨fun h => ?_, fun nonzero => absurd rfl nonzero⟩
    have one : max 1 0 = 1 := by decide
    rw [one, Nat.div_one, Nat.div_one] at h
    exfalso
    omega
  have positive' : max 1 period = period := Nat.max_eq_right (Nat.succ_le_of_lt positive)
  rw [positive'] at prior ⊢
  have mono := Nat.div_le_div_right (c := period) low
  by_cases divides : period ∣ em + 1
  · have succ := Nat.succ_div_of_dvd divides
    have rotated := boundary (Nat.mod_eq_zero_of_dvd divides)
    refine ⟨fun h => ?_, fun _ h => ?_⟩
    · rw [succ] at h
      exfalso
      omega
    · rw [succ] at h
      exact rotated.trans (prior.1 (by omega)).2
  · have succ := Nat.succ_div_of_not_dvd divides
    have kept := inside fun zero => divides (Nat.dvd_of_mod_eq_zero zero)
    refine ⟨fun h => ?_, fun nonzero h => ?_⟩
    · rw [succ] at h
      have before := prior.1 h
      exact ⟨kept.1.trans before.1, kept.2.trans before.2⟩
    · rw [succ] at h
      exact kept.1.trans (prior.2 nonzero h)

/-- Along a run, the keys of the committees follow the periods of the epochs.

Inside the period of the start they stay.

In the next period the keys of the current committee are the next ones at the start. -/
private theorem Run.committees_of_periods {x y : ForkedBeaconState preset}
    (tail : Run config checks x y)
    (altair : .altair ≤ y.fork) (altair' : .altair ≤ x.fork) :
    (epochOf y / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
        epochOf x / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat →
      curKeys y altair = curKeys x altair' ∧ nxtKeys y altair = nxtKeys x altair') ∧
    (preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat ≠ 0 →
      epochOf y / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
        epochOf x / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 1 →
      curKeys y altair = nxtKeys x altair') := by
  induction tail with
  | nil => exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ h => absurd h (by omega)⟩
  | @snoc middle last pre step ih =>
    have midAltair := Nat.le_trans altair' (fork_le_of_chainSteps pre.chainSteps)
    have low := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
    refine committees_step low ?_ (ih midAltair)
    cases step with
    | block engine signed _ ok =>
      have processed := (applySignedBlock_ok ok).2.1
      have same := SameSyncCommittees.processBlock processed
      have slot := (frame_processBlock processed).slot
      refine .inl ⟨?_, ?_, ?_⟩
      · simp only [epochOf, getCurrentEpoch, slot]
      · simp only [curKeys, same.1]
      · simp only [nxtKeys, same.2.1]
    | slot ok => exact advanceSlotAcross_committees ok altair midAltair

/-- Inside one period of sync committees, from Altair, the keys of the current committee stay. -/
theorem Run.currentSyncCommittee_eq_of_same_period {x y : ForkedBeaconState preset}
    (tail : Run config checks x y)
    (same : (getCurrentEpoch y.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
      (getCurrentEpoch x.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
    (altair : .altair ≤ y.fork) (altair' : .altair ≤ x.fork) :
    (y.state.currentSyncCommittee altair).value.pubkeys.toList =
      (x.state.currentSyncCommittee altair').value.pubkeys.toList :=
  ((tail.committees_of_periods altair altair').1 same).1

/-- Across one sync-period boundary, the current sync committee is the next one of the start. -/
theorem Run.currentSyncCommittee_eq_nextSyncCommittee_of_next_period
    {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (syncPeriod : preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD ≠ 0)
    (next : (getCurrentEpoch y.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
      (getCurrentEpoch x.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 1)
    (altair : .altair ≤ y.fork) (altair' : .altair ≤ x.fork) :
    (y.state.currentSyncCommittee altair).value.pubkeys.toList =
      (x.state.nextSyncCommittee altair').value.pubkeys.toList :=
  (tail.committees_of_periods altair altair').2
    (fun zero => syncPeriod (UInt64.toNat_inj.mp (by rw [UInt64.toNat_zero]; exact zero))) next

end EthLib.Consensus
