module

public import EthLib.Consensus.Proofs.DirectSafety.Attestations
public import EthLib.Consensus.Proofs.DirectSafety.Fields
public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Consensus.Proofs.Transition.TargetUpgrades

/-!
# Slashed validators come from evidence on the selected history

A slashed flag in a reachable registry must originate in a slashing operation of the run.

The walk follows the state transition operation by operation; no abstract protocol is an input.

The steps of an epoch use the generic traversal of the epoch laws.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- Slashing operations carry evidence even when their votes were not included as attestations. -/
def _root_.EthLib.Consensus.Step.SlashingEvidence {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (key : BLSPubkey) : Prop :=
  match step with
  | .slot _ => False
  | .block _ signed _ _ =>
    (∃ sl ∈ signed.message.body.proposerSlashings.data.toList, ∃ v,
      x.state.validators.data[sl.signedHeader1.message.proposerIndex.toNat]? = some v ∧
      v.pubkey = key) ∨
    (∃ sl ∈ signed.message.body.attesterSlashings.data.toList, ∃ i ∈ slashingIndices sl, ∃ v,
      x.state.validators.data[i.toNat]? = some v ∧ v.pubkey = key)

/-- A block of the run carries a slashing that names `key`. -/
def _root_.EthLib.Consensus.Run.SlashingEvidence {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (key : BLSPubkey) : Prop :=
  ∃ x y, ∃ step : Step config checks x y, run.Contains step ∧ step.SlashingEvidence key

/-- Both header checks that a block of the run executed for one of its proposer slashings.

Each check is for `key`, the key of the proposer at the state of the check, and accepted. -/
structure HeaderCheck {g a : ForkedBeaconState preset} (run : Run config checks g a)
    (key : BLSPubkey) extends CheckSite run where
  pre : List ProposerSlashing
  post : List ProposerSlashing
  slashing : ProposerSlashing
  checked : BeaconState preset fork
  next : BeaconState preset fork
  split : signed.message.body.proposerSlashings.data.toList = pre ++ slashing :: post
  earlier : pre.foldlM (processProposerSlashing config checks) input = .ok checked
  processed : processProposerSlashing config checks checked slashing = .ok next
  proposer : ∃ v,
    checked.validators.data[slashing.signedHeader1.message.proposerIndex.toNat]? = some v ∧
      v.pubkey = key
  first : checkHeaderSignature config checks checked key slashing.signedHeader1 = .ok ()
  second : checkHeaderSignature config checks checked key slashing.signedHeader2 = .ok ()

/-- Two different headers of one proposer at one slot, as a proposer slashing requires. -/
def ProposerConflict (slashing : ProposerSlashing) : Prop :=
  slashing.signedHeader1.message.slot = slashing.signedHeader2.message.slot ∧
    slashing.signedHeader1.message.proposerIndex =
      slashing.signedHeader2.message.proposerIndex ∧
    slashing.signedHeader1.message ≠ slashing.signedHeader2.message

-- The predicate follows public keys, so registry growth does not require a fixed index set.
private def SlashedBacked (evidence : BLSPubkey → Prop) {fork : Fork}
    (state : BeaconState preset fork) : Prop :=
  ∀ v ∈ state.validators.data.toList, v.slashed = true → evidence v.pubkey

-- Ordinary mutators cannot introduce a slashed key that lacked evidence before the mutation.
private def SlashedKept {fork post : Fork} (state : BeaconState preset fork)
    (after : BeaconState preset post) : Prop :=
  ∀ evidence, SlashedBacked evidence state → SlashedBacked evidence after

private theorem SlashedKept.refl {fork : Fork} (state : BeaconState preset fork) :
    SlashedKept state state := fun _ => id

private theorem SlashedKept.trans {f₁ f₂ f₃ : Fork} {s : BeaconState preset f₁}
    {t : BeaconState preset f₂} {u : BeaconState preset f₃}
    (one : SlashedKept s t) (two : SlashedKept t u) : SlashedKept s u :=
  fun evidence backed => two evidence (one evidence backed)

private theorem SlashedKept.of_validators {fork post : Fork} {state : BeaconState preset fork}
    {after : BeaconState preset post} (same : after.validators.data = state.validators.data :=
      by rfl) : SlashedKept state after := by
  intro evidence backed
  simpa only [SlashedBacked, same] using backed

private theorem SlashedKept.foldlM {fork : Fork} {α ε : Type}
    {step : BeaconState preset fork → α → Except ε _}
    (keeps : ∀ s x t, step s x = .ok t → SlashedKept s t)
    {items : List α} {state after : BeaconState preset fork}
    (ok : items.foldlM step state = .ok after) : SlashedKept state after :=
  foldlM_ok_invariant (SlashedKept state)
    (fun _ _ _ before computed => before.trans (keeps _ _ _ computed)) (.refl state) ok

namespace SlashedKept

variable {fork : Fork} {state after : BeaconState preset fork}

private theorem setValidatorAt {position : Nat} {v old : Validator}
    (found : getValidatorAt state position = .ok old)
    (key : v.pubkey = old.pubkey) (flag : v.slashed = old.slashed)
    (set : state.setValidatorAt position v = .ok after) : SlashedKept state after := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have oldEq : state.validators.data[position] = old := by
    simpa [getValidatorAt, inside] using found
  intro evidence backed current member slashed
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.toList_set] at member
  rcases List.mem_or_eq_of_mem_set member with member | equal
  · exact backed current member slashed
  · subst current
    rw [key]
    apply backed old
    · rw [← oldEq]
      simp
    · rwa [flag] at slashed

private theorem setValidator {index : ValidatorIndex} {v old : Validator}
    (found : getValidator state index = .ok old)
    (key : v.pubkey = old.pubkey) (flag : v.slashed = old.slashed)
    (set : state.setValidator index v = .ok after) : SlashedKept state after :=
  setValidatorAt (by rwa [← getValidator_eq_getValidatorAt]) key flag
    (by rwa [← setValidator_eq_setValidatorAt])

private theorem increaseBalance {index : ValidatorIndex} {amount : Gwei}
    (ok : Consensus.increaseBalance state index amount = .ok after) : SlashedKept state after :=
  of_validators (congrArg (·.data) (increaseBalance_validators ok))

private theorem decreaseBalance {index : ValidatorIndex} {amount : Gwei}
    (ok : Consensus.decreaseBalance state index amount = .ok after) : SlashedKept state after :=
  of_validators (congrArg (·.data) (decreaseBalance_validators ok))

private theorem initiateValidatorExit {index : ValidatorIndex}
    (ok : Consensus.initiateValidatorExit config state index = .ok after) :
    SlashedKept state after := by
  obtain ⟨v, found, unchanged | ⟨_, queued, epoch, withdrawal, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · rw [unchanged.2]; exact refl _
  · have same := (exitQueue_validators queue).1
    exact (of_validators (congrArg (·.data) same)).trans
      (setValidator (old := v) (v := { v with exitEpoch := epoch, withdrawableEpoch := withdrawal })
        (by rw [getValidator_of_validators_eq same]; exact found)
        rfl rfl set)

private theorem append {v : Validator}
    (added : after.validators.data = state.validators.data.push v) (flag : v.slashed = false) :
    SlashedKept state after := by
  intro evidence backed current member slashed
  simp only [added, Array.toList_push, List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact backed current member slashed
  · simp [flag] at slashed

/-- A write keeps the key and the slashed flag of its validator.

Every other epoch step leaves both alone, so the generic traversal of an epoch applies.

The registry updates are among them, by the laws that the epoch traversal derives from the write.
-/
private theorem slashedKeptLaws :
    EpochFrameLaws (preset := preset) (fork := fork) fun s t => SlashedKept s t where
  refl := refl
  trans := trans
  setValidatorAt := fun set found key flag _ _ => setValidatorAt found key flag set
  increaseBalance := increaseBalance
  decreaseBalance := decreaseBalance
  initiateValidatorExit := initiateValidatorExit
  addValidatorToRegistry := fun added _ =>
    append (addValidatorToRegistry_validators_eq_push added) rfl
  eth1DataVotes _ _ := of_validators
  inactivityScores _ _ := of_validators
  slashings _ _ := of_validators
  randaoMixes _ _ := of_validators
  historicalRoots _ _ := of_validators
  historicalSummaries _ _ := of_validators
  participationRecords _ := of_validators
  pendingDeposits _ _ _ := of_validators
  pendingConsolidations _ _ := of_validators
  syncCommittees _ _ _ := of_validators
  proposerLookahead _ _ := of_validators
  ptcWindow _ _ := of_validators


private theorem applyDeposit {pubkey : BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    {signature : BLSSignature}
    (ok : Consensus.applyDeposit config checks state pubkey credentials amount signature =
      .ok after) : SlashedKept state after := by
  unfold Consensus.applyDeposit at ok
  split at ok
  · unfold applyDepositElectra at ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨middle, added, queued⟩ := ok
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq queued
        exact (append (addValidatorToRegistry_validators_eq_push added) rfl).trans
          (of_validators (state := middle))
      · cases ok; exact refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp ok)
      exact of_validators
  · exact slashedKeptLaws.applyPendingDeposit ok

private theorem processDeposit {before : fork < .hegota} {deposit : Deposit}
    (ok : Consensus.processDeposit config checks before state deposit = .ok after) :
    SlashedKept state after := by
  obtain ⟨_, _, next, _, credited⟩ := processDeposit_ok ok
  exact (of_validators (state := state)
    (after := { state with eth1DepositIndex := fun _ => next })).trans (applyDeposit credited)

private theorem genesisDeposit {before : fork < .hegota} {leaves : Array DepositData}
    {entry : Deposit × Nat}
    (ok : Consensus.genesisDeposit config checks before leaves state entry = .ok after) :
    SlashedKept state after := by
  simp only [Consensus.genesisDeposit, bind_ok_iff] at ok
  obtain ⟨root, _, deposited⟩ := ok
  exact (of_validators (state := state)
    (after := { state with
      eth1Data := fun _ => { state.eth1Data before with depositRoot := root } })).trans
    (processDeposit deposited)

private theorem activateAtGenesis {index : Nat}
    (ok : Consensus.activateAtGenesis state index = .ok after) : SlashedKept state after := by
  simp only [Consensus.activateAtGenesis, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨v, found, _, _, set⟩ := ok
  apply setValidatorAt found _ _ set <;> split <;> rfl

private theorem genesis {hash : Hash32} {time : UInt64} {deposits : Array Deposit}
    (ok : initializeBeaconStateFromEth1 config checks hash time deposits = .ok after) :
    SlashedBacked (fun _ => False) after := by
  obtain ⟨before, genesisTime, root, deposited, activated, finalRoot, depositedOk, activatedOk,
    rfl⟩ := initializeBeaconStateFromEth1_ok ok
  have first := foldlM (fun _ _ _ ok => genesisDeposit ok) depositedOk
  have second := foldlM (fun _ _ _ ok => activateAtGenesis ok) activatedOk
  exact (first.trans second) (fun _ => False) (by simp [SlashedBacked, emptyGenesisState])

private theorem processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (ok : Consensus.processDepositRequest state electra request = .ok after) :
    SlashedKept state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [Consensus.processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit,
    bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  exact of_validators

private theorem requestPartialWithdrawal {electra : .pectra ≤ fork} {index : ValidatorIndex}
    {v : Validator} {amount owed : Gwei}
    (ok : Consensus.requestPartialWithdrawal config state electra index v amount owed = .ok after) :
    SlashedKept state after := by
  simp only [Consensus.requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure]
    at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
    exact of_validators (by rw [(computeExitEpochAndUpdateChurn_earliest churned).2.1])
  · cases ok; exact refl _

private theorem processWithdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (ok : Consensus.processWithdrawalRequest config state electra request = .ok after) :
    SlashedKept state after := by
  unfold Consensus.processWithdrawalRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact refl _)
    | exact initiateValidatorExit (liftAccessor_ok.mp ok)
    | exact requestPartialWithdrawal ok

private theorem queueExcessActiveBalance {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.queueExcessActiveBalance state electra index = .ok after) :
    SlashedKept state after := by
  simp only [Consensus.queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact of_validators
  · cases ok; exact refl _

private theorem switchToCompoundingValidator {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.switchToCompoundingValidator state electra index = .ok after) :
    SlashedKept state after := by
  simp only [Consensus.switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, found, _, set, queued⟩ := ok
  exact (setValidator found (by rfl) (by rfl) set).trans (queueExcessActiveBalance queued)

private theorem queueConsolidation {electra : .pectra ≤ fork}
    {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (found : state.validators.data[sourceIndex.toNat]? = some source)
    (ok : Consensus.queueConsolidation config state electra sourceIndex source targetIndex =
      .ok after) : SlashedKept state after := by
  simp only [Consensus.queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, Uint64.addChecked_ok_iff, pure, Except.pure] at ok
  obtain ⟨⟨churnedState, exitEpoch⟩, churned, withdrawal, _, _, set, _, _, ok⟩ := ok
  simp only [Except.ok.injEq] at ok
  subst ok
  have validators := (computeConsolidationEpochAndUpdateChurn_earliest churned).2.1
  have first : SlashedKept state churnedState := of_validators (by rw [validators])
  have found' : getValidator churnedState sourceIndex = .ok source := by
    rw [getValidator, validators, found]
  exact first.trans ((setValidator found' (by rfl) (by rfl) set).trans of_validators)

private theorem processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (ok : Consensus.processConsolidationRequest config state electra request = .ok after) :
    SlashedKept state after := by
  unfold Consensus.processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact refl _)
    | exact switchToCompoundingValidator (liftAccessor_ok.mp ok)
    | exact queueConsolidation (getElem?_toNat_of_ofNatChecked (by assumption)) ok

-- EIP-8282, Consensus Layer Processing: builder requests touch a separate registry.
private theorem builderDeposit {gloas : .glamsterdam ≤ fork} {request : BuilderDepositRequest}
    (ok : processBuilderDepositRequest config checks state gloas request = .ok after) :
    SlashedKept state after := by
  unfold processBuilderDepositRequest addBuilderToRegistry at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first | (cases ok; done) | (cases ok; exact of_validators)

private theorem builderExit {gloas : .glamsterdam ≤ fork} {request : BuilderExitRequest}
    (ok : processBuilderExitRequest config state gloas request = .ok after) :
    SlashedKept state after := by
  rcases processBuilderExitRequest_cases ok with rfl | ⟨_, _, _, _, _, exited⟩
  · exact refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact of_validators

-- EIP-7732, Beacon chain changes: requests move to the parent payload's processing.
private theorem parentPayload {gloas : .glamsterdam ≤ fork} {body : BeaconBlockBody preset fork}
    (ok : processParentExecutionPayload config checks state gloas body = .ok after) :
    SlashedKept state after := by
  rcases processParentExecutionPayload_ok ok with ⟨_, _, rfl⟩ |
    ⟨_, settled, _, _, _, _, _, _, settledOk, depositsOk, withdrawalsOk, consolidationsOk,
      buildersOk, exitsOk, _, rfl⟩
  · exact refl _
  · have first : SlashedKept state settled := by
      rw [settleParentPayment_eq settledOk]
      exact of_validators
    exact first.trans <|
      (foldlM (fun _ _ _ ok => processDepositRequest ok) depositsOk).trans <|
      (foldlM (fun _ _ _ ok => processWithdrawalRequest ok) withdrawalsOk).trans <|
      (foldlM (fun _ _ _ ok => processConsolidationRequest ok) consolidationsOk).trans <|
      (foldlM (fun _ _ _ ok => builderDeposit ok) buildersOk).trans <|
      (foldlM (fun _ _ _ ok => builderExit ok) exitsOk).trans of_validators

private theorem executionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (ok : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    SlashedKept state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok ok
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact of_validators
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at recordedOk
    subst recordedOk
    exact of_validators

private theorem processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (ok : Consensus.processExecutionRequests config state body electra = .ok after) :
    SlashedKept state after := by
  simp only [Consensus.processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, deposits, _, withdrawals, consolidations⟩ := ok
  exact (foldlM (fun _ _ _ ok => processDepositRequest ok) deposits).trans
    ((foldlM (fun _ _ _ ok => processWithdrawalRequest ok) withdrawals).trans
      (foldlM (fun _ _ _ ok => processConsolidationRequest ok) consolidations))

private theorem applyWithdrawal {withdrawal : Withdrawal}
    (ok : Consensus.applyWithdrawal state withdrawal = .ok after) : SlashedKept state after := by
  unfold Consensus.applyWithdrawal at ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, set⟩ := ok
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact of_validators
  · exact decreaseBalance ok

private theorem applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (ok : Consensus.applyExpectedWithdrawals state capella expected = .ok after) :
    SlashedKept state after := by
  unfold Consensus.applyExpectedWithdrawals at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := ok
  have one : SlashedKept state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact foldlM (fun _ _ _ ok => applyWithdrawal ok) appliedOk
  have indexedStep : SlashedKept applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      exact of_validators
    · cases indexedOk; exact refl _
  have queued : ∀ s : BeaconState preset fork,
      SlashedKept s (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals s gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount else s) := by
    intro s
    split <;> exact of_validators
  have partials : ∀ s : BeaconState preset fork,
      SlashedKept s (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals s electra expected.processedPartialWithdrawalsCount
      else s) := by
    intro s
    split <;> exact of_validators
  have swept : ∀ s : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex s gloas expected.processedBuildersSweepCount
      else pure s) = .ok finished → SlashedKept s finished := by
    intro s computed
    split at computed
    · unfold updateNextWithdrawalBuilderIndex at computed
      dsimp only at computed
      split at computed
      · cases computed; exact of_validators
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
        obtain ⟨_, _, rfl⟩ := computed
        exact of_validators
    · cases computed; exact refl _
  have lastStep : SlashedKept finished after := by
    unfold updateNextWithdrawalValidatorIndex at last
    simp only [bind_ok_iff] at last
    obtain ⟨_, _, last⟩ := last
    split at last
    · cases last
    · cases last; exact of_validators
  exact one.trans (indexedStep.trans ((queued _).trans ((partials _).trans
    ((swept _ sweptOk).trans lastStep))))

private theorem processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (ok : Consensus.processWithdrawals state capella payload = .ok after) :
    SlashedKept state after := by
  unfold Consensus.processWithdrawals at ok
  split at ok
  · split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, applied⟩ := ok
      exact applyExpectedWithdrawals applied
    · cases ok; exact refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, applied⟩ := ok
    exact applyExpectedWithdrawals applied

private theorem processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (ok : Consensus.processBlsToExecutionChange config checks state signed = .ok after) :
    SlashedKept state after := by
  obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  exact setValidator found (by rfl) (by rfl) set

private theorem processSyncAggregate {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    (ok : Consensus.processSyncAggregate config checks state altair aggregate = .ok after) :
    SlashedKept state after := by
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

private theorem processVoluntaryExit {signed : SignedVoluntaryExit}
    (ok : Consensus.processVoluntaryExit config checks state signed = .ok after) :
    SlashedKept state after := by
  unfold Consensus.processVoluntaryExit at ok
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ok
  exact initiateValidatorExit exited

private theorem processJustificationAndFinalization
    (ok : Consensus.processJustificationAndFinalization state = .ok after) :
    SlashedKept state after :=
  of_validators (by rw [(processJustificationAndFinalization_keeps ok).2.2.2.2.2.1])

private theorem processEpoch (ok : Consensus.processEpoch config checks state = .ok after) :
    SlashedKept state after := by
  unfold Consensus.processEpoch at ok
  split at ok
  · obtain ⟨pending, paid, rooted, pendingOk, paidOk, middle, tail⟩ :=
      slashedKeptLaws.processEpochAltair_paymentSplit ok
    obtain ⟨justified, justifiedOk, head⟩ := slashedKeptLaws.epochBeforePayments_split pendingOk
    have paidStep : SlashedKept pending paid := by
      split at paidOk
      · simp only [processBuilderPendingPayments, liftAccessor_ok, bind_ok_iff, pure,
          Except.pure, Except.ok.injEq] at paidOk
        obtain ⟨_, _, rfl⟩ := paidOk
        exact of_validators
      · cases paidOk; exact refl _
    exact (processJustificationAndFinalization justifiedOk).trans <| head.trans <|
      paidStep.trans <| middle.trans <| (of_validators (state := rooted)).trans tail
  · simp only [bind_ok_iff] at ok
    obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
      slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
      rootedOk, rotated⟩ := ok
    exact (processJustificationAndFinalization justifiedOk).trans <|
      (slashedKeptLaws.processRewardsAndPenalties rewardedOk).trans <|
      (slashedKeptLaws.processRegistryUpdates registeredOk).trans <|
      (slashedKeptLaws.processSlashings slashedOk).trans <|
      (slashedKeptLaws.processEth1DataReset resetOk).trans <|
      (slashedKeptLaws.processEffectiveBalanceUpdates balancedOk).trans <|
      (slashedKeptLaws.processSlashingsReset clearedOk).trans <|
      (slashedKeptLaws.processRandaoMixesReset mixedOk).trans <|
      (slashedKeptLaws.processHistoricalRootsUpdate rootedOk).trans
        (slashedKeptLaws.processParticipationRecordUpdates rotated)


private theorem advanceSlot (ok : Consensus.advanceSlot config checks state = .ok after) :
    SlashedKept state after := by
  obtain ⟨next, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have first : SlashedKept state cached := of_validators (by rw [cachedEq])
  have second : SlashedKept cached epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact processEpoch epochedOk
    · cases epochedOk; exact refl _
  exact (first.trans second).trans of_validators

private theorem queuePreActivation {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (ok : Consensus.queuePreActivation state electra index = .ok after) :
    SlashedKept state after := by
  simp only [Consensus.queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨v, found, _, _, _, _, _, set₁, _, set₂, rfl⟩ := ok
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  exact (of_validators (state := state)).trans <|
    (setValidator (by exact found) (by rfl) (by rfl) set₂).trans of_validators

private theorem queueCompoundingExcess {electra : .pectra ≤ fork} {index : Nat}
    (ok : Consensus.queueCompoundingExcess state electra index = .ok after) :
    SlashedKept state after := by
  unfold Consensus.queueCompoundingExcess at ok
  split at ok
  · split at ok
    · exact queueExcessActiveBalance (liftAccessor_ok.mp ok)
    · cases ok; exact refl _
  · cases ok; exact refl _

private theorem upgradeToElectra {pre : BeaconState preset .dencun}
    {post : BeaconState preset .pectra}
    (ok : Consensus.upgradeToElectra config pre = .ok post) : SlashedKept pre post := by
  simp only [Consensus.upgradeToElectra, bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, queued, compounded⟩ := ok
  exact (of_validators (state := pre)).trans <|
    (foldlM (fun _ _ _ ok => queuePreActivation ok) queued).trans
      (foldlM (fun _ _ _ ok => queueCompoundingExcess ok) compounded)

private theorem upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (ok : Consensus.upgradeNext config checks pre = .ok post) :
    SlashedKept pre.state post.val.state := by
  obtain ⟨fork, state⟩ := pre
  cases fork
  case phase0 =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    exact of_validators (upgradeToAltair_spec upgraded).1
  case altair | bellatrix | shapella =>
    simp only [Consensus.upgradeNext, pure, Except.pure, Except.ok.injEq] at ok
    subst ok
    exact of_validators
  case dencun =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    exact upgradeToElectra upgraded
  case pectra =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    exact of_validators (upgradeToFulu_spec upgraded).1
  case fusaka =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    exact of_validators (upgradeToGloas_spec upgraded).1
  case glamsterdam =>
    simp only [Consensus.upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, upgraded, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact of_validators (upgradeHezeFields_lists _).1
  all_goals simp only [Consensus.upgradeNext] at ok; cases ok

private theorem advanceSlotAcross {pre post : ForkedBeaconState preset}
    (ok : Consensus.advanceSlotAcross config checks pre = .ok post) :
    SlashedKept pre.state post.state := by
  obtain ⟨advanced, slotOk, upgrades⟩ := bind_ok_iff.mp ok
  have rest := processUpgrades_induction
    (property := fun post => SlashedKept advanced post.state)
    (fun before ok => before.trans (upgradeNext ok)) (refl advanced) upgrades
  exact (advanceSlot slotOk).trans rest

end SlashedKept

private theorem key_of_same_size {fork : Fork} {state after : BeaconState preset fork}
    (kept : validatorKeys state <+: validatorKeys after)
    (size : after.validators.data.size = state.validators.data.size)
    {i : Nat} {v : Validator} (found : after.validators.data[i]? = some v) :
    ∃ old, state.validators.data[i]? = some old ∧ old.pubkey = v.pubkey := by
  -- The registry has the same size, so the position was filled before, with the same key.
  have before : i < state.validators.data.size :=
    size ▸ (Array.getElem?_eq_some_iff.mp found).1
  have atOld : state.validators.data[i]? = some state.validators.data[i] := by simp [before]
  obtain ⟨current, foundCurrent, same⟩ := validators_getElem?_of_validatorKeys_prefix kept atOld
  obtain rfl : current = v := Option.some.inj (foundCurrent.symm.trans found)
  exact ⟨_, atOld, same.symm⟩

private theorem slashValidator_backed {fork : Fork} {state after : BeaconState preset fork}
    {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config state index whistleblower = .ok after)
    (evidence : BLSPubkey → Prop) (backed : SlashedBacked evidence state)
    (selected : ∀ old, state.validators.data[index.toNat]? = some old → evidence old.pubkey) :
    SlashedBacked evidence after := by
  obtain ⟨exited, validator, withdrawable, marked, _, _, slashings, lowered, _, _, raised, last,
    exitedOk, found, _, markedOk, _, _, _, loweredOk, _, _, raisedOk, lastOk, done⟩ :=
    slashValidator_ok ok
  have oldBacked := SlashedKept.initiateValidatorExit exitedOk evidence backed
  -- Only the selected validator can acquire a flag at this write.
  have markedBacked : SlashedBacked evidence marked := by
    obtain ⟨inside, rfl⟩ := setValidator_ok markedOk
    intro v member flag
    simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Array.toList_set] at member
    rcases List.mem_or_eq_of_mem_set member with member | rfl
    · exact oldBacked v member flag
    · obtain ⟨old, atOld, same⟩ := key_of_same_size
        (frame_initiateValidatorExit exitedOk).pubkeysPrefix
        (sameSizes_initiateValidatorExit exitedOk).1 (getValidator_eq_ok_iff.mp found)
      exact same ▸ selected old atOld
  have rest : SlashedKept marked last :=
    (SlashedKept.of_validators (after := { marked with slashings })).trans <|
    (SlashedKept.decreaseBalance loweredOk).trans <|
    (SlashedKept.increaseBalance raisedOk).trans (SlashedKept.increaseBalance lastOk)
  have lastBacked := rest evidence markedBacked
  rw [done]
  split <;> exact lastBacked

private theorem proposerSlashing_backed {fork : Fork} {state after : BeaconState preset fork}
    {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks state slashing = .ok after)
    (evidence : BLSPubkey → Prop) (backed : SlashedBacked evidence state)
    (selected : ∀ old,
      state.validators.data[slashing.signedHeader1.message.proposerIndex.toNat]? = some old →
        evidence old.pubkey) : SlashedBacked evidence after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact slashValidator_backed slashed evidence backed selected

private theorem attesterSlashing_backed {fork : Fork} {state after : BeaconState preset fork}
    {slashing : AttesterSlashing preset fork}
    (ok : processAttesterSlashing config checks state slashing = .ok after)
    (evidence : BLSPubkey → Prop) (backed : SlashedBacked evidence state)
    (selected : ∀ i ∈ slashingIndices slashing, ∀ old,
      state.validators.data[i.toNat]? = some old → evidence old.pubkey) :
    SlashedBacked evidence after := by
  have traverse (indices : List ValidatorIndex)
      (allowed : ∀ i ∈ indices, ∀ old,
        state.validators.data[i.toNat]? = some old → evidence old.pubkey)
      {start finish : BeaconState preset fork × Bool}
      (identity : validatorKeys state <+: validatorKeys start.1)
      (size : start.1.validators.data.size = state.validators.data.size)
      (backed : SlashedBacked evidence start.1)
      (ok : indices.foldlM (slashIfSlashable config) start = .ok finish) :
      SlashedBacked evidence finish.1 := by
    induction indices generalizing start with
    | nil => cases ok; exact backed
    | cons index rest ih =>
      obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ok
      obtain ⟨s, anySlashed⟩ := start
      simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at first
      obtain ⟨_, _, first⟩ := first
      split at first
      · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at first
        obtain ⟨next, slashed, rfl⟩ := first
        refine ih (fun i member => allowed i (by simp [member]))
          (identity.trans (frame_slashValidator slashed).pubkeysPrefix)
          ((sameSizes_slashValidator slashed).1.trans size) ?_ tail
        apply slashValidator_backed slashed evidence backed
        intro old found
        obtain ⟨original, originalAt, same⟩ := key_of_same_size identity size found
        exact same ▸ allowed index (by simp) original originalAt
      · cases first
        exact ih (fun i member => allowed i (by simp [member])) identity size backed tail
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  exact traverse _ selected (List.prefix_refl _) rfl backed folded

private theorem fold_slashings_backed {fork : Fork} {α : Type}
    {step : BeaconState preset fork → α → Except TransitionError (BeaconState preset fork)}
    (indices : α → List ValidatorIndex)
    (identityStep : ∀ s x t, step s x = .ok t → validatorKeys s <+: validatorKeys t)
    (sizeStep : ∀ s x t, step s x = .ok t → SameSizes s t)
    (backedStep : ∀ s x t, step s x = .ok t → ∀ evidence,
      SlashedBacked evidence s →
      (∀ i ∈ indices x, ∀ old, s.validators.data[i.toNat]? = some old → evidence old.pubkey) →
      SlashedBacked evidence t)
    {state start finish : BeaconState preset fork} (items : List α)
    (identity : validatorKeys state <+: validatorKeys start)
    (size : start.validators.data.size = state.validators.data.size)
    (evidence : BLSPubkey → Prop) (backed : SlashedBacked evidence start)
    (selected : ∀ x ∈ items, ∀ i ∈ indices x, ∀ old,
      state.validators.data[i.toNat]? = some old → evidence old.pubkey)
    (ok : items.foldlM step start = .ok finish) : SlashedBacked evidence finish := by
  induction items generalizing start with
  | nil => cases ok; exact backed
  | cons item rest ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ok
    refine ih (identity.trans (identityStep _ _ _ first))
      ((sizeStep _ _ _ first).1.trans size) ?_
      (fun x member => selected x (by simp [member])) tail
    apply backedStep _ _ _ first evidence backed
    intro i member old found
    -- Earlier slashings preserve the index and key used by the block's original evidence.
    obtain ⟨original, originalAt, same⟩ := key_of_same_size identity size found
    exact same ▸ selected item (by simp) i member original originalAt

private theorem operations_backed {fork : Fork} {state after : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (ok : processOperations config checks state body parentSlot = .ok after)
    (evidence : BLSPubkey → Prop) (backed : SlashedBacked evidence state)
    (proposers : ∀ sl ∈ body.proposerSlashings.data.toList, ∀ old,
      state.validators.data[sl.signedHeader1.message.proposerIndex.toNat]? = some old →
        evidence old.pubkey)
    (attesters : ∀ sl ∈ body.attesterSlashings.data.toList, ∀ i ∈ slashingIndices sl, ∀ old,
      state.validators.data[i.toNat]? = some old → evidence old.pubkey) :
    SlashedBacked evidence after := by
  -- The operations after the attestations keep the slashed flags.
  obtain ⟨proposed, slashed, attested, proposersOk, attestersOk, attestations, tail⟩ :=
    processOperations_folds_of (fun s t => SlashedKept s t) SlashedKept.refl
      (fun one two => one.trans two) SlashedKept.processDeposit
      SlashedKept.processVoluntaryExit SlashedKept.processBlsToExecutionChange
      SlashedKept.processExecutionRequests
      (fun ok => by rw [processPayloadAttestation_eq ok]; exact SlashedKept.of_validators) ok
  have proposedBacked : SlashedBacked evidence proposed := by
    refine fold_slashings_backed (fun sl => [sl.signedHeader1.message.proposerIndex])
      (fun _ _ _ ok => (frame_processProposerSlashing ok).pubkeysPrefix)
      (fun _ _ _ ok => sameSizes_processProposerSlashing ok) ?_ _ (List.prefix_refl _) rfl
      evidence backed ?_ proposersOk
    · intro s sl t ok evidence backed selected
      exact proposerSlashing_backed ok evidence backed (selected _ (by simp))
    · intro sl member i inIndices
      simp only [List.mem_singleton] at inIndices
      subst i
      exact proposers sl member
  have proposedSize : SameSizes state proposed :=
    (foldlM_ok_steps SameSizes SameSizes.refl SameSizes.trans
      (fun _ _ _ ok => sameSizes_processProposerSlashing ok) proposersOk).1
  have slashedBacked := fold_slashings_backed slashingIndices
    (fun _ _ _ ok => (frame_processAttesterSlashing ok).pubkeysPrefix)
    (fun _ _ _ ok => sameSizes_processAttesterSlashing ok)
    (fun _ _ _ ok => attesterSlashing_backed ok) _
    (BlockFrame.foldlM (fun _ _ _ ok => frame_processProposerSlashing ok) proposersOk).pubkeysPrefix
    proposedSize.1 evidence proposedBacked attesters attestersOk
  -- Attestations keep the registry.
  have attestedKept : SlashedKept slashed attested := SlashedKept.foldlM
    (fun _ _ _ ok => SlashedKept.of_validators (by rw [(processAttestation_registry ok).1]))
    attestations
  exact (attestedKept.trans tail) evidence slashedBacked

/-- The payload of the parent keeps the size of the registry.

Its requests queue deposits and act on the builders, so no validator joins. -/
private theorem size_processParentExecutionPayload {fork : Fork}
    {state after : BeaconState preset fork} {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (ok : processParentExecutionPayload config checks state gloas body = .ok after) :
    after.validators.data.size = state.validators.data.size := by
  rcases processParentExecutionPayload_ok ok with ⟨_, _, rfl⟩ |
    ⟨_, settled, _, _, _, _, _, _, settledOk, depositsOk, withdrawalsOk,
      consolidationsOk, buildersOk, exitsOk, _, rfl⟩
  · rfl
  have foldSize {α : Type} {step : BeaconState preset fork → α → Except TransitionError _}
      (keeps : ∀ s x t, step s x = .ok t → t.validators.data.size = s.validators.data.size)
      {xs : List α} {s t : BeaconState preset fork} (ok : xs.foldlM step s = .ok t) :
      t.validators.data.size = s.validators.data.size :=
    foldlM_ok_invariant (fun t => t.validators.data.size = s.validators.data.size)
      (fun _ _ _ before computed => (keeps _ _ _ computed).trans before) rfl ok
  have depositSize := foldSize (fun _ _ _ ok =>
    congrArg (fun vs => vs.data.size) (processDepositRequest_ok ok).2.1) depositsOk
  have withdrawalSize := foldSize (fun _ _ _ ok =>
    (sameSizes_processWithdrawalRequest ok).1) withdrawalsOk
  have consolidationSize := foldSize (fun _ _ _ ok =>
    (sameSizes_processConsolidationRequest ok).1) consolidationsOk
  have builderSize := foldSize (fun _ _ _ ok => by
    unfold processBuilderDepositRequest addBuilderToRegistry at ok
    simp only [bind, Except.bind, pure, Except.pure] at ok
    repeat' split at ok
    all_goals first | (cases ok; done) | (cases ok; rfl)) buildersOk
  have exitSize := foldSize (fun _ _ _ ok => by
    rcases processBuilderExitRequest_cases ok with rfl | ⟨_, _, _, _, _, exited⟩
    · rfl
    · simp only [initiateBuilderExit, bind_ok_iff] at exited
      obtain ⟨_, _, _, _, set⟩ := exited
      obtain ⟨_, rfl⟩ := setBuilder_ok set
      rfl) exitsOk
  exact exitSize.trans <| builderSize.trans <| consolidationSize.trans <|
    withdrawalSize.trans <| depositSize.trans (by rw [settleParentPayment_eq settledOk])

/-- The execution part of a block keeps the slashed flags and the size of the registry. -/
private theorem slashedKept_processBlockExecution {fork : Fork}
    {state after : BeaconState preset fork} {engine : ExecutionEngine preset fork}
    {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork}
    (ok : processBlockExecution config checks engine state body bellatrix = .ok after) :
    SlashedKept state after ∧ after.validators.data.size = state.validators.data.size := by
  have payload {s t : BeaconState preset fork}
      {execution : .bellatrix ≤ fork ∧ fork < .glamsterdam}
      (ok : processExecutionPayload config engine s body execution = .ok t) :
      SlashedKept s t ∧ t.validators.data = s.validators.data := by
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
    exact ⟨SlashedKept.of_validators, rfl⟩
  unfold processBlockExecution at ok
  split at ok
  · obtain ⟨middle, withdrawn, executed⟩ := bind_ok_iff.mp ok
    have size : after.validators.data.size = middle.validators.data.size := by
      obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok executed
      by_cases paid : 0 < (body.signedExecutionPayloadBid (by assumption)).message.value
      · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
        rfl
      · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure,
          Except.ok.injEq] at recordedOk
        subst recordedOk
        rfl
    exact ⟨(SlashedKept.processWithdrawals withdrawn).trans
      (SlashedKept.executionPayloadBid executed),
      size.trans (sameSizes_processWithdrawals withdrawn).1⟩
  split at ok
  · obtain ⟨middle, withdrawn, executed⟩ := bind_ok_iff.mp ok
    exact ⟨(SlashedKept.processWithdrawals withdrawn).trans (payload executed).1,
      (congrArg Array.size (payload executed).2).trans (sameSizes_processWithdrawals withdrawn).1⟩
  · dsimp only at ok
    split at ok
    · exact ⟨(payload ok).1, congrArg Array.size (payload ok).2⟩
    · cases ok; exact ⟨.refl _, rfl⟩

/-- The steps of a block before its operations keep the slashed flags and the size of the registry.

The keys of the registry are a prefix, by the block frame of the same steps. -/
private theorem slashedKept_operationsInput {fork : Fork}
    {state input : BeaconState preset fork} {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork}
    (started : OperationsInput config checks engine state block input) :
    SlashedKept state input ∧ input.validators.data.size = state.validators.data.size :=
  started.step_of
    (fun s t => SlashedKept s t ∧ t.validators.data.size = s.validators.data.size)
    (fun _ => ⟨.refl _, rfl⟩) (fun one two => ⟨one.1.trans two.1, two.2.trans one.2⟩)
    (fun _ ok => ⟨SlashedKept.parentPayload ok, size_processParentExecutionPayload ok⟩)
    (fun ok => by
      refine ⟨?_, (sameSizes_processBlockHeader ok).1⟩
      obtain ⟨_, _, rfl⟩ := processBlockHeader_eq ok
      exact SlashedKept.of_validators)
    (fun _ ok => slashedKept_processBlockExecution ok)
    (fun ok => by
      refine ⟨?_, (sameSizes_processRandao ok).1⟩
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq ok
      exact SlashedKept.of_validators)
    (fun _ ok => by
      refine ⟨?_, (sameSizes_processEth1Data ok).1⟩
      obtain ⟨_, _, rest⟩ := processEth1Data_eq ok
      rw [← rest]
      exact SlashedKept.of_validators)

private theorem block_backed {fork : Fork} {state after : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    (ok : processBlock config checks engine state block = .ok after)
    (evidence : BLSPubkey → Prop) (backed : SlashedBacked evidence state)
    (proposers : ∀ sl ∈ block.body.proposerSlashings.data.toList, ∀ old,
      state.validators.data[sl.signedHeader1.message.proposerIndex.toNat]? = some old →
        evidence old.pubkey)
    (attesters : ∀ sl ∈ block.body.attesterSlashings.data.toList,
      ∀ i ∈ slashingIndices sl, ∀ old,
      state.validators.data[i.toNat]? = some old → evidence old.pubkey) :
    SlashedBacked evidence after := by
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput ok
  -- The evidence of the block names validators before it, and they keep their keys to its input.
  have kept := (frame_operationsInput started).pubkeysPrefix
  obtain ⟨slashedKept, size⟩ := slashedKept_operationsInput started
  have operatedBacked : SlashedBacked evidence last := by
    apply operations_backed operated evidence (slashedKept evidence backed)
    · intro sl member old found
      obtain ⟨original, originalAt, same⟩ := key_of_same_size kept size found
      exact same ▸ proposers sl member original originalAt
    · intro sl member i inIndices old found
      obtain ⟨original, originalAt, same⟩ := key_of_same_size kept size found
      exact same ▸ attesters sl member i inIndices original originalAt
  -- From Altair the sync aggregate follows, and it keeps the slashed flags.
  split at synced
  · exact SlashedKept.processSyncAggregate synced evidence operatedBacked
  · cases synced
    exact operatedBacked

/-- A slashed validator of the last state has a slashing in a block of the run that names its key.

The key is read in the registry before that block.

The run starts at a genesis built from deposits. -/
theorem _root_.EthLib.Consensus.Run.slashed_evidence {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (genesis : Genesis (config := config) (checks := checks) g)
    (v : Validator) (member : v ∈ a.state.validators.data.toList) (slashed : v.slashed = true) :
    run.SlashingEvidence v.pubkey := by
  have backed : SlashedBacked run.SlashingEvidence a.state := by
    clear member slashed v
    induction run with
    | nil =>
      obtain ⟨_, _, _, ok⟩ := genesis
      intro current member flag
      exact False.elim (SlashedKept.genesis ok current member flag)
    | snoc pre step ih =>
      rename_i middle last
      have inherited : SlashedBacked (pre.snoc step).SlashingEvidence middle.state := by
        intro current member flag
        obtain ⟨x, y, occurrence, contained, evidence⟩ := ih current member flag
        exact ⟨x, y, occurrence, .earlier contained step, evidence⟩
      cases step with
      | slot ok => exact SlashedKept.advanceSlotAcross ok _ inherited
      | block engine signed due ok =>
        apply block_backed (applySignedBlock_ok ok).2.1 _ inherited
        · intro sl member old found
          exact ⟨_, _, .block engine signed due ok, .last pre _,
            Or.inl ⟨sl, member, old, found, rfl⟩⟩
        · intro sl member i inIndices old found
          exact ⟨_, _, .block engine signed due ok, .last pre _,
            Or.inr ⟨sl, member, i, inIndices, old, found, rfl⟩⟩
  exact backed v member slashed

/-- A block of the run that applied an attester slashing checked both of its attestations.

Both checks accepted, and the data of the two attestations are slashable.

Take an index of the slashing and its validator in the registry before the block.

Each attestation then has an index that holds the key of that validator at the state of the check.
-/
theorem _root_.EthLib.Consensus.Run.attestationChecks_of_attesterSlashing
    {g a : ForkedBeaconState preset}
    {run : Run config checks g a} {fork : Fork} {before after : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    {due : upgradeDue config ⟨fork, before⟩ = false}
    {applied : applySignedBlock config checks engine before signed true = .ok after}
    (member : run.Contains (.block engine signed due applied))
    {slashing : AttesterSlashing preset fork}
    (included : slashing ∈ signed.message.body.attesterSlashings.data.toList)
    {i : ValidatorIndex} (named : i ∈ slashingIndices slashing) {v : Validator}
    (found : before.validators.data[i.toNat]? = some v) :
    ∃ one two : AttestationCheck run v.pubkey,
      one.indexed.data = slashing.attestation1.data ∧
      two.indexed.data = slashing.attestation2.data ∧
      isSlashableAttestationData slashing.attestation1.data slashing.attestation2.data =
        true := by
  obtain ⟨_, processed, _⟩ := applySignedBlock_ok applied
  obtain ⟨input, _, _, _, started, proposers, slashings, -⟩ := processBlock_folds processed
  -- The slashing sits at a position of the attester slashings of the block.
  obtain ⟨pre, post, checked, next, split, earlier, processedS⟩ :=
    foldlM_ok_of_mem included slashings
  have site (indexed : IndexedAttestation preset fork)
      (which : indexed = slashing.attestation1 ∨ indexed = slashing.attestation2) :
      AttestationSite config checks input signed.message.body before.latestBlockHeader.slot
        checked indexed :=
    .slashing split proposers earlier processedS which
  -- The validator at the index keeps its key from the state before the block to the check.
  obtain ⟨current, foundCurrent, currentKey⟩ :=
    validators_getElem?_of_validatorKeys_prefix
      ((frame_operationsInput started).toFrame.trans
        (site _ (.inl rfl)).frame).pubkeysPrefix found
  -- The index is in both attestations, because the slashed indices are those in both.
  unfold slashingIndices at named
  obtain ⟨first, second⟩ := List.mem_filter.mp (mem_sortedSet.mp named)
  have inSecond := of_decide_eq_true second
  -- Both attestations are checked at the state where the slashing runs.
  obtain ⟨conflict, oneOk, twoOk⟩ := processAttesterSlashing_checks processedS
  exact ⟨⟨⟨fork, before, after, engine, signed, due, applied, member, input, started⟩, checked,
      slashing.attestation1, site _ (.inl rfl),
      ⟨i, first, current, foundCurrent, currentKey⟩, oneOk⟩,
    ⟨⟨fork, before, after, engine, signed, due, applied, member, input, started⟩, checked,
      slashing.attestation2, site _ (.inr rfl),
      ⟨i, inSecond, current, foundCurrent, currentKey⟩, twoOk⟩, rfl, rfl, conflict⟩

/-- A block of the run that applied a proposer slashing checked both of its headers.

The checks are for the key of the proposer in the registry before the block, and accepted.

The two headers conflict. -/
theorem _root_.EthLib.Consensus.Run.headerCheck_of_proposerSlashing
    {g a : ForkedBeaconState preset}
    {run : Run config checks g a} {fork : Fork} {before after : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    {due : upgradeDue config ⟨fork, before⟩ = false}
    {applied : applySignedBlock config checks engine before signed true = .ok after}
    (member : run.Contains (.block engine signed due applied))
    {slashing : ProposerSlashing}
    (included : slashing ∈ signed.message.body.proposerSlashings.data.toList) {v : Validator}
    (found : before.validators.data[slashing.signedHeader1.message.proposerIndex.toNat]? =
      some v) :
    ∃ c : HeaderCheck run v.pubkey, c.slashing = slashing ∧ ProposerConflict slashing := by
  obtain ⟨_, processed, _⟩ := applySignedBlock_ok applied
  obtain ⟨input, _, _, _, started, proposers, -⟩ := processBlock_folds processed
  -- The slashing sits at a position of the proposer slashings of the block.
  obtain ⟨pre, post, checked, next, split, earlier, processedP⟩ :=
    foldlM_ok_of_mem included proposers
  have frame : Frame before checked :=
    (frame_operationsInput started).toFrame.trans
      (BlockFrame.foldlM (fun _ _ _ ok => frame_processProposerSlashing ok) earlier).toFrame
  obtain ⟨current, foundCurrent, currentKey⟩ :=
    validators_getElem?_of_validatorKeys_prefix frame.pubkeysPrefix found
  obtain ⟨slotEq, indexEq, differ, proposer, proposerOk, -, oneOk, twoOk⟩ :=
    processProposerSlashing_checks processedP
  -- The validator that the check reads is the one that the key reaches.
  have same : proposer = current := Option.some.inj
    ((getValidator_eq_ok_iff.mp proposerOk).symm.trans foundCurrent)
  have key : proposer.pubkey = v.pubkey := same ▸ currentKey
  rw [key] at oneOk twoOk
  exact ⟨⟨⟨fork, before, after, engine, signed, due, applied, member, input, started⟩, pre, post,
    slashing, checked, next, split, earlier, processedP, ⟨current, foundCurrent, currentKey⟩,
    oneOk, twoOk⟩, rfl, slotEq, indexEq, differ⟩

end EthLib.Consensus.DirectSafety
