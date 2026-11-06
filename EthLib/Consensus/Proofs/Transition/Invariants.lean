module

public import EthLib.Consensus.Proofs.Transition.EpochJustification
public import EthLib.Consensus.Proofs.Transition.EpochRewards
public import EthLib.Consensus.Proofs.Transition.EpochUpdates
public import EthLib.Consensus.Proofs.Transition.Execution
public import EthLib.Consensus.Proofs.Transition.Operations
public import EthLib.Consensus.Proofs.Transition.Payload
public import EthLib.Consensus.Proofs.Transition.Requests
public import EthLib.Consensus.Proofs.Transition.StateTransition

/-!
# Proofs: invariants of the state transition

A valid block keeps four properties of a state, at every fork.

The registry and the balances keep one entry for each validator.

Each validator may withdraw no earlier than it exits.

The finalized, previous justified and current justified epochs stay in increasing order.

The current justified epoch is at most the previous epoch.

So the next epoch transition cannot lower the finalized epoch.

The finalized epoch then never decreases.

Most steps change neither the slot nor the checkpoints, and keep the first two properties.

Justification and finalization change the checkpoints, and the slot step moves the epoch on.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork}
  {state after : BeaconState preset fork}

/-- Each validator may withdraw no earlier than it exits. -/
def ExitsOrdered (state : BeaconState preset fork) : Prop :=
  ∀ validator ∈ state.validators.data, validator.exitEpoch ≤ validator.withdrawableEpoch

/-- A step that keeps the slot and the three checkpoints.

When they hold before it, it also keeps one balance for each validator.

It then also keeps each exit no later than its withdrawal. -/
structure Frame (state after : BeaconState preset fork) : Prop where
  slot : after.slot = state.slot
  finalized : after.finalizedCheckpoint = state.finalizedCheckpoint
  previousJustified : after.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint
  currentJustified : after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint
  balancesMatch : BalancesMatch state → BalancesMatch after
  exitsOrdered : ExitsOrdered state → ExitsOrdered after

theorem Frame.refl (state : BeaconState preset fork) : Frame state state :=
  ⟨rfl, rfl, rfl, rfl, id, id⟩

theorem Frame.trans {first second third : BeaconState preset fork} (one : Frame first second)
    (two : Frame second third) : Frame first third :=
  ⟨two.slot.trans one.slot, two.finalized.trans one.finalized,
    two.previousJustified.trans one.previousJustified,
    two.currentJustified.trans one.currentJustified, two.balancesMatch ∘ one.balancesMatch,
    two.exitsOrdered ∘ one.exitsOrdered⟩

/-- A step that keeps the slot, the checkpoints and the registry, and the number of balances. -/
theorem Frame.of_validators (sizes : SameSizes state after)
    (validators : after.validators = state.validators) (slot : after.slot = state.slot)
    (finalized : after.finalizedCheckpoint = state.finalizedCheckpoint)
    (previousJustified : after.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint)
    (currentJustified : after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint) :
    Frame state after :=
  ⟨slot, finalized, previousJustified, currentJustified, balancesMatch_of_sameSizes sizes,
    fun ordered => by rw [ExitsOrdered, validators]; exact ordered⟩

/-- A fold whose every step is a frame is a frame. -/
theorem Frame.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (frame : ∀ s x s', step s x = .ok s' → Frame s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : Frame state after :=
  foldlM_ok_invariant (Frame state) (fun _ _ _ before ok => before.trans (frame _ _ _ ok))
    (Frame.refl state) computed

/-! ## Mutators -/

theorem mem_of_getValidator {index : ValidatorIndex} {validator : Validator}
    (found : getValidator state index = .ok validator) : validator ∈ state.validators.data := by
  unfold getValidator at found
  split at found
  · rename_i read
    cases found
    exact Array.mem_of_getElem? read
  · cases found

/-- Replacing a validator by one that exits no later than it may withdraw keeps the order. -/
theorem ExitsOrdered.putValidator {index : Nat} {validator : Validator}
    (inside : index < state.validators.data.size)
    (ordered : ExitsOrdered state) (le : validator.exitEpoch ≤ validator.withdrawableEpoch) :
    ExitsOrdered (state.putValidator index inside validator) := by
  intro other member
  simp only [BeaconState.putValidator, RootedForkList.data_set] at member
  rcases Array.mem_or_eq_of_mem_set (w := inside) member with old | rfl
  · exact ordered other old
  · exact le

theorem frame_setValidator {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after)
    (le : ExitsOrdered state → validator.exitEpoch ≤ validator.withdrawableEpoch) :
    Frame state after := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  exact ⟨rfl, rfl, rfl, rfl, balancesMatch_of_sameSizes (sameSizes_putValidator state inside _),
    fun ordered => ordered.putValidator inside (le ordered)⟩

theorem frame_increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : Frame state after := by
  obtain ⟨_, set⟩ := increaseBalance_ok computed
  have sizes := sameSizes_setBalance set
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact Frame.of_validators sizes rfl rfl rfl rfl rfl

theorem frame_decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : Frame state after := by
  obtain ⟨_, set⟩ := decreaseBalance_ok computed
  have sizes := sameSizes_setBalance set
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact Frame.of_validators sizes rfl rfl rfl rfl rfl

theorem frame_exitQueue {exitBalance : Gwei} {exitEpoch : Epoch}
    (computed : exitQueue config state exitBalance = .ok (after, exitEpoch)) :
    Frame state after := by
  obtain ⟨validators, balances⟩ := exitQueue_validators computed
  unfold exitQueue at computed
  have sizes : SameSizes state after := ⟨by rw [validators], by rw [balances]⟩
  split at computed
  · simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := computed
    exact Frame.of_validators sizes validators rfl rfl rfl rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, rfl, _⟩ := computed
    exact Frame.refl _

/-- Starting an exit sets a withdrawable epoch no earlier than the exit epoch. -/
theorem frame_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) : Frame state after := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, queued, exitEpoch, withdrawableEpoch, queue, summed, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact Frame.refl _
  · refine (frame_exitQueue queue).trans (frame_setValidator set fun _ => ?_)
    have sum := (addChecked_ok_iff.mp summed).2
    exact UInt64.le_iff_toNat_le.mpr (by simp only at sum ⊢; omega)

theorem frame_slashings (state : BeaconState preset fork) (slashings : RootedVector Gwei _) :
    Frame state { state with slashings } :=
  Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl

/-- The last step of a slashing, which from Gloas cancels builder payments, keeps the frame. -/
theorem frame_slashValidatorLast {last : BeaconState preset fork} {index : ValidatorIndex}
    (done : (pure (if gloas : .glamsterdam ≤ fork then cancelProposerPayments last gloas index
      else last) : Except AccessorError (BeaconState preset fork)) = .ok after) :
    Frame last after := by
  simp only [pure, Except.pure, Except.ok.injEq] at done
  subst done
  split
  · exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl
  · exact Frame.refl _

/-- Slashing a validator only delays its withdrawal. -/
theorem frame_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    Frame state after := by
  simp only [slashValidator, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨exited, exitedOk, validator, found, delay, _, marked, markedOk, _, _, _, _, _, _,
    lowered, loweredOk,
    proposer, _, _, _, raised, raisedOk, last, lastOk, done⟩ := computed
  refine (frame_initiateValidatorExit exitedOk).trans <|
    ((frame_setValidator markedOk
      fun ordered => ?_).trans
      (frame_slashings _ _)).trans <|
    (frame_decreaseBalance loweredOk).trans <| (frame_increaseBalance raisedOk).trans <|
    (frame_increaseBalance lastOk).trans (frame_slashValidatorLast done)
  refine UInt64.le_trans (ordered validator (mem_of_getValidator found)) ?_
  rw [UInt64.max_def]
  split
  · assumption
  · exact UInt64.le_refl _

/-! ## The steps of a block -/

theorem frame_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) : Frame state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl

theorem frame_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) : Frame state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl

theorem frame_processEth1Data {before : fork < .hegota} {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) : Frame state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  exact Frame.of_validators (sameSizes_processEth1Data computed) (by rw [← rest])
    (by rw [← rest]) (by rw [← rest]) (by rw [← rest]) (by rw [← rest])

theorem frame_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    Frame state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact frame_slashValidator slashed

theorem frame_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    Frame step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact frame_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Frame.refl _

theorem frame_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    Frame state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant (fun step => Frame state step.1)
    (fun _ _ _ before ok => before.trans (frame_slashIfSlashable ok))
    (show Frame state (state, false).1 from Frame.refl state) folded

theorem frame_setEpochParticipation (current : Bool)
    (participation : EpochParticipation preset fork) :
    Frame state (setEpochParticipation state current participation) := by
  unfold setEpochParticipation
  split <;> exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl

/-- From Altair, an attestation sets flags, pays the proposer, and from Gloas weighs a payment. -/
theorem frame_processAttestationAltair {attestation : Attestation preset fork}
    {altair : .altair ≤ fork} {parentSlot : Slot}
    (computed :
      processAttestationAltair config checks state attestation altair parentSlot = .ok after) :
    Frame state after := by
  unfold processAttestationAltair at computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, raised, raisedOk, final⟩ := computed
  have last : Frame raised after := by
    split at final
    · rw [recordPaymentWeight_eq final]
      exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl
    · cases final
      exact Frame.refl _
  exact (frame_setEpochParticipation _ _).trans ((frame_increaseBalance raisedOk).trans last)

theorem frame_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    Frame state after := by
  unfold processAttestation at computed
  split at computed
  · exact frame_processAttestationAltair computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
  have kept := recordPendingAttestation_ok recorded
  split at kept
  · obtain ⟨_, rest⟩ := kept
    exact Frame.of_validators (by rw [← rest]; exact ⟨rfl, rfl⟩) (by rw [← rest])
      (by rw [← rest]) (by rw [← rest]) (by rw [← rest]) (by rw [← rest])
  · obtain ⟨_, rest⟩ := kept
    exact Frame.of_validators (by rw [← rest]; exact ⟨rfl, rfl⟩) (by rw [← rest])
      (by rw [← rest]) (by rw [← rest]) (by rw [← rest]) (by rw [← rest])

/-- A new validator exits and withdraws at the far future epoch. -/
theorem frame_addValidatorToRegistry {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    Frame state after := by
  have balances := balancesMatch_addValidatorToRegistry computed
  have exits : ExitsOrdered state → ExitsOrdered after := fun ordered validator member => by
    obtain ⟨_, found⟩ := Array.getElem?_of_mem member
    rcases addValidatorToRegistry_validator computed found with old | rfl
    · exact ordered validator (Array.mem_of_getElem? old)
    · exact UInt64.le_refl _
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
    exact ⟨rfl, rfl, rfl, rfl, balances, exits⟩
  split at computed
  · cases computed
    exact ⟨rfl, rfl, rfl, rfl, balances, exits⟩
  · cases computed

theorem frame_applyDepositElectra {electra : .pectra ≤ fork} {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei} {signature : BLSSignature}
    (computed : applyDepositElectra config checks state electra pubkey withdrawalCredentials
      amount signature = .ok after) :
    Frame state after := by
  unfold applyDepositElectra at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, added, pushed⟩ := computed
      obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
      exact (frame_addValidatorToRegistry added).trans
        (Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl)
    · cases computed
      exact Frame.refl _
  · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
    exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl

theorem frame_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    Frame state after := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact Frame.refl _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact frame_addValidatorToRegistry computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ Frame.refl _
  · rw [liftAccessor_ok] at computed
    exact frame_increaseBalance computed

theorem frame_applyDeposit {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    Frame state after := by
  unfold applyDeposit at computed
  split at computed
  · exact frame_applyDepositElectra computed
  · exact frame_applyPendingDeposit computed

theorem frame_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    Frame state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact (Frame.of_validators (state := state)
    (after := { state with eth1DepositIndex := fun _ => next })
    ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl).trans (frame_applyDeposit applied)

theorem frame_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    Frame state after := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact frame_initiateValidatorExit exited

/-! ## Requests of the execution layer -/

theorem frame_processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) : Frame state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl

theorem frame_computeExitEpochAndUpdateChurn {electra : .pectra ≤ fork} {exitBalance : Gwei}
    {epoch : Epoch}
    (computed :
      computeExitEpochAndUpdateChurn config state electra exitBalance = .ok (after, epoch)) :
    Frame state after := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl

theorem frame_computeConsolidationEpochAndUpdateChurn {electra : .pectra ≤ fork} {balance : Gwei}
    {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (after, epoch)) :
    Frame state after := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl

theorem frame_requestPartialWithdrawal {electra : .pectra ≤ fork} {index : ValidatorIndex}
    {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    Frame state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    exact (frame_computeExitEpochAndUpdateChurn churned).trans
      (Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl)
  · cases computed
    exact Frame.refl _

theorem frame_processWithdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    Frame state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact Frame.refl _)
    | exact frame_initiateValidatorExit (liftAccessor_ok.mp computed)
    | exact frame_requestPartialWithdrawal computed

theorem frame_queueExcessActiveBalance {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queueExcessActiveBalance state electra index = .ok after) : Frame state after := by
  have sizes := sameSizes_queueExcessActiveBalance computed
  simp only [queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, set, rfl⟩ := computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact Frame.of_validators sizes rfl rfl rfl rfl rfl
  · cases computed
    exact Frame.refl _

/-- Compounding credentials keep the epochs, and the excess balance moves to the deposit queue. -/
theorem frame_switchToCompoundingValidator {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    Frame state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨validator, found, _, set, queued⟩ := computed
  exact (frame_setValidator set fun ordered => ordered validator (mem_of_getValidator found)).trans
    (frame_queueExcessActiveBalance queued)

/-- The source of a consolidation exits, and may withdraw a checked delay later. -/
theorem frame_queueConsolidation {electra : .pectra ≤ fork} {sourcePosition : Nat}
    {source : Validator} {targetIndex : ValidatorIndex}
    (computed :
      queueConsolidation config state electra sourcePosition source targetIndex = .ok after) :
    Frame state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure] at computed
  obtain ⟨⟨churnedState, exitEpoch⟩, churned, withdrawable, ⟨_, sum⟩, _, set, _, _, computed⟩ :=
    computed
  simp only [Except.ok.injEq] at computed
  subst computed
  have le : exitEpoch ≤ withdrawable :=
    UInt64.le_iff_toNat_le.mpr (by simp only at sum ⊢; omega)
  exact (frame_computeConsolidationEpochAndUpdateChurn churned).trans <|
    (frame_setValidator set fun _ => le).trans (Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl)

theorem frame_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    Frame state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact Frame.refl _)
    | exact frame_switchToCompoundingValidator (liftAccessor_ok.mp computed)
    | exact frame_queueConsolidation computed

theorem frame_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    Frame state after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  exact (Frame.foldlM (fun _ _ _ ok => frame_processDepositRequest ok) depositsOk).trans <|
    (Frame.foldlM (fun _ _ _ ok => frame_processWithdrawalRequest ok) withdrawalsOk).trans <|
    Frame.foldlM (fun _ _ _ ok => frame_processConsolidationRequest ok) consolidationsOk

/-! ## Withdrawals -/

theorem frame_applyWithdrawal {withdrawal : Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) : Frame state after := by
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, set⟩ := computed
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl
  · exact frame_decreaseBalance computed

theorem frame_updateNextWithdrawalIndex {withdrawals : Array Withdrawal}
    (computed : updateNextWithdrawalIndex state withdrawals = .ok after) : Frame state after := by
  unfold updateNextWithdrawalIndex at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl
  · cases computed
    exact Frame.refl _

theorem frame_updateNextWithdrawalValidatorIndex {capella : .shapella ≤ fork}
    {withdrawals : Array Withdrawal}
    (computed : updateNextWithdrawalValidatorIndex state capella withdrawals = .ok after) :
    Frame state after := by
  unfold updateNextWithdrawalValidatorIndex at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · cases computed
  · cases computed
    exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl

theorem frame_updateNextWithdrawalBuilderIndex {gloas : .glamsterdam ≤ fork} {count : Nat}
    (computed : updateNextWithdrawalBuilderIndex state gloas count = .ok after) :
    Frame state after := by
  unfold updateNextWithdrawalBuilderIndex at computed
  dsimp only at computed
  split at computed
  · cases computed
    exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl

theorem frame_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    Frame state after := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : Frame state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact Frame.foldlM (fun _ _ _ ok => frame_applyWithdrawal ok) appliedOk
  have queued : ∀ kept : BeaconState preset fork,
      Frame kept (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals kept gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else kept) := by
    intro kept
    split <;> exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl
  have partials : ∀ kept : BeaconState preset fork,
      Frame kept (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals kept electra expected.processedPartialWithdrawalsCount
      else kept) := by
    intro kept
    split <;> exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl
  have swept : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → Frame kept finished := by
    intro kept ok
    split at ok
    · exact frame_updateNextWithdrawalBuilderIndex ok
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ Frame.refl _
  exact one.trans <| (frame_updateNextWithdrawalIndex indexedOk).trans <| (queued _).trans <|
    (partials _).trans <| (swept _ sweptOk).trans (frame_updateNextWithdrawalValidatorIndex last)

theorem frame_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) : Frame state after := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, applied⟩ := computed
      exact frame_applyExpectedWithdrawals applied
    · cases computed
      exact Frame.refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact frame_applyExpectedWithdrawals applied

theorem frame_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    Frame state after := by
  obtain ⟨validator, found, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact frame_setValidator set fun ordered => ordered validator (mem_of_getValidator found)

/-! ## The parent payload and the execution part of a block -/

theorem frame_processExecutionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    Frame state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl

theorem frame_processBuilderDepositRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    Frame state after := by
  unfold processBuilderDepositRequest addBuilderToRegistry at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl)

theorem frame_processBuilderExitRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    Frame state after := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · exact Frame.refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl

theorem frame_settleParentPayment {gloas : .glamsterdam ≤ fork}
    (computed : settleParentPayment state gloas = .ok after) : Frame state after := by
  unfold settleParentPayment at computed
  split at computed
  · have settled := liftAccessor_ok.mp computed
    unfold settleBuilderPayment at settled
    split at settled
    · cases settled
      exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl
    · cases settled
  · simp only at computed
    split at computed <;> cases computed <;>
      exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl

theorem frame_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    Frame state after := by
  unfold processParentExecutionPayload at computed
  dsimp only at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact Frame.refl _
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, applied⟩ := computed
  unfold applyParentExecutionPayload at applied
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at applied
  obtain ⟨_, _, _, _, _, _, _, _, settled, settledOk, requested, requestedOk, _, _, rfl⟩ :=
    applied
  unfold processParentRequests at requestedOk
  simp only [bind_ok_iff, ← Array.foldlM_toList] at requestedOk
  obtain ⟨_, depositsOk, _, withdrawalsOk, _, consolidationsOk, _, buildersOk, exitsOk⟩ :=
    requestedOk
  exact (frame_settleParentPayment settledOk).trans <|
    (Frame.foldlM (fun _ _ _ ok => frame_processDepositRequest ok) depositsOk).trans <|
    (Frame.foldlM (fun _ _ _ ok => frame_processWithdrawalRequest ok) withdrawalsOk).trans <|
    (Frame.foldlM (fun _ _ _ ok => frame_processConsolidationRequest ok) consolidationsOk).trans <|
    (Frame.foldlM (fun _ _ _ ok => frame_processBuilderDepositRequest ok) buildersOk).trans <|
    (Frame.foldlM (fun _ _ _ ok => frame_processBuilderExitRequest ok) exitsOk).trans
      (Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl)

theorem frame_processExecutionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    Frame state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok computed
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at recordedOk
    subst recordedOk
    exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl

theorem frame_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    Frame state after := by
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    exact (frame_processWithdrawals withdrawnOk).trans (frame_processExecutionPayloadBid bid)
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact (frame_processWithdrawals withdrawnOk).trans (frame_processExecutionPayload paid)
  · dsimp only at computed
    split at computed
    · exact frame_processExecutionPayload computed
    · cases computed
      exact Frame.refl _

/-! ## The sync aggregate -/

theorem frame_applySyncReward {reward proposerReward : Gwei} {member : ValidatorIndex × Bool}
    (computed : applySyncReward reward proposerReward state member = .ok after) :
    Frame state after := by
  unfold applySyncReward at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, raised, _, _, paid⟩ := computed
    exact (frame_increaseBalance raised).trans (frame_increaseBalance paid)
  · exact frame_decreaseBalance (liftAccessor_ok.mp computed)

theorem frame_processSyncAggregate {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    Frame state after := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  exact Frame.foldlM (fun _ _ _ ok => frame_applySyncReward ok) folded

/-! ## Blocks -/

/-- The operations of a block form a frame. -/
theorem frame_processOperations {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    Frame state after := by
  unfold processOperations at computed
  split at computed
  · unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
    exact (Frame.foldlM (fun _ _ _ ok => frame_processProposerSlashing ok) proposersOk).trans <|
      (Frame.foldlM (fun _ _ _ ok => frame_processAttesterSlashing ok) attestersOk).trans <|
      (Frame.foldlM (fun _ _ _ ok => frame_processAttestation ok) attestedOk).trans <|
      (Frame.foldlM (fun _ _ _ ok => frame_processVoluntaryExit ok) exitsOk).trans <|
      (Frame.foldlM (fun _ _ _ ok => frame_processBlsToExecutionChange ok) changesOk).trans <|
      Frame.foldlM (fun _ _ _ ok => by
        rw [processPayloadAttestation_eq ok]
        exact Frame.refl _) paid
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, exited,
    exitsOk, changed, changesOk, requestsOk⟩ := computed
  have changes : Frame exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact Frame.foldlM (fun _ _ _ ok => frame_processBlsToExecutionChange ok) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ Frame.refl _
  have requests : Frame changed after := by
    split at requestsOk
    · exact frame_processExecutionRequests requestsOk
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact requestsOk ▸ Frame.refl _
  exact (Frame.foldlM (fun _ _ _ ok => frame_processProposerSlashing ok) proposersOk).trans <|
    (Frame.foldlM (fun _ _ _ ok => frame_processAttesterSlashing ok) attestersOk).trans <|
    (Frame.foldlM (fun _ _ _ ok => frame_processAttestation ok) attestedOk).trans <|
    (Frame.foldlM (fun _ _ _ ok => frame_processDeposit ok) depositedOk).trans <|
    (Frame.foldlM (fun _ _ _ ok => frame_processVoluntaryExit ok) exitsOk).trans <|
    changes.trans requests

/-- A block forms a frame. -/
theorem frame_processBlock {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) : Frame state after := by
  unfold processBlock at computed
  split at computed
  · unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, _, operatedOk, synced⟩ := computed
    -- From Gloas the payload of the parent runs before the header.
    have paidFrame : Frame state paid := by
      split at paidOk
      · exact frame_processParentExecutionPayload paidOk
      · cases paidOk
        exact Frame.refl _
    -- From Bellatrix the execution part runs between the header and the RANDAO reveal.
    have executedFrame : Frame headed executed := by
      split at executedOk
      · exact frame_processBlockExecution executedOk
      · cases executedOk
        exact Frame.refl _
    -- Heze drops the vote on the deposit contract.
    have votedFrame : Frame revealed voted := by
      split at votedOk
      · exact frame_processEth1Data votedOk
      · cases votedOk
        exact Frame.refl _
    exact paidFrame.trans <| (frame_processBlockHeader headedOk).trans <| executedFrame.trans <|
      (frame_processRandao revealedOk).trans <| votedFrame.trans <|
      (frame_processOperations operatedOk).trans (frame_processSyncAggregate synced)
  simp only [bind_ok_iff] at computed
  obtain ⟨_, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := computed
  exact (frame_processBlockHeader headerOk).trans <| (frame_processRandao randaoOk).trans <|
    (frame_processEth1Data eth1Ok).trans (frame_processOperations operationsOk)

/-! ## The steps of an epoch -/

theorem frame_applyDeltas {rewards penalties : Array Gwei} {index : Nat}
    (computed : applyDeltas rewards penalties state index = .ok after) : Frame state after := by
  simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, raised, lowered⟩ := computed
  exact (frame_increaseBalance raised).trans (frame_decreaseBalance lowered)

theorem frame_applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (computed : applyAllDeltas state deltas = .ok after) : Frame state after :=
  Frame.foldlM (fun _ _ _ ok => frame_applyDeltas ok) computed

theorem frame_processRewardsAndPenalties
    (computed : processRewardsAndPenalties config state = .ok after) : Frame state after := by
  unfold processRewardsAndPenalties at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Frame.refl _
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact Frame.foldlM (fun _ _ _ ok => frame_applyAllDeltas ok) applied
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact frame_applyAllDeltas applied

/-- Joining the activation queue changes neither the exit nor the withdrawable epoch. -/
theorem queueForActivation_epochs {validator queued : Validator}
    (computed : queueForActivation state validator = .ok queued) :
    queued.exitEpoch = validator.exitEpoch ∧
      queued.withdrawableEpoch = validator.withdrawableEpoch := by
  unfold queueForActivation at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact ⟨rfl, rfl⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ ⟨rfl, rfl⟩

theorem frame_updateRegistryEntry {index : Nat}
    (computed : updateRegistryEntry config state index = .ok after) : Frame state after := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, queued, queuedOk, marked, markedOk, computed⟩ := computed
  obtain ⟨exitSame, withdrawableSame⟩ := queueForActivation_epochs queuedOk
  have set : Frame state marked := frame_setValidator markedOk fun ordered => by
    rw [exitSame, withdrawableSame]
    exact ordered validator (mem_of_getValidator found)
  split at computed
  · rw [liftAccessor_ok] at computed
    exact set.trans (frame_initiateValidatorExit computed)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ set

theorem frame_activateValidator {index : ValidatorIndex}
    (computed : activateValidator state index = .ok after) : Frame state after := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, _, _, set⟩ := computed
  exact frame_setValidator set fun ordered => ordered validator (mem_of_getValidator found)

theorem frame_updateRegistryEntryElectra {activationEpoch : Epoch} {index : Nat}
    (computed : updateRegistryEntryElectra config activationEpoch state index = .ok after) :
    Frame state after := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, computed⟩ := computed
  have kept : ExitsOrdered state → validator.exitEpoch ≤ validator.withdrawableEpoch :=
    fun ordered => ordered validator (mem_of_getValidator found)
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, set⟩ := computed
    exact frame_setValidator set kept
  split at computed
  · rw [liftAccessor_ok] at computed
    exact frame_initiateValidatorExit computed
  split at computed
  · rw [liftAccessor_ok] at computed
    exact frame_setValidator computed kept
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Frame.refl _

theorem frame_processRegistryUpdates
    (computed : processRegistryUpdates config state = .ok after) : Frame state after := by
  unfold processRegistryUpdates at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, computed⟩ := computed
    exact Frame.foldlM (fun _ _ _ ok => frame_updateRegistryEntryElectra ok) computed
  simp only [bind_ok_iff] at computed
  obtain ⟨updated, updatedOk, activated⟩ := computed
  exact (Frame.foldlM (fun _ _ _ ok => frame_updateRegistryEntry ok) updatedOk).trans
    (Frame.foldlM (fun _ _ _ ok => frame_activateValidator ok) activated)

theorem frame_applySlashingPenalty {total adjusted : Gwei} {index : Nat}
    (computed : applySlashingPenalty state total adjusted index = .ok after) :
    Frame state after := by
  simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, _, _, lowered⟩ := computed
      exact frame_decreaseBalance lowered
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ Frame.refl _
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Frame.refl _

theorem frame_applySlashingPenaltyElectra {perIncrement : Gwei} {index : Nat}
    (computed : applySlashingPenaltyElectra state perIncrement index = .ok after) :
    Frame state after := by
  simp only [applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, lowered⟩ := computed
      exact frame_decreaseBalance lowered
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ Frame.refl _
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Frame.refl _

theorem frame_processSlashings (computed : processSlashings state = .ok after) :
    Frame state after := by
  unfold processSlashings at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact Frame.foldlM (fun _ _ _ ok => frame_applySlashingPenaltyElectra ok) applied
  · exact Frame.foldlM (fun _ _ _ ok => frame_applySlashingPenalty ok) computed

theorem frame_processEth1DataReset {before : fork < .hegota}
    (computed : processEth1DataReset before state = .ok after) : Frame state after := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Frame.refl _

theorem frame_updateEffectiveBalance {index : Nat}
    (computed : updateEffectiveBalance state index = .ok after) : Frame state after := by
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, _, _, _, _, set⟩ := computed
  exact frame_setValidator set fun ordered => ordered validator (mem_of_getValidator found)

theorem frame_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) : Frame state after := by
  unfold processEffectiveBalanceUpdates at computed
  exact Frame.foldlM (fun _ _ _ ok => frame_updateEffectiveBalance ok) computed

theorem frame_processSlashingsReset (computed : processSlashingsReset state = .ok after) :
    Frame state after := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq computed
  exact frame_slashings _ _

theorem frame_processRandaoMixesReset (computed : processRandaoMixesReset state = .ok after) :
    Frame state after := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq computed
  exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl

theorem frame_processHistoricalRootsUpdate
    (computed : processHistoricalRootsUpdate state = .ok after) : Frame state after := by
  unfold processHistoricalRootsUpdate at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Frame.refl _

theorem frame_processParticipationRecordUpdates
    (computed : processParticipationRecordUpdates state = .ok after) : Frame state after := by
  unfold processParticipationRecordUpdates at computed
  split at computed
  · cases computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl

/-! ## The steps of an epoch from Altair -/

theorem frame_processInactivityUpdates {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) : Frame state after := by
  unfold processInactivityUpdates at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Frame.refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl

theorem frame_passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      Frame state pass.1.state
  | [], _, _, _, _, _, computed => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact Frame.refl _
  | deposit :: rest, state, processed, count, postponed, pass, computed => by
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      exact Frame.refl _
    split at computed
    · split at computed
      · cases computed
      rename_i credited
      split at computed
      · cases computed
      cases computed
      exact (frame_applyPendingDeposit credited).trans
        (frame_passPendingDeposits (deposits := rest) ‹_›)
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact frame_passPendingDeposits (deposits := rest) ‹_›
    split at computed
    · cases computed
    split at computed
    · cases computed
      exact Frame.refl _
    split at computed
    · cases computed
    rename_i credited
    split at computed
    · cases computed
    cases computed
    exact (frame_applyPendingDeposit credited).trans
      (frame_passPendingDeposits (deposits := rest) ‹_›)

theorem frame_processPendingDeposits {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    Frame state after := by
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals
    exact (frame_passPendingDeposits ‹_›).trans
      (Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl)

theorem frame_passPendingConsolidations {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      Frame state result.1
  | [], _, _, computed => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact Frame.refl _
  | consolidation :: rest, state, result, computed => by
    simp only [passPendingConsolidations, bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨source, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨⟨passed, read⟩, passedOk, computed⟩ := computed
      cases computed
      exact frame_passPendingConsolidations (result := (passed, read)) passedOk
    split at computed
    · cases computed
      exact Frame.refl _
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, lowered, loweredOk, raised, raisedOk, ⟨passed, read⟩, passedOk, computed⟩ :=
      computed
    cases computed
    exact (frame_decreaseBalance loweredOk).trans <|
      (frame_increaseBalance raisedOk).trans
        (frame_passPendingConsolidations (result := (passed, read)) passedOk)

theorem frame_processPendingConsolidations {electra : .pectra ≤ fork}
    (computed : processPendingConsolidations state electra = .ok after) : Frame state after := by
  unfold processPendingConsolidations at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals
    exact (frame_passPendingConsolidations ‹_›).trans
      (Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl)

theorem frame_processPendingBalances
    (computed : processPendingBalances config checks state = .ok after) : Frame state after := by
  unfold processPendingBalances at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, deposited, consolidated⟩ := computed
    exact (frame_processPendingDeposits deposited).trans
      (frame_processPendingConsolidations consolidated)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Frame.refl _

theorem frame_processBuilderPendingPayments {gloas : .glamsterdam ≤ fork}
    (computed : processBuilderPendingPayments state gloas = .ok after) : Frame state after := by
  simp only [processBuilderPendingPayments, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl

theorem frame_processHistoricalSummariesUpdate {capella : .shapella ≤ fork}
    (computed : processHistoricalSummariesUpdate state capella = .ok after) :
    Frame state after := by
  unfold processHistoricalSummariesUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals first
    | exact Frame.refl _
    | exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl

theorem frame_processParticipationFlagUpdates (state : BeaconState preset fork)
    (altair : .altair ≤ fork) : Frame state (processParticipationFlagUpdates state altair) :=
  Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl

theorem frame_processSyncCommitteeUpdates {altair : .altair ≤ fork}
    (computed : processSyncCommitteeUpdates state altair = .ok after) : Frame state after := by
  unfold processSyncCommitteeUpdates at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals first
    | exact Frame.refl _
    | exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl

theorem frame_processProposerLookahead {fulu : .fusaka ≤ fork}
    (computed : processProposerLookahead state fulu = .ok after) : Frame state after := by
  simp only [processProposerLookahead, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl

theorem frame_processPtcWindow {gloas : .glamsterdam ≤ fork}
    (computed : processPtcWindow state gloas = .ok after) : Frame state after := by
  simp only [processPtcWindow, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl

/-- The steps that close an epoch from Altair, after the history. -/
private theorem frame_epochEnd {altair : .altair ≤ fork}
    {rooted synced looked : BeaconState preset fork}
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair) altair =
      .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) : Frame rooted after := by
  have lookedFrame : Frame synced looked := by
    split at lookedOk
    · exact frame_processProposerLookahead (liftAccessor_ok.mp lookedOk)
    · simp only [pure, Except.pure, Except.ok.injEq] at lookedOk
      exact lookedOk ▸ Frame.refl _
  have windowedFrame : Frame looked after := by
    split at windowed
    · exact frame_processPtcWindow (liftAccessor_ok.mp windowed)
    · simp only [pure, Except.pure, Except.ok.injEq] at windowed
      exact windowed ▸ Frame.refl _
  exact (frame_processParticipationFlagUpdates rooted altair).trans <|
    (frame_processSyncCommitteeUpdates syncedOk).trans (lookedFrame.trans windowedFrame)

/-- From Altair, the epoch transition is justification, then steps that keep the frame. -/
theorem processEpochAltair_frame {altair : .altair ≤ fork}
    (computed : processEpochAltair config checks state altair = .ok after) :
    ∃ justified, processJustificationAndFinalization state = .ok justified ∧
      Frame justified after := by
  unfold processEpochAltair at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
    registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk, balanced,
    balancedOk, cleared, clearedOk, mixed, mixedOk, computed⟩ := computed
  have resetFrame : Frame slashed reset := by
    split at resetOk
    · exact frame_processEth1DataReset resetOk
    · simp only [pure, Except.pure, Except.ok.injEq] at resetOk
      exact resetOk ▸ Frame.refl _
  have paidFrame : Frame pending paid := by
    split at paidOk
    · exact frame_processBuilderPendingPayments (liftAccessor_ok.mp paidOk)
    · simp only [pure, Except.pure, Except.ok.injEq] at paidOk
      exact paidOk ▸ Frame.refl _
  have head : Frame justified mixed :=
    (frame_processInactivityUpdates scoredOk).trans <|
    (frame_processRewardsAndPenalties rewardedOk).trans <|
    (frame_processRegistryUpdates registeredOk).trans <|
    (frame_processSlashings slashedOk).trans <|
    resetFrame.trans <|
    (frame_processPendingBalances pendingOk).trans <|
    paidFrame.trans <|
    (frame_processEffectiveBalanceUpdates balancedOk).trans <|
    (frame_processSlashingsReset clearedOk).trans <|
    (frame_processRandaoMixesReset mixedOk)
  split at computed <;> simp only [bind_ok_iff] at computed <;>
    obtain ⟨rooted, rootedOk, synced, syncedOk, looked, lookedOk, windowed⟩ := computed
  · exact ⟨justified, justifiedOk, head.trans <|
      (frame_processHistoricalSummariesUpdate rootedOk).trans
        (frame_epochEnd syncedOk lookedOk windowed)⟩
  · exact ⟨justified, justifiedOk, head.trans <|
      (frame_processHistoricalRootsUpdate rootedOk).trans
        (frame_epochEnd syncedOk lookedOk windowed)⟩

/-! ## Justification and the epoch transition -/

/-- The current justified epoch is at most the previous epoch. -/
def JustifiedSettled (state : BeaconState preset fork) : Prop :=
  state.currentJustifiedCheckpoint.epoch ≤ getPreviousEpoch state

/-- The properties that each valid block keeps. -/
structure Invariant (state : BeaconState preset fork) : Prop where
  balancesMatch : BalancesMatch state
  exitsOrdered : ExitsOrdered state
  ordered : CheckpointsOrdered state
  settled : JustifiedSettled state

theorem getPreviousEpoch_toNat (state : BeaconState preset fork) :
    (getPreviousEpoch state).toNat = (getCurrentEpoch state).toNat - 1 := by
  unfold getPreviousEpoch saturatingSub
  split
  · rename_i lt
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt lt)]
    rfl
  · rename_i notLt
    rw [UInt64.lt_iff_toNat_lt] at notLt
    simp only [UInt64.toNat_one] at notLt
    simp only [UInt64.toNat_zero]
    omega

theorem Frame.invariant (frame : Frame state after) (holds : Invariant state) :
    Invariant after where
  balancesMatch := frame.balancesMatch holds.balancesMatch
  exitsOrdered := frame.exitsOrdered holds.exitsOrdered
  ordered := by
    have := holds.ordered
    unfold CheckpointsOrdered at this ⊢
    rw [frame.finalized, frame.previousJustified, frame.currentJustified]
    exact this
  settled := by
    have := holds.settled
    unfold JustifiedSettled getPreviousEpoch getCurrentEpoch at this ⊢
    rw [frame.currentJustified, frame.slot]
    exact this

/-- Justification and finalization keep the checkpoints in order, and the finalized epoch rises.

They change neither the slot, nor the registry, nor the balances.

The new current justified epoch is at most the current epoch. -/
theorem processJustificationAndFinalization_invariant (ordered : CheckpointsOrdered state)
    (settled : JustifiedSettled state)
    (computed : processJustificationAndFinalization state = .ok after) :
    CheckpointsOrdered after ∧
      state.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch ∧
      after.currentJustifiedCheckpoint.epoch ≤ getCurrentEpoch state ∧
      after.slot = state.slot ∧ after.validators = state.validators ∧
      after.balances = state.balances := by
  obtain ⟨ordered', finalized⟩ :=
    processJustificationAndFinalization_ordered ordered settled computed
  have previous := getPreviousEpoch_le state
  obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · subst same
    exact ⟨ordered', finalized, UInt64.le_trans settled previous, rfl, rfl, rfl⟩
  · obtain ⟨_, current, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    refine ⟨ordered', finalized, ?_, by rw [← rest], by rw [← rest], by rw [← rest]⟩
    rcases current with same | same | same
    · rw [same]
      exact UInt64.le_trans settled previous
    · rw [same]
      exact previous
    · rw [same]
      exact UInt64.le_refl _

/-- What an epoch transition keeps when it is justification, then steps that keep the frame. -/
private theorem epoch_invariant {justified : BeaconState preset fork} (holds : Invariant state)
    (justifiedOk : processJustificationAndFinalization state = .ok justified)
    (frame : Frame justified after) :
    after.slot = state.slot ∧ BalancesMatch after ∧ ExitsOrdered after ∧
      CheckpointsOrdered after ∧
      state.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch ∧
      after.currentJustifiedCheckpoint.epoch ≤ getCurrentEpoch state := by
  obtain ⟨ordered, finalized, current, slot, validators, balances⟩ :=
    processJustificationAndFinalization_invariant holds.ordered holds.settled justifiedOk
  have balancesMatch : BalancesMatch justified := by
    have := holds.balancesMatch
    unfold BalancesMatch at this ⊢
    rw [validators, balances]
    exact this
  have exitsOrdered : ExitsOrdered justified := by
    have := holds.exitsOrdered
    unfold ExitsOrdered at this ⊢
    rw [validators]
    exact this
  refine ⟨frame.slot.trans slot, frame.balancesMatch balancesMatch,
    frame.exitsOrdered exitsOrdered, ?_, ?_, ?_⟩
  · unfold CheckpointsOrdered at ordered ⊢
    rw [frame.finalized, frame.previousJustified, frame.currentJustified]
    exact ordered
  · rw [frame.finalized]
    exact finalized
  · rw [frame.currentJustified]
    exact current

/-- The epoch transition keeps the order of the checkpoints and the slot.

The finalized epoch does not decrease.

The current justified epoch ends at most at the current epoch.

The registry keeps one balance for each validator, and each exit no later than its withdrawal. -/
theorem processEpoch_invariant (holds : Invariant state)
    (computed : processEpoch config checks state = .ok after) :
    after.slot = state.slot ∧ BalancesMatch after ∧ ExitsOrdered after ∧
      CheckpointsOrdered after ∧
      state.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch ∧
      after.currentJustifiedCheckpoint.epoch ≤ getCurrentEpoch state := by
  unfold processEpoch at computed
  split at computed
  · obtain ⟨justified, justifiedOk, frame⟩ := processEpochAltair_frame computed
    exact epoch_invariant holds justifiedOk frame
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := computed
  exact epoch_invariant holds justifiedOk <|
    (frame_processRewardsAndPenalties rewardedOk).trans <|
    (frame_processRegistryUpdates registeredOk).trans <|
    (frame_processSlashings slashedOk).trans <|
    (frame_processEth1DataReset resetOk).trans <|
    (frame_processEffectiveBalanceUpdates balancedOk).trans <|
    (frame_processSlashingsReset clearedOk).trans <|
    (frame_processRandaoMixesReset mixedOk).trans <|
    (frame_processHistoricalRootsUpdate rootedOk).trans <|
    frame_processParticipationRecordUpdates rotated

/-! ## Slots and blocks -/

theorem getCurrentEpoch_toNat (state : BeaconState preset fork) :
    (getCurrentEpoch state).toNat = state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
  simp [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div]

theorem frame_processSlot (computed : processSlot state = .ok after) : Frame state after := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok computed
  exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl

/-- One slot keeps the invariant, and the finalized epoch does not decrease.

When the slot ends an epoch, the current justified epoch is at most that epoch.

The next slot starts the next epoch, whose previous epoch is that one. -/
theorem advanceSlot_invariant (holds : Invariant state)
    (computed : advanceSlot config checks state = .ok after) :
    Invariant after ∧ state.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, ⟨_, sum⟩, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have cachedFrame := frame_processSlot cachedOk
  have cachedHolds := cachedFrame.invariant holds
  simp only [UInt64.toNat_one] at sum
  have stateEpoch := getCurrentEpoch_toNat state
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    obtain ⟨_, balancesMatch, exitsOrdered, ordered, finalized, current⟩ :=
      processEpoch_invariant cachedHolds epochedOk
    have boundary' : next.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 := by
      simpa [UInt64.toNat_mod] using congrArg UInt64.toNat boundary
    have step : next.toNat / preset.SLOTS_PER_EPOCH.toNat =
        state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 := by
      rw [sum]
      exact Nat.succ_div_of_dvd (Nat.dvd_of_mod_eq_zero (sum ▸ boundary'))
    refine ⟨⟨balancesMatch, exitsOrdered, ordered, ?_⟩, ?_⟩
    · have current' := UInt64.le_iff_toNat_le.mp current
      rw [getCurrentEpoch_toNat, cachedFrame.slot] at current'
      unfold JustifiedSettled
      rw [UInt64.le_iff_toNat_le, getPreviousEpoch_toNat, getCurrentEpoch_toNat]
      dsimp only
      omega
    · rw [← cachedFrame.finalized]
      exact finalized
  · rename_i notBoundary
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    have notBoundary' : ¬preset.SLOTS_PER_EPOCH.toNat ∣ state.slot.toNat + 1 := by
      intro divides
      apply notBoundary
      apply UInt64.toNat_inj.mp
      simpa [UInt64.toNat_mod, sum] using Nat.mod_eq_zero_of_dvd divides
    have step : next.toNat / preset.SLOTS_PER_EPOCH.toNat =
        state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      rw [sum]
      exact Nat.succ_div_of_not_dvd notBoundary'
    refine ⟨⟨cachedHolds.balancesMatch, cachedHolds.exitsOrdered, cachedHolds.ordered, ?_⟩, ?_⟩
    · have settled := UInt64.le_iff_toNat_le.mp holds.settled
      rw [getPreviousEpoch_toNat, getCurrentEpoch_toNat] at settled
      unfold JustifiedSettled
      rw [UInt64.le_iff_toNat_le, getPreviousEpoch_toNat, getCurrentEpoch_toNat]
      dsimp only
      rw [cachedFrame.currentJustified, step]
      exact settled
    · rw [cachedFrame.finalized]
      exact UInt64.le_refl _

theorem advanceSlots_invariant :
    ∀ {count : Nat} {state after : BeaconState preset fork}, Invariant state →
      advanceSlots config checks count state = .ok after →
      Invariant after ∧ state.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch
  | 0, state, after, holds, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨holds, UInt64.le_refl _⟩
  | count + 1, state, after, holds, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    obtain ⟨nextHolds, first⟩ := advanceSlot_invariant holds nextOk
    obtain ⟨afterHolds, second⟩ := advanceSlots_invariant nextHolds rest
    exact ⟨afterHolds, UInt64.le_trans first second⟩

/-- Advancing to a later slot keeps the invariant.

The finalized epoch does not decrease. -/
theorem processSlots_invariant {slot : Slot} (holds : Invariant state)
    (computed : processSlots config checks state slot = .ok after) :
    Invariant after ∧ state.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch := by
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, advanced⟩ := computed
  exact advanceSlots_invariant holds advanced

/-- Each valid block keeps the invariant, and the finalized epoch never decreases.

The registry and the balances keep one entry for each validator.

Each validator may withdraw no earlier than it exits.

The checkpoints stay in order, and the current justified epoch stays at most the previous epoch.

This holds for every signature check and with or without validating the result. -/
theorem stateTransition_invariant
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool} (holds : Invariant state)
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    Invariant after ∧ state.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch := by
  obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok computed
  obtain ⟨advancedHolds, finalized⟩ := processSlots_invariant holds slotsOk
  have frame := frame_processBlock blockOk
  refine ⟨frame.invariant advancedHolds, ?_⟩
  rw [frame.finalized]
  exact finalized

end EthLib.Consensus
