module

public import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
import EthLib.Consensus.Proofs.Transition.Committees
import EthLib.Consensus.Proofs.Transition.Requests

/-!
# Effective balances kept by block operations

A block operation keeps the effective balance of every validator that existed before it.

Before Gloas a whole block keeps them.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The effective balance at a registry position, or zero past the end of the registry. -/
def effectiveAt (s : ForkedBeaconState preset) (i : Nat) : Nat :=
  ((s.state.validators.data[i]?).map (·.effectiveBalance.toNat)).getD 0

/-- The ordering of the effective-balance caps that the departure bound assumes. -/
structure CapOrder (preset : Preset) : Prop where
  activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE
  compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA

/-- The mainnet preset orders its effective-balance caps. -/
theorem CapOrder.mainnet : CapOrder Preset.mainnet := ⟨by decide, by decide⟩

/-- The minimal preset orders its effective-balance caps. -/
theorem CapOrder.minimal : CapOrder Preset.minimal := ⟨by decide, by decide⟩

/-- Each validator of the first state keeps its effective balance in the second. -/
def EffectiveKept {f h : Fork} (s : BeaconState preset f)
    (t : BeaconState preset h) : Prop :=
  ∀ i, i < s.validators.data.size → effectiveAt ⟨h, t⟩ i = effectiveAt ⟨f, s⟩ i

theorem effectiveKept_refl {f : Fork} (s : BeaconState preset f) : EffectiveKept s s :=
  fun _ _ => rfl

theorem effectiveKept_trans {f h k : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} {u : BeaconState preset k}
    (one : EffectiveKept s t) (two : EffectiveKept t u)
    (grows : s.validators.data.size ≤ t.validators.data.size) : EffectiveKept s u :=
  fun i inside => (two i (Nat.lt_of_lt_of_le inside grows)).trans (one i inside)

theorem effectiveKept_data {f h : Fork} {s : BeaconState preset f}
    {t : BeaconState preset h} (same : t.validators.data = s.validators.data := by rfl) :
    EffectiveKept s t := by
  intro i _
  simp only [effectiveAt, same]

private theorem effectiveKept_setValidatorAt {f : Fork} {s t : BeaconState preset f}
    {index : Nat} {old v : Validator} (found : getValidatorAt s index = .ok old)
    (set : s.setValidatorAt index v = .ok t)
    (same : v.effectiveBalance = old.effectiveBalance) : EffectiveKept s t := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have read : s.validators.data[index]? = some old := by
    simpa [getValidatorAt, inside] using found
  intro i _
  by_cases eq : i = index
  · subst i
    simp [effectiveAt, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      read, same]
  · simp [effectiveAt, BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
      Ne.symm eq]

private theorem effectiveKept_setValidator {f : Fork} {s t : BeaconState preset f}
    {index : ValidatorIndex} {old v : Validator} (found : getValidator s index = .ok old)
    (set : s.setValidator index v = .ok t)
    (same : v.effectiveBalance = old.effectiveBalance) : EffectiveKept s t :=
  effectiveKept_setValidatorAt (by rwa [← getValidator_eq_getValidatorAt])
    (by rwa [← setValidator_eq_setValidatorAt]) same

private theorem effectiveKept_increase {f : Fork} {s t : BeaconState preset f}
    {index amount : UInt64} (ok : increaseBalance s index amount = .ok t) : EffectiveKept s t :=
  effectiveKept_data (congrArg (·.data) (increaseBalance_validators ok))

private theorem effectiveKept_decrease {f : Fork} {s t : BeaconState preset f}
    {index amount : UInt64} (ok : decreaseBalance s index amount = .ok t) : EffectiveKept s t :=
  effectiveKept_data (congrArg (·.data) (decreaseBalance_validators ok))

private theorem effectiveKept_exit {f : Fork} {s t : BeaconState preset f}
    {index : ValidatorIndex} (ok : initiateValidatorExit config s index = .ok t) :
    EffectiveKept s t := by
  obtain ⟨v, found, unchanged | ⟨_, queued, epoch, withdrawal, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · rw [unchanged.2]; exact effectiveKept_refl _
  · have same := (exitQueue_validators queue).1
    exact effectiveKept_trans (effectiveKept_data (congrArg (·.data) same))
      (effectiveKept_setValidator (old := v)
        (by rw [getValidator_of_validators_eq same]; exact found) set rfl)
      (Nat.le_of_eq (by rw [same]))

theorem effectiveKept_slash {f : Fork} {s t : BeaconState preset f}
    {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ok : slashValidator config s index whistleblower = .ok t) : EffectiveKept s t := by
  obtain ⟨_, _, _, marked, _, _, slashings, _, _, _, _, last, exited, found, _, set,
    _, _, _, lowered, _, _, raised, paid, rfl⟩ := slashValidator_ok ok
  have first := effectiveKept_trans (effectiveKept_exit exited)
    (effectiveKept_setValidator found set rfl) (frame_initiateValidatorExit exited).registryGrows
  have second := effectiveKept_trans (effectiveKept_decrease lowered)
    (effectiveKept_trans (effectiveKept_increase raised) (effectiveKept_increase paid)
      (frame_increaseBalance raised).registryGrows) (frame_decreaseBalance lowered).registryGrows
  have middle := effectiveKept_trans (effectiveKept_data (s := marked)
    (t := { marked with slashings })) second (Nat.le_refl _)
  have total := effectiveKept_trans first middle
    (Nat.le_trans (frame_initiateValidatorExit exited).registryGrows
      (Nat.le_of_eq (sameSizes_setValidator set).1.symm))
  split <;> exact total

theorem effectiveKept_fold {f : Fork} {s t : BeaconState preset f}
    {α ε : Type} {step : BeaconState preset f → α → Except ε _} {xs : List α}
    (kept : ∀ a b c, step a b = .ok c → EffectiveKept a c)
    (grows : ∀ a b c, step a b = .ok c → a.validators.data.size ≤ c.validators.data.size)
    (ok : xs.foldlM step s = .ok t) : EffectiveKept s t := by
  have result := foldlM_ok_invariant
    (fun t => EffectiveKept s t ∧ s.validators.data.size ≤ t.validators.data.size)
    (fun a b c previous computed =>
      ⟨effectiveKept_trans previous.1 (kept a b c computed) previous.2,
        Nat.le_trans previous.2 (grows a b c computed)⟩)
    ⟨effectiveKept_refl s, Nat.le_refl _⟩ ok
  exact result.1

private theorem effectiveKept_add {f : Fork} {s t : BeaconState preset f}
    {key : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (ok : addValidatorToRegistry s key credentials amount = .ok t) : EffectiveKept s t := by
  intro i inside
  simp [effectiveAt, addValidatorToRegistry_validators_eq_push ok, Array.getElem?_push,
    Nat.ne_of_lt inside]

private theorem effectiveKept_deposit {f : Fork} {s t : BeaconState preset f}
    {deposit : PendingDeposit}
    (ok : applyPendingDeposit config checks s deposit = .ok t) : EffectiveKept s t := by
  rcases applyPendingDeposit_cases ok with rfl | ⟨_, raised⟩ | ⟨_, added⟩
  · exact effectiveKept_refl _
  · exact effectiveKept_increase raised
  · exact effectiveKept_add added

private theorem effectiveKept_applyDeposit {f : Fork} {s t : BeaconState preset f}
    {key : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    {signature : Cryptography.Bls.BLSSignature}
    (ok : applyDeposit config checks s key credentials amount signature = .ok t) :
    EffectiveKept s t := by
  unfold applyDeposit at ok
  split at ok
  · unfold applyDepositElectra at ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨middle, added, queued⟩ := ok
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq queued
        exact effectiveKept_trans (effectiveKept_add added) (effectiveKept_data rfl)
          (by rw [addValidatorToRegistry_validators_eq_push added]; simp)
      · cases ok; exact effectiveKept_refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp ok)
      exact effectiveKept_refl _
  · exact effectiveKept_deposit ok

theorem effectiveKept_processDeposit {f : Fork} {s t : BeaconState preset f}
    {before : f < .hegota} {deposit : Deposit}
    (ok : processDeposit config checks before s deposit = .ok t) : EffectiveKept s t := by
  obtain ⟨_, _, next, _, credited⟩ := processDeposit_ok ok
  exact effectiveKept_trans (effectiveKept_data (s := s)
    (t := { s with eth1DepositIndex := fun _ => next }))
    (effectiveKept_applyDeposit credited) (Nat.le_refl _)

theorem effectiveKept_registryElectra {f : Fork} {s t : BeaconState preset f}
    {epoch : Epoch} {index : Nat}
    (ok : updateRegistryEntryElectra config epoch s index = .ok t) : EffectiveKept s t := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, set⟩ := ok
    exact effectiveKept_setValidatorAt found set rfl
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, exited⟩ := ok
    exact effectiveKept_exit exited
  split at ok
  · exact effectiveKept_setValidatorAt found (liftAccessor_ok.mp ok) rfl
  · cases ok; exact effectiveKept_refl _

private theorem effectiveKept_excess {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {index : ValidatorIndex}
    (ok : queueExcessActiveBalance s electra index = .ok t) : EffectiveKept s t := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, _, _, _, set, rfl⟩ := ok
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact effectiveKept_refl _
  · cases ok; exact effectiveKept_refl _

private theorem effectiveKept_compounding {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {index : ValidatorIndex}
    (ok : switchToCompoundingValidator s electra index = .ok t) : EffectiveKept s t := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at ok
  obtain ⟨_, found, _, set, queued⟩ := ok
  exact effectiveKept_trans (effectiveKept_setValidator found set rfl)
    (effectiveKept_excess queued) (Nat.le_of_eq (sameSizes_setValidator set).1.symm)

private theorem effectiveKept_consolidate {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {sourceIndex targetIndex : ValidatorIndex} {source : Validator}
    (found : s.validators.data[sourceIndex.toNat]? = some source)
    (ok : queueConsolidation config s electra sourceIndex source targetIndex = .ok t) :
    EffectiveKept s t := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, Base.Uint64.addChecked_ok_iff, pure, Except.pure] at ok
  obtain ⟨⟨churnedState, exitEpoch⟩, churned, withdrawal, _, marked, set, _, _, ok⟩ := ok
  simp only [Except.ok.injEq] at ok
  subst ok
  have validators := (computeConsolidationEpochAndUpdateChurn_earliest churned).2.1
  have read : getValidator churnedState sourceIndex = .ok source := by
    rw [getValidator, validators, found]
  exact effectiveKept_trans (effectiveKept_data (by rw [validators]))
    (effectiveKept_trans (effectiveKept_setValidator read set rfl) (effectiveKept_data rfl)
      (Nat.le_of_eq (sameSizes_setValidator set).1.symm)) (Nat.le_of_eq (by rw [validators]))

theorem effectiveKept_consolidationRequest {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t) : EffectiveKept s t := by
  unfold processConsolidationRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact effectiveKept_refl _)
    | exact effectiveKept_compounding (liftAccessor_ok.mp ok)
    | exact effectiveKept_consolidate (getElem?_toNat_of_ofNatChecked (by assumption)) ok

private theorem effectiveKept_partial {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {index : ValidatorIndex} {v : Validator} {amount owed : Gwei}
    (ok : requestPartialWithdrawal config s electra index v amount owed = .ok t) :
    EffectiveKept s t := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at ok
  obtain ⟨_, _, _, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at ok
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := ok
    exact effectiveKept_data (by rw [(computeExitEpochAndUpdateChurn_earliest churned).2.1])
  · cases ok; exact effectiveKept_refl _

theorem effectiveKept_withdrawalRequest {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t) : EffectiveKept s t := by
  unfold processWithdrawalRequest at ok
  simp only [bind, Except.bind, pure, Except.pure] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact effectiveKept_refl _)
    | exact effectiveKept_exit (liftAccessor_ok.mp ok)
    | exact effectiveKept_partial ok

theorem effectiveKept_depositRequest {f : Fork} {s t : BeaconState preset f}
    {electra : .pectra ≤ f} {request : DepositRequest}
    (ok : processDepositRequest s electra request = .ok t) : EffectiveKept s t := by
  obtain ⟨start, recorded⟩ := recordDepositRequestsStart_eq (state := s) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit,
    bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, rfl⟩ := ok
  exact effectiveKept_refl _

private theorem effectiveKept_requests {f : Fork} {s t : BeaconState preset f}
    {body : BeaconBlockBody preset f} {electra : .pectra ≤ f ∧ f < .glamsterdam}
    (ok : processExecutionRequests config s body electra = .ok t) : EffectiveKept s t := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨deposited, deposits, withdrawn, withdrawals, consolidations⟩ := ok
  have first := effectiveKept_fold (fun _ _ _ => effectiveKept_depositRequest)
    (fun _ _ _ ok => (registryLifecycle_processDepositRequest ok).size_le) deposits
  have grows := RegistryLifecycle.foldlM
    (fun _ _ _ ok => registryLifecycle_processDepositRequest ok) deposits
  have second := effectiveKept_fold (fun _ _ _ => effectiveKept_withdrawalRequest)
    (fun _ _ _ ok => (registryLifecycle_processWithdrawalRequest ok).size_le) withdrawals
  have grows' := RegistryLifecycle.foldlM
    (fun _ _ _ ok => registryLifecycle_processWithdrawalRequest ok) withdrawals
  exact effectiveKept_trans first (effectiveKept_trans second
    (effectiveKept_fold (fun _ _ _ => effectiveKept_consolidationRequest)
      (fun _ _ _ ok => (registryLifecycle_processConsolidationRequest ok).size_le) consolidations)
    grows'.size_le) grows.size_le

theorem effectiveKept_proposerSlashing {f : Fork} {s t : BeaconState preset f}
    {slashing : ProposerSlashing}
    (ok : processProposerSlashing config checks s slashing = .ok t) : EffectiveKept s t := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ok
  exact effectiveKept_slash slashed

theorem effectiveKept_attesterSlashing {f : Fork} {s t : BeaconState preset f}
    {slashing : AttesterSlashing preset f}
    (ok : processAttesterSlashing config checks s slashing = .ok t) : EffectiveKept s t := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ok
  have result := foldlM_ok_invariant
    (fun step => EffectiveKept s step.1 ∧ s.validators.data.size ≤ step.1.validators.data.size)
    (fun step _ next before ok => ?_)
    (show EffectiveKept s (s, false).1 ∧ s.validators.data.size ≤ (s, false).1.validators.data.size
      from ⟨effectiveKept_refl _, Nat.le_refl _⟩) folded
  · exact result.1
  · obtain ⟨middle, slashedAny⟩ := step
    simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨_, slashed, rfl⟩ := ok
      exact ⟨effectiveKept_trans before.1 (effectiveKept_slash slashed) before.2,
        Nat.le_trans before.2 (frame_slashValidator slashed).registryGrows⟩
    · cases ok; exact before

theorem effectiveKept_voluntaryExit {f : Fork} {s t : BeaconState preset f}
    {signed : SignedVoluntaryExit}
    (ok : processVoluntaryExit config checks s signed = .ok t) : EffectiveKept s t :=
  effectiveKept_exit (processVoluntaryExit_initiates ok)

theorem effectiveKept_blsChange {f : Fork} {s t : BeaconState preset f}
    {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) : EffectiveKept s t := by
  obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  exact effectiveKept_setValidator found set rfl

/-- Before Gloas, a block keeps the effective balance of every existing validator. -/
theorem effectiveKept_block {f : Fork} {s t : BeaconState preset f}
    {engine : ExecutionEngine preset f} {block : BeaconBlock preset f}
    (early : f < .glamsterdam) (ok : processBlock config checks engine s block = .ok t) :
    EffectiveKept s t := by
  -- Composing two steps needs the registry growth of the first.
  let Kept (a b : BeaconState preset f) : Prop :=
    EffectiveKept a b ∧ a.validators.data.size ≤ b.validators.data.size
  have refl (a : BeaconState preset f) : Kept a a := ⟨effectiveKept_refl a, Nat.le_refl _⟩
  have trans {a b c : BeaconState preset f} (one : Kept a b) (two : Kept b c) : Kept a c :=
    ⟨effectiveKept_trans one.1 two.1 one.2, Nat.le_trans one.2 two.2⟩
  have same {a b : BeaconState preset f} (validators : b.validators = a.validators) : Kept a b :=
    ⟨effectiveKept_data (congrArg (·.data) validators),
      Nat.le_of_eq (congrArg (·.data.size) validators).symm⟩
  have folds {α : Type} {step : BeaconState preset f → α → Except TransitionError _}
      (each : ∀ a x b, step a x = .ok b → Kept a b) {items : List α}
      {a b : BeaconState preset f} (computed : items.foldlM step a = .ok b) : Kept a b :=
    foldlM_ok_invariant (Kept a) (fun _ _ _ before stepped => trans before (each _ _ _ stepped))
      (refl a) computed
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput ok
  have head : Kept s input := same (started.validators_eq early)
  obtain ⟨_, _, _, proposersOk, slashingsOk, attestedOk, rest⟩ :=
    processOperations_folds_of Kept refl trans
      (fun deposited => ⟨effectiveKept_processDeposit deposited,
        (frame_processDeposit deposited).registryGrows⟩)
      (fun exited => ⟨effectiveKept_voluntaryExit exited,
        (frame_processVoluntaryExit exited).registryGrows⟩)
      (fun changed => ⟨effectiveKept_blsChange changed,
        (frame_processBlsToExecutionChange changed).registryGrows⟩)
      (fun requested => ⟨effectiveKept_requests requested,
        (registryLifecycle_processExecutionRequests requested).size_le⟩)
      (fun attested => same (by rw [processPayloadAttestation_eq attested])) operated
  have tail : Kept last t := by
    split at synced
    · obtain ⟨_, rfl⟩ := processSyncAggregate_eq synced
      exact same rfl
    · cases synced
      exact refl _
  exact (trans head <| trans (folds (fun _ _ _ slashed => ⟨effectiveKept_proposerSlashing slashed,
      (frame_processProposerSlashing slashed).registryGrows⟩) proposersOk) <|
    trans (folds (fun _ _ _ slashed => ⟨effectiveKept_attesterSlashing slashed,
      (frame_processAttesterSlashing slashed).registryGrows⟩) slashingsOk) <|
    trans (folds (fun _ _ _ attested => ⟨effectiveKept_data
        (by rw [(processAttestation_registry attested).1]),
      (frame_processAttestation attested).registryGrows⟩) attestedOk) <|
    trans rest tail).1

end EthLib.Consensus
