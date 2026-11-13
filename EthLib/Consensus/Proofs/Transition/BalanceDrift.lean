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
  unfold applyPendingDeposit at ok
  split at ok
  · split at ok
    · cases ok; exact effectiveKept_refl _
    simp only [bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · exact effectiveKept_add ok
    · cases ok; exact effectiveKept_refl _
  · simp only [liftAccessor_ok, bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    exact effectiveKept_increase ok

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

theorem effectiveKept_withdrawals {f : Fork} {s t : BeaconState preset f}
    {capella : .shapella ≤ f} {payload : Until .glamsterdam f (ExecutionPayload preset f)}
    (ok : processWithdrawals s capella payload = .ok t) : EffectiveKept s t := by
  have applied {s t : BeaconState preset f} {expected : ExpectedWithdrawals}
      (ok : applyExpectedWithdrawals s capella expected = .ok t) : EffectiveKept s t := by
    unfold applyExpectedWithdrawals at ok
    simp only [bind_ok_iff] at ok
    obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := ok
    have one : EffectiveKept s applied := by
      unfold applyWithdrawals at appliedOk
      rw [← Array.foldlM_toList] at appliedOk
      refine effectiveKept_fold (fun _ _ _ ok => ?_)
        (fun _ _ _ ok => (registryLifecycle_applyWithdrawal ok).size_le) appliedOk
      unfold applyWithdrawal at ok
      split at ok
      · simp only [bind_ok_iff] at ok
        obtain ⟨_, _, set⟩ := ok
        obtain ⟨_, rfl⟩ := setBuilder_ok set
        exact effectiveKept_refl _
      · exact effectiveKept_decrease ok
    have indexedSame : indexed.validators = applied.validators := by
      unfold updateNextWithdrawalIndex at indexedOk
      split at indexedOk
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
        obtain ⟨_, _, rfl⟩ := indexedOk
        rfl
      · cases indexedOk; rfl
    have sweptSame : finished.validators = indexed.validators := by
      have swept {a : BeaconState preset f}
          (computed : (if gloas : .glamsterdam ≤ f then
            updateNextWithdrawalBuilderIndex a gloas expected.processedBuildersSweepCount
            else pure a) = .ok finished) : finished.validators = a.validators := by
        split at computed
        · unfold updateNextWithdrawalBuilderIndex at computed
          dsimp only at computed
          split at computed
          · cases computed; rfl
          · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
            obtain ⟨_, _, rfl⟩ := computed
            rfl
        · cases computed; rfl
      rw [swept sweptOk]
      split <;> (try split) <;> rfl
    have lastSame : t.validators = finished.validators := by
      unfold updateNextWithdrawalValidatorIndex at last
      simp only [bind_ok_iff] at last
      obtain ⟨_, _, last⟩ := last
      split at last
      · cases last
      · cases last; rfl
    intro i inside
    simpa only [effectiveAt, lastSame, sweptSame, indexedSame] using one i inside
  unfold processWithdrawals at ok
  split at ok
  · split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, appliedOk⟩ := ok
      exact applied appliedOk
    · cases ok; exact effectiveKept_refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, _, _, appliedOk⟩ := ok
    exact applied appliedOk

private theorem effectiveKept_sync {f : Fork} {s t : BeaconState preset f}
    {altair : .altair ≤ f} {aggregate : SyncAggregate preset}
    (ok : processSyncAggregate config checks s altair aggregate = .ok t) : EffectiveKept s t := by
  unfold processSyncAggregate at ok
  simp only [bind_ok_iff] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := ok
  rw [← Array.foldlM_toList] at folded
  refine effectiveKept_fold (fun _ _ _ ok => ?_)
    (fun _ _ _ ok => (frame_applySyncReward ok).registryGrows) folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    exact effectiveKept_trans (effectiveKept_increase raised) (effectiveKept_increase paid)
      (frame_increaseBalance raised).registryGrows
  · exact effectiveKept_decrease (liftAccessor_ok.mp ok)

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
    (ok : processVoluntaryExit config checks s signed = .ok t) : EffectiveKept s t := by
  unfold processVoluntaryExit at ok
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ok
  exact effectiveKept_exit exited

theorem effectiveKept_blsChange {f : Fork} {s t : BeaconState preset f}
    {signed : SignedBLSToExecutionChange}
    (ok : processBlsToExecutionChange config checks s signed = .ok t) : EffectiveKept s t := by
  obtain ⟨_, found, _, _, _, set⟩ := processBlsToExecutionChange_ok ok
  exact effectiveKept_setValidator found set rfl

private theorem effectiveKept_operations {f : Fork} {s t : BeaconState preset f}
    (early : f < .glamsterdam) {body : BeaconBlockBody preset f} {parentSlot : Slot}
    (ok : processOperations config checks s body parentSlot = .ok t) : EffectiveKept s t := by
  unfold processOperations at ok
  split at ok
  · rename_i later
    exact False.elim (Nat.not_le_of_lt early later)
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at ok
  obtain ⟨_, _, _, _, _, proposers, _, attesters, _, attestations, _, deposits, exited,
    exits, changed, changesOk, requestsOk⟩ := ok
  have changes : EffectiveKept exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact effectiveKept_fold (fun _ _ _ => effectiveKept_blsChange)
        (fun _ _ _ ok => (frame_processBlsToExecutionChange ok).registryGrows) changesOk
    · cases changesOk; exact effectiveKept_refl _
  have requests : EffectiveKept changed t := by
    split at requestsOk
    · exact effectiveKept_requests requestsOk
    · cases requestsOk; exact effectiveKept_refl _
  have compose {a b c : BeaconState preset f} (one : EffectiveKept a b)
      (two : EffectiveKept b c) (size : a.validators.data.size ≤ b.validators.data.size) :=
    effectiveKept_trans one two size
  apply compose (effectiveKept_fold (fun _ _ _ => effectiveKept_proposerSlashing)
    (fun _ _ _ ok => (frame_processProposerSlashing ok).registryGrows) proposers)
  · apply compose (effectiveKept_fold (fun _ _ _ => effectiveKept_attesterSlashing)
      (fun _ _ _ ok => (frame_processAttesterSlashing ok).registryGrows) attesters)
    · apply compose (effectiveKept_fold
        (fun _ _ _ ok => effectiveKept_data (by rw [(processAttestation_registry ok).1]))
        (fun _ _ _ ok => (frame_processAttestation ok).registryGrows) attestations)
      · apply compose (effectiveKept_fold (fun _ _ _ => effectiveKept_processDeposit)
          (fun _ _ _ ok => (frame_processDeposit ok).registryGrows) deposits)
        · apply compose (effectiveKept_fold (fun _ _ _ => effectiveKept_voluntaryExit)
            (fun _ _ _ ok => (frame_processVoluntaryExit ok).registryGrows) exits)
          · apply compose changes requests
            unfold processBlsToExecutionChanges at changesOk
            split at changesOk
            · rw [← Array.foldlM_toList] at changesOk
              exact (RegistryLifecycle.foldlM
                (fun _ _ _ ok => registryLifecycle_processBlsToExecutionChange ok)
                changesOk).size_le
            · cases changesOk; exact Nat.le_refl _
          · exact (RegistryLifecycle.foldlM
              (fun _ _ _ ok => registryLifecycle_processVoluntaryExit ok) exits).size_le
        · exact (RegistryLifecycle.foldlM
            (fun _ _ _ ok => registryLifecycle_processDeposit ok) deposits).size_le
      · exact (RegistryLifecycle.foldlM
          (fun _ _ _ ok => registryLifecycle_processAttestation ok) attestations).size_le
    · exact (RegistryLifecycle.foldlM
        (fun _ _ _ ok => registryLifecycle_processAttesterSlashing ok) attesters).size_le
  · exact (RegistryLifecycle.foldlM
      (fun _ _ _ ok => registryLifecycle_processProposerSlashing ok) proposers).size_le

/-- Before Gloas, a block keeps the effective balance of every existing validator. -/
theorem effectiveKept_block {f : Fork} {s t : BeaconState preset f}
    {engine : ExecutionEngine preset f} {block : BeaconBlock preset f}
    (early : f < .glamsterdam) (ok : processBlock config checks engine s block = .ok t) :
    EffectiveKept s t := by
  have header {a b : BeaconState preset f} {block : BeaconBlock preset f}
      (ok : processBlockHeader a block = .ok b) : b.validators = a.validators := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq ok
    rfl
  have randao {a b : BeaconState preset f} {body : BeaconBlockBody preset f}
      (ok : processRandao config checks a body = .ok b) : b.validators = a.validators := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq ok
    rfl
  have vote {a b : BeaconState preset f} {body : BeaconBlockBody preset f} {before : f < .hegota}
      (ok : processEth1Data before a body = .ok b) : b.validators = a.validators := by
    obtain ⟨_, _, rest⟩ := processEth1Data_eq ok
    rw [← rest]
  have execution {a b : BeaconState preset f} {body : BeaconBlockBody preset f}
      {bellatrix : .bellatrix ≤ f}
      (ok : processBlockExecution config checks engine a body bellatrix = .ok b) :
      EffectiveKept a b := by
    have payload {a b : BeaconState preset f} {bellatrix : .bellatrix ≤ f ∧ f < .glamsterdam}
        (ok : processExecutionPayload config engine a body bellatrix = .ok b) :
        b.validators = a.validators := by
      obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
      rfl
    unfold processBlockExecution at ok
    split at ok
    · exact False.elim (Nat.not_le_of_lt early (by assumption))
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, withdrawn, paid⟩ := ok
      intro i inside
      simpa only [effectiveAt, payload paid] using effectiveKept_withdrawals withdrawn i inside
    · dsimp only at ok
      split at ok
      · exact effectiveKept_data (congrArg (·.data) (payload ok))
      · cases ok; exact effectiveKept_refl _
  unfold processBlock at ok
  split at ok
  · unfold processBlockAltair at ok
    simp only [bind_ok_iff] at ok
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, operated, operatedOk, synced⟩ := ok
    have paidSame : paid = s := by
      split at paidOk
      · exact False.elim (Nat.not_le_of_lt early (by assumption))
      · cases paidOk; rfl
    subst paid
    have executionStep : EffectiveKept headed executed := by
      split at executedOk
      · exact execution executedOk
      · cases executedOk; exact effectiveKept_refl _
    have votedSame : voted.validators = revealed.validators := by
      split at votedOk
      · exact vote votedOk
      · cases votedOk; rfl
    have head : EffectiveKept s voted := by
      intro i inside
      have size : i < headed.validators.data.size := by simpa [header headedOk] using inside
      simpa only [effectiveAt, votedSame, randao revealedOk, header headedOk] using
        executionStep i size
    have grows := Nat.le_trans (frame_processBlockHeader headedOk).registryGrows
      ((by
        split at executedOk
        · exact (frame_processBlockExecution executedOk).registryGrows
        · cases executedOk; exact Nat.le_refl _) :
          headed.validators.data.size ≤ executed.validators.data.size)
    have grows' : s.validators.data.size ≤ voted.validators.data.size := by
      simpa [votedSame, randao revealedOk] using grows
    exact effectiveKept_trans head
      (effectiveKept_trans (effectiveKept_operations early operatedOk) (effectiveKept_sync synced)
        (frame_processOperations operatedOk).registryGrows) grows'
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, headed, _, revealed, _, voted, operated⟩ := ok
    intro i inside
    have kept := effectiveKept_operations early operated i
      (by simpa [vote voted, randao revealed, header headed] using inside)
    simpa only [effectiveAt, vote voted, randao revealed, header headed] using kept
end EthLib.Consensus
