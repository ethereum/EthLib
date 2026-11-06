module

public import EthLib.Consensus.Proofs.Transition.Operations
public import EthLib.Consensus.Transition.Requests

/-!
# Proofs: withdrawal and consolidation requests, and the pending consolidations

A withdrawal request and a consolidation request keep one balance for each validator.

The pending consolidations of an epoch keep the registry.

They move balance from one validator to another, so the sum of the balances stays.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {config : Config}
  {state after : BeaconState preset fork}

/-- A pass over the pending consolidations keeps the registry and the sum of the balances. -/
theorem passPendingConsolidations_kept {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork} {result},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      result.1.validators = state.validators ∧ balanceSum result.1 = balanceSum state
  | [], _, _, computed => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨rfl, rfl⟩
  | consolidation :: rest, state, result, computed => by
    unfold passPendingConsolidations at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
    split at computed
    · split at computed
      · cases computed
      rename_i recur
      cases computed
      exact (passPendingConsolidations_kept (consolidations := rest) recur :)
    split at computed
    · cases computed
      exact ⟨rfl, rfl⟩
    split at computed
    · cases computed
    rename_i balance found
    split at computed
    · cases computed
    rename_i lowered loweredOk
    split at computed
    · cases computed
    rename_i raised raisedOk
    split at computed
    · cases computed
    rename_i recur
    cases computed
    have lowered := liftAccessor_ok.mp loweredOk
    have raised := liftAccessor_ok.mp raisedOk
    obtain ⟨validators, summed⟩ := passPendingConsolidations_kept (consolidations := rest) recur
    refine ⟨validators.trans ((increaseBalance_validators raised).trans
      (decreaseBalance_validators lowered)), ?_⟩
    have taken := balanceSum_decreaseBalance (liftAccessor_ok.mp found) Std.min_le_left lowered
    have given := balanceSum_increaseBalance raised
    simp only at summed ⊢
    omega

/-- The pending consolidations of an epoch keep the registry and the sum of the balances. -/
theorem processPendingConsolidations_kept {electra : .pectra ≤ fork}
    (computed : processPendingConsolidations state electra = .ok after) :
    after.validators = state.validators ∧ balanceSum after = balanceSum state := by
  simp only [processPendingConsolidations, bind, Except.bind, pure, Except.pure] at computed
  split at computed
  · cases computed
  split at computed
  · cases computed
  rename_i passed
  cases computed
  exact passPendingConsolidations_kept passed

/-- A request for a partial withdrawal keeps the sizes of the registry and the balances. -/
theorem sameSizes_requestPartialWithdrawal {electra : .pectra ≤ fork} {index : ValidatorIndex}
    {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    SameSizes state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    obtain ⟨_, validators, balances⟩ := computeExitEpochAndUpdateChurn_earliest churned
    exact ⟨congrArg (·.data.size) validators, congrArg (·.data.size) balances⟩
  · cases computed
    exact SameSizes.refl _

/-- A withdrawal request keeps the sizes of the registry and the balances. -/
theorem sameSizes_processWithdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    SameSizes state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact SameSizes.refl _)
    | exact sameSizes_initiateValidatorExit (liftAccessor_ok.mp computed)
    | exact sameSizes_requestPartialWithdrawal computed

/-- Queueing a consolidation keeps the sizes of the registry and the balances. -/
theorem sameSizes_queueConsolidation {electra : .pectra ≤ fork} {sourcePosition : Nat}
    {source : Validator} {targetIndex : ValidatorIndex}
    (computed :
      queueConsolidation config state electra sourcePosition source targetIndex = .ok after) :
    SameSizes state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨⟨_, _⟩, churned, computed⟩ := computed
  simp only [Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  obtain ⟨_, validators, balances⟩ := computeConsolidationEpochAndUpdateChurn_earliest churned
  exact (SameSizes.trans ⟨congrArg (·.data.size) validators, congrArg (·.data.size) balances⟩
    (sameSizes_setValidator _ _ _))

/-- A consolidation request keeps the sizes of the registry and the balances. -/
theorem sameSizes_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    SameSizes state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact SameSizes.refl _)
    | exact (switchToCompoundingValidator_compounding (liftAccessor_ok.mp computed)).1
    | exact sameSizes_queueConsolidation computed

end EthLib.Consensus
