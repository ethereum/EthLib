module

public import EthLib.Base.Proofs.List
public import EthLib.Consensus.Proofs.PayloadTimeliness
public import EthLib.Consensus.Proofs.Transition.Operations
public import EthLib.Consensus.Transition.Requests

/-!
# Proofs: withdrawal and consolidation requests, and the pending consolidations

A withdrawal request and a consolidation request keep one balance for each validator.

So the operations of a block, with the requests from Electra, keep one balance for each validator.

The pending consolidations of an epoch keep the registry.

They move balance from one validator to another, so the sum of the balances stays.

From Electra, they drop the front of the queue before the first source that must wait.

A source must wait when it is unslashed and cannot withdraw in the next epoch.

They lower no balance of a validator that is slashed or cannot withdraw in the next epoch.

A source that is slashable in the next epoch keeps its consolidation and at least its balance.
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

/-- A pass leaves its list from the first source that is unslashed and cannot withdraw.

A source can withdraw when its withdrawable epoch is at most the epoch of the pass. -/
theorem passPendingConsolidations_drop {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork} {result},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      consolidations.drop result.2 = consolidations.dropWhile fun consolidation =>
        state.validators.data[consolidation.sourceIndex.toNat]?.any fun source =>
          source.slashed || source.withdrawableEpoch ≤ nextEpoch
  | [], _, _, computed => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    rfl
  | consolidation :: rest, state, result, computed => by
    unfold passPendingConsolidations at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
    rename_i source looked
    have read := getValidator_eq_ok_iff.mp (liftAccessor_ok.mp looked)
    split at computed
    · rename_i slashed
      split at computed
      · cases computed
      rename_i recur
      cases computed
      rw [List.drop_succ_cons, List.dropWhile_cons_of_pos (by simp [read, slashed])]
      exact passPendingConsolidations_drop recur
    rename_i unslashed
    split at computed
    · rename_i waiting
      cases computed
      have late : ¬source.withdrawableEpoch ≤ nextEpoch := UInt64.not_le.mpr waiting
      rw [List.drop_zero, List.dropWhile_cons_of_neg (by simp [read, unslashed, late])]
    rename_i ready
    split at computed
    · cases computed
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
    have same : raised.validators = state.validators :=
      (increaseBalance_validators (liftAccessor_ok.mp raisedOk)).trans
        (decreaseBalance_validators (liftAccessor_ok.mp loweredOk))
    have dropped := passPendingConsolidations_drop recur
    rw [same] at dropped
    have early : source.withdrawableEpoch ≤ nextEpoch := UInt64.not_lt.mp ready
    rw [List.drop_succ_cons, List.dropWhile_cons_of_pos (by simp [read, unslashed, early])]
    exact dropped

/-- A pass lowers no balance of a validator that is slashed or cannot withdraw at its epoch. -/
theorem balance_passPendingConsolidations {nextEpoch : Epoch} {j : Nat} {validator : Validator}
    (waiting : validator.slashed = true ∨ nextEpoch < validator.withdrawableEpoch) :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork} {result}
      {balance : Gwei},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      state.validators.data[j]? = some validator → state.balances.data[j]? = some balance →
      ∃ now, result.1.balances.data[j]? = some now ∧ balance.toNat ≤ now.toNat
  | [], _, _, _, computed, _, held => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨_, held, Nat.le_refl _⟩
  | consolidation :: rest, state, result, balance, computed, found, held => by
    unfold passPendingConsolidations at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
    rename_i source looked
    have read := getValidator_eq_ok_iff.mp (liftAccessor_ok.mp looked)
    split at computed
    · split at computed
      · cases computed
      rename_i recur
      cases computed
      exact (balance_passPendingConsolidations waiting recur found held :)
    rename_i unslashed
    split at computed
    · cases computed
      exact ⟨_, held, Nat.le_refl _⟩
    rename_i ready
    split at computed
    · cases computed
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
    have other : consolidation.sourceIndex.toNat ≠ j := by
      intro same
      rw [same, found, Option.some.injEq] at read
      subst read
      exact waiting.elim unslashed ready
    obtain ⟨kept, keptAt, keptEq⟩ := balance_decreaseBalance (liftAccessor_ok.mp loweredOk) held
    rw [ite_eq_right_of_eq_false _ _ (eq_false other)] at keptEq
    obtain ⟨grown, grownAt, grownEq⟩ := balance_increaseBalance (liftAccessor_ok.mp raisedOk) keptAt
    have same : raised.validators = state.validators :=
      (increaseBalance_validators (liftAccessor_ok.mp raisedOk)).trans
        (decreaseBalance_validators (liftAccessor_ok.mp loweredOk))
    obtain ⟨now, nowAt, rose⟩ :=
      balance_passPendingConsolidations waiting recur (by rw [same]; exact found) grownAt
    have up : kept.toNat ≤ grown.toNat := by
      rw [grownEq]
      exact Nat.le_add_right _ _
    exact ⟨now, nowAt, by omega⟩

/-- A step of the pending consolidations that succeeds runs one pass at the next epoch.

It keeps the balances of the pass, and the queue loses what the pass read. -/
theorem processPendingConsolidations_pass {electra : .pectra ≤ fork}
    (computed : processPendingConsolidations state electra = .ok after) :
    ∃ result, passPendingConsolidations (getCurrentEpoch state + 1) state
        (state.pendingConsolidations electra).data.toList = .ok result ∧
      after.balances = result.1.balances ∧
      (after.pendingConsolidations electra).data.toList =
        (state.pendingConsolidations electra).data.toList.drop result.2 := by
  simp only [processPendingConsolidations, bind, Except.bind, pure, Except.pure] at computed
  split at computed
  · cases computed
  rename_i nextEpoch next
  split at computed
  · cases computed
  rename_i passed
  cases computed
  -- The next epoch that the step computes is the wrapping sum, since the step succeeds.
  have added := liftAccessor_ok.mp next
  rw [liftArith, mapError_ok_iff, addChecked_ok_iff] at added
  obtain rfl := UInt64.toNat_inj.mp (added.2.trans (toNat_add_of_lt added.1).symm)
  refine ⟨_, passed, rfl, ?_⟩
  simp only [Array.toList_extract, List.extract_eq_take_drop]
  exact List.take_of_length_le (by simp)

/-- From Electra, take a step of the pending consolidations that succeeds.

The queue loses its longest front where each source is slashed or can withdraw in the next epoch. -/
theorem processPendingConsolidations_queue {electra : .pectra ≤ fork}
    (computed : processPendingConsolidations state electra = .ok after) :
    (after.pendingConsolidations electra).data.toList =
      (state.pendingConsolidations electra).data.toList.dropWhile fun consolidation =>
        state.validators.data[consolidation.sourceIndex.toNat]?.any fun source =>
          source.slashed || source.withdrawableEpoch ≤ getCurrentEpoch state + 1 := by
  obtain ⟨_, passed, -, queue⟩ := processPendingConsolidations_pass computed
  rw [queue]
  exact passPendingConsolidations_drop passed

/-- From Electra, take a step of the pending consolidations that succeeds.

It lowers no balance of a validator that is slashed or cannot withdraw in the next epoch. -/
theorem balance_processPendingConsolidations {electra : .pectra ≤ fork}
    (computed : processPendingConsolidations state electra = .ok after) {j : Nat}
    {validator : Validator} (found : state.validators.data[j]? = some validator)
    (waiting : validator.slashed = true ∨ getCurrentEpoch state + 1 < validator.withdrawableEpoch)
    {balance : Gwei} (held : state.balances.data[j]? = some balance) :
    ∃ now, after.balances.data[j]? = some now ∧ balance.toNat ≤ now.toNat := by
  obtain ⟨_, passed, balances, -⟩ := processPendingConsolidations_pass computed
  rw [balances]
  exact balance_passPendingConsolidations waiting passed found held

/-- From Electra, take a step of the pending consolidations that succeeds.

A consolidation whose source is slashable in the next epoch is still in the queue.

Its source keeps at least its balance. -/
theorem processPendingConsolidations_of_slashable {electra : .pectra ≤ fork}
    (computed : processPendingConsolidations state electra = .ok after)
    {consolidation : PendingConsolidation}
    (pending : consolidation ∈ (state.pendingConsolidations electra).data.toList)
    {source : Validator}
    (found : state.validators.data[consolidation.sourceIndex.toNat]? = some source)
    (slashable : isSlashableValidator source (getCurrentEpoch state + 1) = true) {balance : Gwei}
    (held : state.balances.data[consolidation.sourceIndex.toNat]? = some balance) :
    consolidation ∈ (after.pendingConsolidations electra).data.toList ∧
      ∃ now, after.balances.data[consolidation.sourceIndex.toNat]? = some now ∧
        balance.toNat ≤ now.toNat := by
  simp only [isSlashableValidator, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at slashable
  obtain ⟨⟨unslashed, -⟩, early⟩ := slashable
  refine ⟨?_, balance_processPendingConsolidations computed found (.inr early) held⟩
  rw [processPendingConsolidations_queue computed]
  have late : ¬source.withdrawableEpoch ≤ getCurrentEpoch state + 1 := UInt64.not_le.mpr early
  exact mem_dropWhile_of_eq_false (by simp [found, unslashed, late]) pending

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

/-- The checked index of a position of the registry names the validator at that position. -/
theorem getElem?_toNat_of_ofNatChecked {position : Fin state.validators.data.size}
    {index : ValidatorIndex}
    (checked : liftAccessor (liftArith (ofNatChecked position.val)) = .ok index) :
    state.validators.data[index.toNat]? = some state.validators.data[position] := by
  rw [liftAccessor_ok, liftArith, mapError_ok_iff] at checked
  rw [getElem?_toNat_eq_of_ofNatChecked checked]
  simp

/-- Queueing a consolidation keeps the sizes of the registry and the balances. -/
theorem sameSizes_queueConsolidation {electra : .pectra ≤ fork} {sourceIndex : ValidatorIndex}
    {source : Validator} {targetIndex : ValidatorIndex}
    (computed :
      queueConsolidation config state electra sourceIndex source targetIndex = .ok after) :
    SameSizes state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨⟨_, _⟩, churned, computed⟩ := computed
  simp only [Except.ok.injEq] at computed
  obtain ⟨_, _, _, set, _, _, rfl⟩ := computed
  obtain ⟨_, validators, balances⟩ := computeConsolidationEpochAndUpdateChurn_earliest churned
  exact (SameSizes.trans ⟨congrArg (·.data.size) validators, congrArg (·.data.size) balances⟩
    (sameSizes_setValidator set)).trans ⟨rfl, rfl⟩

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

/-! ## All the operations of a block -/

/-- The requests of the execution layer in a block keep the sizes of the registry and balances. -/
theorem sameSizes_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    SameSizes state after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨deposited, depositedOk, withdrawn, withdrawnOk, consolidated⟩ := computed
  have keep {α : Type} {step : BeaconState preset fork → α → Except TransitionError _}
      (sizes : ∀ s x s', step s x = .ok s' → SameSizes s s') {items : List α}
      {start finish : BeaconState preset fork} (folded : items.foldlM step start = .ok finish) :
      SameSizes start finish :=
    foldlM_ok_invariant (SameSizes start) (fun _ _ _ same ok => same.trans (sizes _ _ _ ok))
      (SameSizes.refl _) folded
  have requested := keep (fun _ _ _ ok =>
    ⟨congrArg (·.data.size) (processDepositRequest_ok ok).2.1,
      congrArg (·.data.size) (processDepositRequest_ok ok).2.2⟩) depositedOk
  exact requested.trans <|
    (keep (fun _ _ _ ok => sameSizes_processWithdrawalRequest ok) withdrawnOk).trans
      (keep (fun _ _ _ ok => sameSizes_processConsolidationRequest ok) consolidated)

/-- From Gloas, the operations of a block keep the sizes of the registry and the balances.

No deposit runs there, and a payload attestation changes nothing. -/
theorem sameSizes_processOperationsGloas {body : BeaconBlockBody preset fork}
    {gloas : .glamsterdam ≤ fork} {parentSlot : Slot}
    (computed : processOperationsGloas config checks state body gloas parentSlot = .ok after) :
    SameSizes state after := by
  unfold processOperationsGloas at computed
  simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, proposers, proposersOk, attesters,
    attestersOk, attested, attestedOk, exited, exitsOk, changed, changesOk, paid⟩ := computed
  have keep {α : Type} {step : BeaconState preset fork → α → Except TransitionError _}
      (sizes : ∀ s x s', step s x = .ok s' → SameSizes s s') {items : List α}
      {start finish : BeaconState preset fork} (folded : items.foldlM step start = .ok finish) :
      SameSizes start finish :=
    foldlM_ok_invariant (SameSizes start) (fun _ _ _ same ok => same.trans (sizes _ _ _ ok))
      (SameSizes.refl _) folded
  exact (keep (fun _ _ _ ok => sameSizes_processProposerSlashing ok) proposersOk).trans <|
    (keep (fun _ _ _ ok => sameSizes_processAttesterSlashing ok) attestersOk).trans <|
    (keep (fun _ _ _ ok => sameSizes_processAttestation ok) attestedOk).trans <|
    (keep (fun _ _ _ ok => sameSizes_processVoluntaryExit ok) exitsOk).trans <|
    (keep (fun _ _ _ ok => sameSizes_processBlsToExecutionChange ok) changesOk).trans <|
    keep (fun _ _ _ ok => processPayloadAttestation_eq ok ▸ SameSizes.refl _) paid

/-- The operations of a block keep one balance for each validator. -/
theorem balancesMatch_processOperations {checks : SignatureChecks}
    {body : BeaconBlockBody preset fork}
    {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after)
    (holds : BalancesMatch state) : BalancesMatch after := by
  unfold processOperations at computed
  split at computed
  · exact balancesMatch_of_sameSizes (sameSizes_processOperationsGloas computed) holds
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, proposers, proposersOk, attesters, attestersOk, attested, attestedOk,
    deposited, depositedOk, exited, exitsOk, changed, changesOk, requestsOk⟩ := computed
  have keep {α : Type} (step : BeaconState preset fork → α → Except TransitionError _)
      (sizes : ∀ s x s', step s x = .ok s' → SameSizes s s') :=
    fun s x s' (h : BalancesMatch s) ok => balancesMatch_of_sameSizes (sizes s x s' ok) h
  have one := foldlM_ok_invariant BalancesMatch
    (keep _ fun _ _ _ ok => sameSizes_processProposerSlashing ok) holds proposersOk
  have two := foldlM_ok_invariant BalancesMatch
    (keep _ fun _ _ _ ok => sameSizes_processAttesterSlashing ok) one attestersOk
  have three := foldlM_ok_invariant BalancesMatch
    (keep _ fun _ _ _ ok => sameSizes_processAttestation ok) two attestedOk
  have four := foldlM_ok_invariant BalancesMatch
    (fun _ _ _ h ok => balancesMatch_processDeposit ok h) three depositedOk
  have five := foldlM_ok_invariant BalancesMatch
    (keep _ fun _ _ _ ok => sameSizes_processVoluntaryExit ok) four exitsOk
  have six : BalancesMatch changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact foldlM_ok_invariant BalancesMatch
        (keep _ fun _ _ _ ok => sameSizes_processBlsToExecutionChange ok) five changesOk
    · cases changesOk
      exact five
  split at requestsOk
  · exact balancesMatch_of_sameSizes (sameSizes_processExecutionRequests requestsOk) six
  · cases requestsOk
    exact six

end EthLib.Consensus
