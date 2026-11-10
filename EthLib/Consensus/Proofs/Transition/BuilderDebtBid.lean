module

public import EthLib.Consensus.Proofs.Transition.BuilderDebtSlots
public import EthLib.Consensus.Proofs.Transition.BuilderRequests
public import EthLib.Consensus.Proofs.Transition.PayloadInputs

/-!
# Proofs: from the parent payload to the bid, a block keeps each builder's debt covered

A block of Gloas first applies the payload of its parent, then runs its header.

Its withdrawals follow, then its bid.

Between the payment of the parent and the bid, the invariant of the builder debt has a weaker form.

* For each builder, the debt is at most the balance.
* A builder that has started to exit owes nothing.
* From the position of the slot of the state, each position of the window is empty.

The reserve of the late path is no longer needed in that form.

On a full parent, the late path has queued the value of the parent bid, or the payment has settled.

On an empty parent, the payload of the parent never pays, and its bid is about to be replaced.

The bid then restores the invariant.

Its builder can cover its value, its debt and a minimum, and the position of its slot was empty.

So the bid becomes the payment of the latest block, with no weight.

[EIP-7732] adds the payload of the parent and the bid of a block.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- From Gloas, inside a block: the balance of each builder covers its debt.

A builder that has started to exit owes nothing.

Each position from that of the slot of the state, in the second half of the window, is empty. -/
structure BuilderDebtSettled (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) :
    Prop where
  covered : ∀ index, pendingBuilderTotal state gloas index ≤ builderBalance state gloas index
  exitedClear : ∀ index builder, (state.builders gloas).data[index.toNat]? = some builder →
    builder.withdrawableEpoch ≠ FAR_FUTURE_EPOCH → pendingBuilderTotal state gloas index = 0
  laterEmpty : ∀ position,
    preset.SLOTS_PER_EPOCH.toNat + state.slot.toNat % preset.SLOTS_PER_EPOCH.toNat ≤ position →
      paymentAt state gloas position = .empty

/-- A step that keeps the slot, the builders, their payments and their withdrawals keeps the form.
-/
theorem BuilderDebtSettled.of_eq {gloas : .glamsterdam ≤ fork} (slot : after.slot = state.slot)
    (builders : after.builders = state.builders)
    (payments : after.builderPendingPayments = state.builderPendingPayments)
    (withdrawals : after.builderPendingWithdrawals = state.builderPendingWithdrawals)
    (holds : BuilderDebtSettled state gloas) : BuilderDebtSettled after gloas := by
  have total : ∀ index,
      pendingBuilderTotal after gloas index = pendingBuilderTotal state gloas index :=
    fun _ => by simp only [pendingBuilderTotal, payments, withdrawals]
  refine ⟨fun index => ?_, fun index builder found exited => ?_, fun k later => ?_⟩
  · simpa only [total, builderBalance, builders] using holds.covered index
  · rw [total]
    exact holds.exitedClear index builder (by rwa [builders] at found) exited
  · simpa only [paymentAt, payments] using holds.laterEmpty k (by rwa [slot] at later)

/-! ## The payload of the parent -/

/-- Below a newer slot, the parent payment sits before each position from that of the slot. -/
private theorem parentPaymentPosition_lt (newer : state.latestBlockHeader.slot < state.slot)
    {position : Nat}
    (later : preset.SLOTS_PER_EPOCH.toNat + state.slot.toNat % preset.SLOTS_PER_EPOCH.toNat ≤
      position) (parent : UInt64) (found : parentPaymentPosition state = some parent) :
    parent.toNat < position := by
  have lt := UInt64.lt_iff_toNat_lt.mp newer
  unfold parentPaymentPosition slotPaymentPosition getPreviousEpoch getCurrentEpoch
    computeEpochAtSlot at found
  dsimp only at found
  split at found
  · rename_i same
    cases found
    have same := congrArg UInt64.toNat same
    simp only [UInt64.toNat_div] at same
    have wrap := Nat.mod_le (preset.SLOTS_PER_EPOCH.toNat +
      (state.latestBlockHeader.slot % preset.SLOTS_PER_EPOCH).toNat) (2 ^ 64)
    rw [UInt64.toNat_add, UInt64.toNat_mod]
    rw [UInt64.toNat_mod] at wrap
    have parentSplit := Nat.div_add_mod state.latestBlockHeader.slot.toNat
      preset.SLOTS_PER_EPOCH.toNat
    have slotSplit := Nat.div_add_mod state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    rw [same] at parentSplit
    omega
  · split at found
    · cases found
      rw [UInt64.toNat_mod]
      rcases Nat.eq_zero_or_pos preset.SLOTS_PER_EPOCH.toNat with zero | pos
      · simp only [zero, Nat.mod_zero, Nat.zero_add] at later ⊢
        omega
      · have := Nat.mod_lt state.latestBlockHeader.slot.toNat pos
        omega
    · cases found

/-- The invariant gives the form inside a block to a step that adds at most the reserve.

The step must keep the slot and the builders, and must not fill a position after the parent. -/
private theorem BuilderDebtCovered.toSettled {gloas : .glamsterdam ≤ fork}
    (holds : BuilderDebtCovered state gloas) (newer : state.latestBlockHeader.slot < state.slot)
    (slot : after.slot = state.slot) (builders : after.builders = state.builders)
    (total : ∀ index, pendingBuilderTotal after gloas index ≤
      pendingBuilderTotal state gloas index + lateBidValue state gloas index)
    (later : ∀ position,
      (∀ parent, parentPaymentPosition state = some parent → parent.toNat < position) →
        paymentAt state gloas position = .empty → paymentAt after gloas position = .empty) :
    BuilderDebtSettled after gloas := by
  have balance : ∀ index, builderBalance after gloas index = builderBalance state gloas index :=
    fun _ => by simp only [builderBalance, builders]
  refine ⟨fun index => ?_, fun index builder found exited => ?_, fun position past => ?_⟩
  · rw [balance]
    exact Nat.le_trans (total index) (holds.covered index)
  · have := holds.exitedClear index builder (by rwa [builders] at found) exited
    have := total index
    omega
  · rw [slot] at past
    have before := parentPaymentPosition_lt newer past
    exact later position before (holds.laterEmpty position before)

/-- The payment of the parent gives the form inside a block. -/
private theorem BuilderDebtCovered.settleParentPayment {gloas : .glamsterdam ≤ fork}
    (holds : BuilderDebtCovered state gloas) (newer : state.latestBlockHeader.slot < state.slot)
    (computed : settleParentPayment state gloas = .ok after) : BuilderDebtSettled after gloas := by
  have builders := settleParentPayment_builders computed
  have slot := (payloadInputs_settleParentPayment computed).slot
  unfold Consensus.settleParentPayment at computed
  split at computed
  · rename_i parent found
    have settled := liftAccessor_ok.mp computed
    obtain ⟨_, payments, -⟩ := settleBuilderPayment_spec settled
    refine holds.toSettled newer slot builders (fun index => ?_) fun position before empty => ?_
    · rw [pendingBuilderTotal_settleBuilderPayment settled]
      exact Nat.le_add_right _ _
    · have := before parent found
      rw [paymentAt_set payments, ite_eq_right (by omega)]
      exact empty
  · rename_i found
    dsimp only at computed
    split at computed
    · cases computed
      refine holds.toSettled newer rfl rfl (fun index => ?_) fun _ _ empty => empty
      have opened : latePaymentOpen state gloas = true := by
        simp only [latePaymentOpen, found]
      simp only [pendingBuilderTotal, lateBidValue, opened, and_true, Array.toList_push,
        owedBy_append]
      split <;> simp_all [owedBy] <;> omega
    · cases computed
      exact holds.toSettled newer rfl rfl (fun _ => Nat.le_add_right _ _) fun _ _ empty => empty

/-- The payment of the parent keeps each pending payment, or empties it. -/
theorem paymentAt_settleParentPayment {gloas : .glamsterdam ≤ fork}
    (computed : settleParentPayment state gloas = .ok after) (position : Nat) :
    paymentAt after gloas position = paymentAt state gloas position ∨
      paymentAt after gloas position = .empty := by
  unfold Consensus.settleParentPayment at computed
  split at computed
  · obtain ⟨_, payments, -⟩ := settleBuilderPayment_spec (liftAccessor_ok.mp computed)
    rw [paymentAt_set payments]
    split
    · exact .inr rfl
    · exact .inl rfl
  · dsimp only at computed
    split at computed <;> cases computed <;> exact .inl rfl

/-! ## The requests of the parent payload -/

/-- A deposit request keeps the builder fields and the two slots. -/
theorem builderFrame_processDepositRequest {electra : .pectra ≤ fork}
    {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    BuilderFrame state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem builderFrame_requestPartialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    BuilderFrame state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churned
    obtain ⟨_, _, _, _, _, _, churned⟩ := churned
    cases churned
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases computed
    exact BuilderFrame.refl _

/-- A withdrawal request keeps the builder fields and the two slots. -/
theorem builderFrame_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    BuilderFrame state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact BuilderFrame.refl _)
    | exact builderFrame_initiateValidatorExit (liftAccessor_ok.mp computed)
    | exact builderFrame_requestPartialWithdrawal computed

private theorem builderFrame_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    BuilderFrame state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨_, _, _, set, queued⟩ := computed
  refine (builderFrame_setValidator set).trans ?_
  simp only [queueExcessActiveBalance, bind_ok_iff] at queued
  obtain ⟨_, _, queued⟩ := queued
  split at queued
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
    obtain ⟨_, _, _, _, _, set, rfl⟩ := queued
    exact (builderFrame_setBalance set).trans ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases queued
    exact BuilderFrame.refl _

private theorem builderFrame_queueConsolidation {electra : .pectra ≤ fork}
    {sourceIndex : ValidatorIndex} {source : Validator} {targetIndex : ValidatorIndex}
    (computed :
      queueConsolidation config state electra sourceIndex source targetIndex = .ok after) :
    BuilderFrame state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure] at computed
  obtain ⟨⟨_, _⟩, churned, _, _, _, set, _, _, computed⟩ := computed
  simp only [Except.ok.injEq] at computed
  subst computed
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at churned
  obtain ⟨_, _, _, _, _, _, churned⟩ := churned
  cases churned
  refine (BuilderFrame.trans ?_ (builderFrame_setValidator set)).trans ?_ <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A consolidation request keeps the builder fields and the two slots. -/
theorem builderFrame_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    BuilderFrame state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact BuilderFrame.refl _)
    | exact builderFrame_switchToCompoundingValidator (liftAccessor_ok.mp computed)
    | exact builderFrame_queueConsolidation computed

/-- The deposit, withdrawal and consolidation requests of validators run in turn.

They keep the builder fields and the two slots. -/
theorem builderFrame_validatorRequests {electra : .pectra ≤ fork}
    {deposits : List DepositRequest} {withdrawals : List WithdrawalRequest}
    {consolidations : List ConsolidationRequest} {deposited withdrawn : BeaconState preset fork}
    (depositsOk : deposits.foldlM (processDepositRequest · electra ·) state = .ok deposited)
    (withdrawalsOk : withdrawals.foldlM (processWithdrawalRequest config · electra ·) deposited =
      .ok withdrawn)
    (consolidationsOk :
      consolidations.foldlM (processConsolidationRequest config · electra ·) withdrawn =
        .ok after) :
    BuilderFrame state after :=
  (BuilderFrame.foldlM (fun _ _ _ ok => builderFrame_processDepositRequest ok)
      depositsOk).trans <|
    (BuilderFrame.foldlM (fun _ _ _ ok => builderFrame_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    BuilderFrame.foldlM (fun _ _ _ ok => builderFrame_processConsolidationRequest ok)
      consolidationsOk

/-- The builder deposit and exit requests run in turn.

They keep the slot, the payments, the withdrawals of builders and the latest bid. -/
theorem builderRequests_paymentFields {gloas : .glamsterdam ≤ fork}
    {deposits : List BuilderDepositRequest} {exits : List BuilderExitRequest}
    {deposited : BeaconState preset fork}
    (depositsOk : deposits.foldlM (processBuilderDepositRequest config checks · gloas ·) state =
      .ok deposited)
    (exitsOk : exits.foldlM (processBuilderExitRequest config · gloas ·) deposited = .ok after) :
    after.slot = state.slot ∧ after.builderPendingPayments = state.builderPendingPayments ∧
      after.builderPendingWithdrawals = state.builderPendingWithdrawals ∧
      after.latestExecutionPayloadBid = state.latestExecutionPayloadBid := by
  have kept := foldlM_ok_invariant (fun s => s.slot = state.slot ∧
      s.builderPendingPayments = state.builderPendingPayments ∧
      s.builderPendingWithdrawals = state.builderPendingWithdrawals ∧
      s.latestExecutionPayloadBid = state.latestExecutionPayloadBid)
    (fun _ _ _ before ok => by
      obtain ⟨_, rfl⟩ := processBuilderDepositRequest_eq ok
      exact before) ⟨rfl, rfl, rfl, rfl⟩ depositsOk
  exact foldlM_ok_invariant (fun s => s.slot = state.slot ∧
      s.builderPendingPayments = state.builderPendingPayments ∧
      s.builderPendingWithdrawals = state.builderPendingWithdrawals ∧
      s.latestExecutionPayloadBid = state.latestExecutionPayloadBid)
    (fun _ _ _ before ok => by
      obtain ⟨_, rfl⟩ := processBuilderExitRequest_eq ok
      exact before) kept exitsOk

/-- A step that only changes the builders keeps the form, if each builder keeps its bounds.

A builder that owes something keeps at least its balance, and its exit once it has started.

The registry must not shrink. -/
private theorem BuilderDebtSettled.of_builders {gloas : .glamsterdam ≤ fork}
    (slot : after.slot = state.slot)
    (payments : after.builderPendingPayments = state.builderPendingPayments)
    (withdrawals : after.builderPendingWithdrawals = state.builderPendingWithdrawals)
    (grows : (state.builders gloas).data.size ≤ (after.builders gloas).data.size)
    (each : ∀ index : BuilderIndex, pendingBuilderTotal state gloas index = 0 ∨
      ∀ old builder, (state.builders gloas).data[index.toNat]? = some old →
        (after.builders gloas).data[index.toNat]? = some builder →
        old.balance.toNat ≤ builder.balance.toNat ∧
          (builder.withdrawableEpoch ≠ FAR_FUTURE_EPOCH →
            old.withdrawableEpoch ≠ FAR_FUTURE_EPOCH))
    (holds : BuilderDebtSettled state gloas) : BuilderDebtSettled after gloas := by
  have total : ∀ index,
      pendingBuilderTotal after gloas index = pendingBuilderTotal state gloas index :=
    fun _ => by simp only [pendingBuilderTotal, payments, withdrawals]
  -- A builder past the old registry owed nothing.
  have absent : ∀ index : BuilderIndex, (state.builders gloas).data[index.toNat]? = none →
      pendingBuilderTotal state gloas index = 0 := by
    intro index none
    have := holds.covered index
    simp only [builderBalance, none] at this
    omega
  refine ⟨fun index => ?_, fun index builder found exited => ?_, fun k later => ?_⟩
  · rw [total]
    rcases each index with zero | kept
    · omega
    cases old : (state.builders gloas).data[index.toNat]? with
    | none => rw [absent index old]; exact Nat.zero_le _
    | some old' =>
      cases new : (after.builders gloas).data[index.toNat]? with
      | none =>
        rw [Array.getElem?_eq_none_iff] at new
        have := (Array.getElem?_eq_some_iff.mp old).1
        omega
      | some new' =>
        have := holds.covered index
        simp only [builderBalance, old, new] at this ⊢
        exact Nat.le_trans this (kept old' new' old new).1
  · rw [total]
    rcases each index with zero | kept
    · exact zero
    cases old : (state.builders gloas).data[index.toNat]? with
    | none => exact absent index old
    | some old' => exact holds.exitedClear index old' old ((kept old' builder old found).2 exited)
  · simpa only [paymentAt, payments] using holds.laterEmpty k (by rwa [slot] at later)

/-- A builder written at one position leaves the builder at each other position. -/
private theorem builders_putBuilder {gloas : .glamsterdam ≤ fork} {k : Nat}
    {inside : k < (state.builders gloas).data.size} {builder : Builder} (position : Nat) :
    ((state.putBuilder gloas k inside builder).builders gloas).data[position]? =
      if k = position then some builder else (state.builders gloas).data[position]? := by
  simp [BeaconState.putBuilder, Array.getElem?_set]

/-- An exit request keeps the form: only a builder that owes nothing starts to exit. -/
private theorem BuilderDebtSettled.processBuilderExitRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest} (holds : BuilderDebtSettled state gloas)
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    BuilderDebtSettled after gloas := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨found, _, _, _, pending, exited⟩
  · exact holds
  have zero := (getPendingBalanceToWithdrawForBuilder_ok_iff.mp pending).2
  simp only [initiateBuilderExit, bind_ok_iff] at exited
  obtain ⟨_, _, _, _, set⟩ := exited
  obtain ⟨_, rfl⟩ := setBuilder_ok set
  refine BuilderDebtSettled.of_builders (state := state) rfl rfl rfl
    (by simp [BeaconState.putBuilder]) (fun index => ?_) holds
  by_cases same : index = found.val.toUInt64
  · subst same
    exact .inl (by simpa using zero.symm)
  · refine .inr fun old builder before now => ?_
    have differ : found.val.toUInt64.toNat ≠ index.toNat := fun equal =>
      same (UInt64.toNat_inj.mp equal).symm
    simp only [builders_putBuilder, differ, ↓reduceIte, before] at now
    cases now
    exact ⟨Nat.le_refl _, id⟩

/-- A builder written with at least its old balance keeps the form.

It may have started to exit only if the old builder had. -/
private theorem BuilderDebtSettled.putBuilder {gloas : .glamsterdam ≤ fork} {k : Nat}
    {inside : k < (state.builders gloas).data.size} {builder : Builder}
    (balance : ((state.builders gloas).data[k]).balance.toNat ≤ builder.balance.toNat)
    (exit : builder.withdrawableEpoch ≠ FAR_FUTURE_EPOCH →
      ((state.builders gloas).data[k]).withdrawableEpoch ≠ FAR_FUTURE_EPOCH)
    (holds : BuilderDebtSettled state gloas) :
    BuilderDebtSettled (state.putBuilder gloas k inside builder) gloas := by
  refine BuilderDebtSettled.of_builders (state := state) rfl rfl rfl
    (by simp [BeaconState.putBuilder]) (fun index => .inr fun old new before now => ?_) holds
  rw [builders_putBuilder] at now
  split at now
  · rename_i same
    subst same
    rw [Array.getElem?_eq_getElem inside] at before
    cases before
    cases now
    exact ⟨balance, exit⟩
  · rw [before] at now
    cases now
    exact ⟨Nat.le_refl _, id⟩

/-- A builder added at the end of the registry keeps the form. -/
private theorem BuilderDebtSettled.pushBuilder {gloas : .glamsterdam ≤ fork} {builder : Builder}
    (holds : BuilderDebtSettled state gloas) :
    BuilderDebtSettled
      { state with builders := fun _ => ⟨(state.builders gloas).data.push builder⟩ } gloas := by
  refine BuilderDebtSettled.of_builders (state := state) rfl rfl rfl
    (by simp) (fun index => .inr fun old new before now => ?_) holds
  simp only [Array.getElem?_push] at now
  split at now
  · rename_i same
    rw [same, Array.getElem?_eq_none_iff.mpr (Nat.le_refl _)] at before
    cases before
  · rw [before] at now
    cases now
    exact ⟨Nat.le_refl _, id⟩

/-- A builder deposit keeps the form.

It raises a balance, or registers a builder at an index that owes nothing. -/
private theorem BuilderDebtSettled.processBuilderDepositRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderDepositRequest} (holds : BuilderDebtSettled state gloas)
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    BuilderDebtSettled after gloas := by
  unfold Consensus.processBuilderDepositRequest at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ holds
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      unfold addBuilderToRegistry
      dsimp only
      split
      · rename_i inside
        have reusable := isReusableBuilder_of_getIndexForNewBuilder_lt inside
        simp only [isReusableBuilder, Bool.and_eq_true, beq_iff_eq] at reusable
        exact holds.putBuilder (by simp [reusable.2]) fun far => absurd rfl far
      · exact holds.pushBuilder
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ holds
  · dsimp only at computed
    split at computed
    all_goals
      simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
        Uint64.addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    · rename_i exited
      obtain ⟨_, _, _, ⟨_, sum⟩, rfl⟩ := computed
      exact holds.putBuilder (by simp only [Fin.getElem_fin] at sum ⊢; omega) fun _ => exited.1
    · obtain ⟨_, rfl, _, ⟨_, sum⟩, rfl⟩ := computed
      exact holds.putBuilder (by simp only [Fin.getElem_fin] at sum ⊢; omega) id

/-- From Gloas, the payload of the parent turns the invariant into its form inside a block.

The latest block must be older than the slot of the state, as the header of the block requires. -/
theorem BuilderDebtCovered.processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork} (holds : BuilderDebtCovered state gloas)
    (newer : state.latestBlockHeader.slot < state.slot)
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    BuilderDebtSettled after gloas := by
  rcases processParentExecutionPayload_ok computed with ⟨-, -, rfl⟩ |
    ⟨-, settled, _, _, _, _, requested, _, settledOk, depositsOk, withdrawalsOk,
      consolidationsOk, buildersOk, exitsOk, -, rfl⟩
  · -- An empty parent leaves the state as it is.
    exact holds.toSettled newer rfl rfl (fun _ => Nat.le_add_right _ _) fun _ _ empty => empty
  -- The requests of validators keep the builder fields.
  have frame := builderFrame_validatorRequests depositsOk withdrawalsOk consolidationsOk
  have paid := holds.settleParentPayment newer settledOk
  have validators := BuilderDebtSettled.of_eq (state := settled) frame.slot frame.builders
    frame.payments frame.withdrawals paid
  have deposited := foldlM_ok_invariant (fun s => BuilderDebtSettled s gloas)
    (fun _ _ _ before ok => before.processBuilderDepositRequest ok) validators buildersOk
  have exited := foldlM_ok_invariant (fun s => BuilderDebtSettled s gloas)
    (fun _ _ _ before ok => before.processBuilderExitRequest ok) deposited exitsOk
  exact BuilderDebtSettled.of_eq (state := requested) rfl rfl rfl rfl exited

/-! ## The header -/

/-- The header of a block keeps the form inside a block, and puts the latest block at the slot. -/
theorem BuilderDebtSettled.processBlockHeader {gloas : .glamsterdam ≤ fork}
    {block : BeaconBlock preset fork} (holds : BuilderDebtSettled state gloas)
    (computed : processBlockHeader state block = .ok after) :
    BuilderDebtSettled after gloas ∧ after.latestBlockHeader.slot = after.slot := by
  have slot : block.slot = state.slot := by
    simp only [Consensus.processBlockHeader, bind_ok_iff, ensure_ok_iff] at computed
    obtain ⟨_, same, _⟩ := computed
    exact same
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact ⟨BuilderDebtSettled.of_eq (state := state) rfl rfl rfl rfl holds, slot⟩

/-! ## The bid -/

/-- A bid with a value, recorded at the empty position of the parent, restores the invariant.

Its builder has not started to exit, and its balance covers its debt and the value. -/
private theorem BuilderDebtSettled.recordBid {gloas : .glamsterdam ≤ fork}
    {bid : ExecutionPayloadBid preset fork} {proposer : ValidatorIndex} {builder : Builder}
    {parent : UInt64} {place : Fin (2 * preset.SLOTS_PER_EPOCH.toNat)}
    (holds : BuilderDebtSettled state gloas) (paid : 0 < bid.value)
    (placed : place.val =
      preset.SLOTS_PER_EPOCH.toNat + state.slot.toNat % preset.SLOTS_PER_EPOCH.toNat)
    (stored : (state.builders gloas).data[bid.builderIndex.toNat]? = some builder)
    (far : builder.withdrawableEpoch = FAR_FUTURE_EPOCH)
    (enough : pendingBuilderTotal state gloas bid.builderIndex + bid.value.toNat ≤
      builder.balance.toNat)
    (latest : after.latestExecutionPayloadBid gloas = bid)
    (builders : after.builders = state.builders)
    (withdrawals : after.builderPendingWithdrawals = state.builderPendingWithdrawals)
    (payments : after.builderPendingPayments gloas =
      (state.builderPendingPayments gloas).set place (bidPayment bid proposer))
    (found : parentPaymentPosition after = some parent) (parentAt : parent.toNat = place.val) :
    BuilderDebtCovered after gloas := by
  have empty := holds.laterEmpty place (Nat.le_of_eq placed.symm)
  have recorded : paymentAt after gloas place = bidPayment bid proposer := by
    rw [paymentAt_set payments, ite_eq_left rfl]
  -- The payment of the bid owes its value, at a position that owed nothing.
  have total : ∀ index, pendingBuilderTotal after gloas index =
      pendingBuilderTotal state gloas index +
        owedBy index [(bidPayment bid proposer).withdrawal] := by
    intro index
    have moved := owedBy_set (index := index)
      (withdrawals := (state.builderPendingPayments gloas).elements.toList.map (·.withdrawal))
      (k := place) (by simp) (bidPayment bid proposer).withdrawal
    rw [paymentAt_of_lt place.isLt] at empty
    have read : (state.builderPendingPayments gloas)[place.val] =
        (state.builderPendingPayments gloas).elements[place.val] := rfl
    simp only [List.getElem_map, Vector.getElem_toList, ← read, empty] at moved
    unfold pendingBuilderTotal
    rw [withdrawals, payments, Serialization.Ssz.RootedVector.elements_set, Vector.toList_set,
      List.map_set]
    simp only [owedBy, BuilderPendingPayment.empty, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, UInt64.toNat_zero, ite_self] at moved ⊢
    omega
  have owe : ∀ index, owedBy index [(bidPayment bid proposer).withdrawal] =
      if bid.builderIndex = index then bid.value.toNat else 0 :=
    fun _ => by simp [owedBy, bidPayment]
  -- The parent payment now has an amount, so the reserve is closed.
  have late : ∀ index, lateBidValue after gloas index = 0 := by
    intro index
    have positive : bid.value.toNat ≠ 0 := by
      have := UInt64.lt_iff_toNat_lt.mp paid
      simp only [UInt64.toNat_zero] at this
      omega
    have closed : latePaymentOpen after gloas = false := by
      simp only [latePaymentOpen, found, parentAt, recorded, bidPayment, beq_eq_false_iff_ne,
        ne_eq]
      exact fun zero => positive (by rw [zero]; rfl)
    simp [lateBidValue, closed]
  have balance : ∀ index, builderBalance after gloas index = builderBalance state gloas index :=
    fun _ => by simp only [builderBalance, builders]
  refine ⟨fun index => ?_, fun index other present exited => ?_, fun position kept => ?_,
    fun k past => ?_⟩
  · rw [late, total, owe, Nat.add_zero, balance]
    by_cases same : bid.builderIndex = index
    · subst same
      simp only [↓reduceIte, builderBalance, stored]
      omega
    · simp only [same, ↓reduceIte, Nat.add_zero]
      exact holds.covered index
  · rw [late, total, owe, Nat.add_zero]
    rw [builders] at present
    by_cases same : bid.builderIndex = index
    · subst same
      rw [stored, Option.some.injEq] at present
      exact absurd (present ▸ far) exited
    · simp only [same, ↓reduceIte, Nat.add_zero]
      exact holds.exitedClear index other present exited
  · have same : position = parent := Option.some.inj (kept.symm.trans found)
    subst same
    rw [parentAt, recorded]
    exact ⟨rfl, .inr (by rw [latestBidWithdrawal, latest]; rfl)⟩
  · have := past parent found
    rw [paymentAt_set payments, ite_eq_right (by omega)]
    exact holds.laterEmpty k (by omega)

/-- From Gloas, the bid of a block restores the builder debt invariant.

The latest block must be at the slot of the state, as after the header of the block.

The preset needs a payment quorum of at least one gwei.

An epoch then has a slot, and the window fits in 64 bits. -/
theorem BuilderDebtSettled.processExecutionPayloadBid (positive : preset.PaymentQuorumPositive)
    {gloas : .glamsterdam ≤ fork} {signed : SignedExecutionPayloadBid preset fork}
    (holds : BuilderDebtSettled state gloas)
    (header : state.latestBlockHeader.slot = state.slot)
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    BuilderDebtCovered after gloas := by
  obtain ⟨checked, recorded, recordOk, rfl⟩ := processExecutionPayloadBid_ok computed
  obtain ⟨builderOk, -, slotEq, -⟩ := checkExecutionPayloadBid_ok_iff.mp checked
  obtain ⟨one, fits⟩ := positive.slotsPerEpoch_bounds
  -- The parent payment sits at the position of the slot in the second half of the window.
  have mod := UInt64.toNat_mod state.slot preset.SLOTS_PER_EPOCH
  have small := Nat.mod_lt state.slot.toNat (Nat.lt_of_lt_of_le Nat.zero_lt_one one)
  have position : (preset.SLOTS_PER_EPOCH + state.slot % preset.SLOTS_PER_EPOCH).toNat =
      preset.SLOTS_PER_EPOCH.toNat + state.slot.toNat % preset.SLOTS_PER_EPOCH.toNat := by
    rw [UInt64.toNat_add, mod]
    exact Nat.mod_eq_of_lt (by omega)
  have parentAt : parentPaymentPosition state =
      some (preset.SLOTS_PER_EPOCH + state.slot % preset.SLOTS_PER_EPOCH) := by
    simp [parentPaymentPosition, slotPaymentPosition, getCurrentEpoch, header]
  -- Each position from that of the parent payment is empty before the bid.
  have later : ∀ k, (preset.SLOTS_PER_EPOCH + state.slot % preset.SLOTS_PER_EPOCH).toNat ≤ k →
      paymentAt state gloas k = .empty :=
    fun k past => holds.laterEmpty k (by omega)
  by_cases paid : 0 < signed.message.value
  · obtain ⟨proposer, place, -, placed, rfl⟩ := recordBidPayment_of_pos paid recordOk
    have notSelf : signed.message.builderIndex ≠ BUILDER_INDEX_SELF_BUILD := fun self => by
      rw [value_eq_zero_of_selfBuild checked self] at paid
      exact absurd paid (by decide)
    clear recordOk computed
    unfold checkBidBuilder at builderOk
    dsimp only at builderOk
    simp only [notSelf, ↓reduceIte, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at builderOk
    obtain ⟨_, activeOk, _, rfl, _, -, _, -, _, coveredOk, _, rfl, -⟩ := builderOk
    obtain ⟨builder, pending, found, pendingOk, enough⟩ :=
      canBuilderCoverBid_eq_ok_true_iff.mp coveredOk
    have owed := (getPendingBalanceToWithdrawForBuilder_ok_iff.mp pendingOk).2
    simp only [isActiveBuilder, found, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
      Bool.and_eq_true, beq_iff_eq, exists_eq_left'] at activeOk
    have stored : (state.builders gloas).data[signed.message.builderIndex.toNat]? =
        some builder := getBuilder_eq_ok_iff.mp found
    rw [slotEq, mod] at placed
    exact holds.recordBid paid placed stored activeOk.2 (by omega) rfl rfl rfl rfl
      ((parentPaymentPosition_congr rfl rfl).trans parentAt) (position.trans placed.symm)
  -- A bid with no value records no payment, and the reserve is empty.
  have free : signed.message.value = 0 := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero] at paid
    exact UInt64.toNat_inj.mp (by simp only [UInt64.toNat_zero]; omega)
  rw [recordBidPayment_of_value_eq_zero free, Except.ok.injEq] at recordOk
  subst recordOk
  have late : ∀ index, lateBidValue
      { state with latestExecutionPayloadBid := fun _ => signed.message } gloas index = 0 :=
    fun _ => by simp [lateBidValue, free]
  refine ⟨fun index => ?_, fun index builder found exited => ?_, fun parent found => ?_,
    fun k past => ?_⟩
  · rw [late, Nat.add_zero]
    exact holds.covered index
  · rw [late, Nat.add_zero]
    exact holds.exitedClear index builder found exited
  · have same : parent = preset.SLOTS_PER_EPOCH + state.slot % preset.SLOTS_PER_EPOCH :=
      Option.some.inj (found.symm.trans parentAt)
    subst same
    have empty := later _ (Nat.le_refl _)
    simp only [paymentAt] at empty ⊢
    rw [empty]
    exact ⟨rfl, .inl rfl⟩
  · have := past _ parentAt
    have empty := later k (by omega)
    simp only [paymentAt] at empty ⊢
    exact empty

/-- From Gloas, the bid of a block keeps the builders. -/
theorem processExecutionPayloadBid_builders (gloas : .glamsterdam ≤ fork)
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    after.builders = state.builders := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok computed
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    rfl
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at recordedOk
    subst recordedOk
    rfl

/-- The bid keeps each payment, or leaves one of no weight in the second half of the window. -/
theorem paymentAt_processExecutionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after)
    (position : Nat) :
    paymentAt after gloas position = paymentAt state gloas position ∨
      preset.SLOTS_PER_EPOCH.toNat ≤ position ∧ (paymentAt after gloas position).weight = 0 := by
  obtain ⟨-, recorded, recordOk, rfl⟩ := processExecutionPayloadBid_ok computed
  change paymentAt recorded gloas position = _ ∨
    _ ∧ (paymentAt recorded gloas position).weight = 0
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, -, placed, rfl⟩ := recordBidPayment_of_pos paid recordOk
    rw [paymentAt_set (state := state) rfl]
    split
    · exact .inr ⟨by omega, rfl⟩
    · exact .inl rfl
  · rw [recordBidPayment_of_value_eq_zero
      (Classical.byContradiction fun nonzero => paid (UInt64.pos_iff_ne_zero.mpr nonzero)),
      Except.ok.injEq] at recordOk
    subst recordOk
    exact .inl rfl

end EthLib.Consensus
