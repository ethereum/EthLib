module

public import EthLib.Execution.Proofs.Evm.Call.AccessesRun
public import EthLib.Execution.Proofs.Evm.Call.StorageAt
public import EthLib.Execution.Proofs.Evm.Call.Unmarked

/-!
# Proofs: a run that reaches no frame at an address keeps or wipes its storage

A run of a call or a creation reaches the frames that its certificate steps through.

When none of them runs at an address, the storage of that address ends as it started, or wiped.

A wipe comes only from an empty account that a change deletes, as EIP-161 asks.

So a wiped account was empty at the start.

No such run marks the account for deletion, unless it was marked at the start.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork)
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.State.TransactionState

variable {fork : Fork} {Meter : Type} [GasMeter Meter] {address : Address}

/-- A message from `address` that moves value starts where the account has a nonce above 0.

The move of value then leaves the account with a nonce, so the account is not empty. -/
def SenderHasNonce (address : Address) (message : Message fork) (state : TransactionState) : Prop :=
  message.shouldTransferValue = true → message.value ≠ 0 → message.caller = address →
    (state.getAccount address).nonce ≠ 0

/-- What a run from `start` asks of the message that it starts with, if any.

A move of value from `address` starts where the account has a nonce.

A creation must have no code address, so it selects no precompile. -/
def BurnStart.Funded (address : Address) : BurnStart fork Meter → Prop
  | .frame _ | .body _ => True
  | .call message state _ _ => SenderHasNonce address message state
  | .create message state _ _ => SenderHasNonce address message state ∧ message.codeAddress = none

/-- No frame that a run from `start` reaches runs at `address`.

A precompile runs no frame. -/
def RunsAway (address : Address) (start : BurnStart fork Meter) : Prop :=
  ReachesAll (fun reached => reached.message.currentTarget ≠ address) start

/-! ## The writes outside a frame at the address -/

/-- A move of the balance of a destroyed account keeps the storage of `address`, or wipes it.

It wipes it only from an empty account.

The destroyed account must be another one. -/
theorem keptOrWipedEmpty_selfdestructTransfer {originator beneficiary : Address}
    {tx tx' : TransactionState} (h : selfdestructTransfer fork tx originator beneficiary = .ok tx')
    (hne : originator ≠ address) : KeptOrWipedEmpty address tx tx' := by
  have hout : address ∉ [originator] := by simpa using Ne.symm hne
  unfold selfdestructTransfer at h
  split at h
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    have moved := keptOrWipedEmpty_moveEther h1 fun hs => absurd hs hne
    split at h
    · exact moved.trans (.of_sameOutside (sameOutside_setAccountBalance h) hout)
    · cases h
      exact moved
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    exact (keptOrWipedEmpty_createEther h1).trans
      (.of_sameOutside (sameOutside_setAccountBalance h) hout)

omit [GasMeter Meter] in
/-- The end of a SELFDESTRUCT at another account keeps the storage of `address`, or wipes it.

It wipes it only from an empty account. -/
theorem keptOrWipedEmpty_finishSelfdestruct {beneficiary : Address} {refund : Nat}
    {evm after : Evm fork Meter} (h : finishSelfdestruct fork beneficiary refund evm = .ok after)
    (hne : evm.message.currentTarget ≠ address) :
    KeptOrWipedEmpty address evm.state after.state := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact keptOrWipedEmpty_selfdestructTransfer (Base.mapError_ok_iff.mp hst) hne

/-- The preparation of a creation touches only its target. -/
theorem sameOutside_prepareCreation {target : Address} {tx tx' : TransactionState}
    (h : prepareCreation fork tx target = .ok tx') : SameOutside [target] tx tx' := by
  have wipe : SameOutside [target] tx ((tx.destroyStorage target).markAccountCreated target) :=
    ((sameOutside_destroyStorage tx target).trans (sameOutside_markAccountCreated _ target)).mono
      (by simp)
  unfold prepareCreation at h
  split at h
  · exact (wipe.trans (sameOutside_incrementNonce (Base.mapError_ok_iff.mp h))).mono (by simp)
  · cases h
    exact wipe

/-- The state that a message enters keeps the storage of `address`, or wipes an empty account.

A move of value from `address` must start where the account has a nonce. -/
theorem keptOrWipedEmpty_entered {message : Message fork} {state entry : TransactionState}
    {substate entrySubstate : Substate}
    (h : Entered fork message state substate entry entrySubstate)
    (funded : SenderHasNonce address message state) : KeptOrWipedEmpty address state entry := by
  -- Before Paris, the message gives its target the empty account, which reads as no account.
  have hacc : (startState fork message state).getAccount address = state.getAccount address := by
    unfold startState
    split
    · by_cases ht : address = message.currentTarget
      · rw [ht]
        exact getAccount_touchAccount_self state _
      · exact getAccount_touchAccount ht
    · rfl
  have start : KeptOrWipedEmpty address state (startState fork message state) := by
    unfold startState
    split
    · exact keptOrWipedEmpty_touchAccount _
    · exact .refl _ _
  rcases h with ⟨-, rfl, -⟩ | ⟨⟨ht, hv⟩, moved, -⟩
  · exact start
  · refine start.trans (keptOrWipedEmpty_moveEther moved fun hs => ?_)
    rw [hacc]
    exact funded ht hv hs

/-- Each step of a frame at another account keeps the storage of `address`, or wipes it.

It wipes it only from an empty account.

The steps keep the message, so the frames on the way are not at `address` either. -/
theorem stepRules_keptOrWipedEmpty (address : Address) :
    StepRules fork (fun a b : Evm fork Meter => b.message = a.message ∧
      (a.message.currentTarget ≠ address → KeptOrWipedEmpty address a.state b.state)) where
  trans hab hbc := ⟨hbc.1.trans hab.1, fun hne =>
    (hab.2 hne).trans (hbc.2 (by rw [hab.1]; exact hne))⟩
  static h := ⟨h.message, fun _ => .of_sameOutside h.state List.not_mem_nil⟩
  -- SSTORE writes the storage of the account of the frame, which is another one.
  sstore _ _ _ _ _ h := ⟨rfl, fun hne =>
    .of_sameOutside (sameOutside_setStorage h) (by simpa using Ne.symm hne)⟩
  tstore _ _ _ _ := ⟨rfl, fun _ => .of_eq rfl fun _ => rfl⟩
  log _ hs _ hm _ := ⟨hm, fun _ => by rw [hs]; exact .refl _ _⟩
  selfdestruct _ _ h := ⟨message_finishSelfdestruct h, keptOrWipedEmpty_finishSelfdestruct h⟩
  incrementNonce _ _ _ _ h := ⟨rfl, fun _ => keptOrWipedEmpty_incrementNonce h⟩
  incorporate h := ⟨message_incorporateChild _ _, fun hne => by
    rw [state_incorporateChild]
    exact h.2 hne⟩

/-! ## Runs -/

/-- The message of the frame that a run from `start` begins with. -/
def BurnStart.message : BurnStart fork Meter → Message fork
  | .frame evm | .body evm => evm.message
  | .call message _ _ _ | .create message _ _ _ => message

/-- A certified run ends in a frame with the message it starts with. -/
theorem RunBurns.message_eq {start : BurnStart fork Meter} {ended : Evm fork Meter}
    {log : BurnLog} (h : RunBurns fork Meter start ended log) : ended.message = start.message := by
  induction h with
  | stopped | skipPrecompile => rfl
  | halt | failedResume => exact (staticStep_exceptionalHalt _ _).message
  | next _ hstep _ ih => exact ih.trans (stepRules_messageCode.step hstep).1
  | child _ hstep _ resumed _ _ ihTail =>
    -- The caller of the message has the message of the frame that sends it.
    exact ihTail.trans ((sameContext_of_step_eq_child hstep resumed).message.trans
      ((message_incorporateChild _ _).trans (stepRules_messageCode.step hstep).1.1))
  | bodyFrame _ _ ih => exact ih
  | precompile _ _ hrun => exact (staticStep_runPrecompile hrun).message
  | call _ _ _ ih => exact (message_rollbackOnError _ _).trans ih
  | createRollback _ _ deposit _ _ ih | createKeep _ _ deposit _ ih =>
    exact (message_depositCode deposit).trans ih

/-- A creation that runs the code of no account reaches the frame of its init code. -/
theorem RunBurns.reaches_initFrame {message : Message fork} {state prepared : TransactionState}
    {substate : Substate} {meter : Meter} {evm : Evm fork Meter} {log : BurnLog}
    (preparation : prepareCreation fork state message.currentTarget = .ok prepared)
    (run : RunBurns fork Meter (.call message prepared substate meter) evm log)
    (creates : message.codeAddress = none) :
    ∃ frame : Evm fork Meter, frame.message = message ∧
      RunReaches fork Meter (.create message state substate meter) frame := by
  cases run with
  | @call _ _ entry _ entrySubstate _ _ _ entered _ _ =>
    have selected :
        precompileAddress fork (startFrame message entry entrySubstate meter).message = none := by
      simp [precompileAddress, startFrame, creates]
    exact ⟨_, rfl, .create preparation (.call entered (.body selected (.here _)))⟩

/-- A certified run that reaches no frame at `address` keeps its storage, or wipes an empty account.

An account empty at the end was empty at the start.

The run does not mark the account for deletion, if it was not marked at the start.

A move of value from `address` at the start must find a nonce, and a creation no code address. -/
theorem RunBurns.keptOrWipedEmpty {start : BurnStart fork Meter} {ended : Evm fork Meter}
    {log : BurnLog} (h : RunBurns fork Meter start ended log) (away : RunsAway address start)
    (funded : start.Funded address) :
    KeptOrWipedEmpty address start.state ended.state ∧
      (address ∉ start.substate.accountsToDelete →
        address ∉ ended.substate.accountsToDelete) := by
  let T := (stepRules_keptOrWipedEmpty (fork := fork) (Meter := Meter) address).and
    (stepRules_unmarked address)
  have ofStatic : ∀ {a b : Evm fork Meter}, StaticStep a b →
      KeptOrWipedEmpty address a.state b.state ∧
        (address ∉ a.substate.accountsToDelete → address ∉ b.substate.accountsToDelete) :=
    fun h => ⟨.of_sameOutside h.state List.not_mem_nil, fun hx => h.toDelete ▸ hx⟩
  induction h with
  | stopped | skipPrecompile => exact ⟨.refl _ _, id⟩
  | halt | failedResume => exact ofStatic (staticStep_exceptionalHalt _ _)
  | precompile _ _ hrun => exact ofStatic (staticStep_runPrecompile hrun)
  | next running hstep _ ih =>
    have hne := away _ (.here _)
    have k := T.step hstep
    have ht := ih (fun r hr => away r (.next running hstep hr)) trivial
    exact ⟨(k.1.2 hne).trans ht.1, fun hx => ht.2 (k.2.2 hne hx)⟩
  | @child evm caller child after _ message _ _ _ running hstep _ resumed _ ihRun ihTail =>
    have hne := away _ (.here _)
    have kc := (T.step hstep).1
    -- A child that moves value moves it from the frame, which is not at `address`.
    have hfund : SenderHasNonce address message caller.state := fun ht _ hc =>
      absurd (hc.symm.trans (step_eq_child_caller hstep ht)).symm hne
    have childFunded : (BurnStart.child caller message).Funded address := by
      unfold BurnStart.child
      split
      · exact hfund
      · rename_i hnone
        exact ⟨hfund, step_eq_child_codeAddress hstep hnone⟩
    have hrun := ihRun (fun r hr => away r (.childRun running hstep hr)) childFunded
    rw [BurnStart.state_child] at hrun
    have hsub : (BurnStart.child caller message).substate.accountsToDelete =
        caller.substate.accountsToDelete := by
      unfold BurnStart.child
      split <;> rfl
    rw [hsub] at hrun
    -- The caller resumes in the state of the child.
    have same := sameContext_of_step_eq_child hstep resumed
    have htail := ihTail (fun r hr => away r (.childTail running hstep ‹_› resumed hr)) trivial
    simp only [BurnStart.state, BurnStart.substate] at htail ⊢
    rw [same.state, state_incorporateChild, same.substate] at htail
    exact ⟨(kc.1.2 hne).trans (hrun.1.trans htail.1), fun hx =>
      htail.2 (unmarked_incorporateChild (kc.2.2 hne hx) (hrun.2 (kc.2.2 hne hx)))⟩
  | bodyFrame selected _ ih => exact ih (fun r hr => away r (.body selected hr)) trivial
  | @call message state entry substate entrySubstate meter ended log entered _ parent ih =>
    have hrun := ih (fun r hr => away r (.call entered hr)) trivial
    simp only [BurnStart.state, BurnStart.substate, startFrame] at hrun ⊢
    have hentry := keptOrWipedEmpty_entered entered funded
    have hsub : entrySubstate.accountsToDelete = substate.accountsToDelete := by
      rcases entered with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> rfl
    rw [hsub] at hrun
    rw [(createdAccounts_rollbackOnError state ended).2]
    refine ⟨?_, hrun.2⟩
    unfold rollbackOnError
    split
    · -- A call that fails gives back the state it was sent from.
      exact .of_sameOutside (sameOutside_restoreTxState parent) List.not_mem_nil
    · exact hentry.trans hrun.1
  | @createRollback message state prepared substate meter evm after log preparation run deposit
      rolled parent ih =>
    obtain ⟨frame, hm, hreach⟩ := run.reaches_initFrame preparation funded.2
    have htarget : message.currentTarget ≠ address := hm ▸ away frame hreach
    have hrun := ih (fun r hr => away r (.create preparation hr)) fun ht hv hc => by
      rw [(sameOutside_prepareCreation preparation).getAccount_eq (by simpa using Ne.symm htarget)]
      exact funded.1 ht hv hc
    simp only [BurnStart.state, BurnStart.substate] at hrun ⊢
    rw [rolled, (createdAccounts_depositCode deposit).2]
    exact ⟨.of_sameOutside (sameOutside_restoreTxState parent) List.not_mem_nil, hrun.2⟩
  | @createKeep message state prepared substate meter evm after log preparation run deposit
      kept ih =>
    obtain ⟨frame, hm, hreach⟩ := run.reaches_initFrame preparation funded.2
    have htarget : message.currentTarget ≠ address := hm ▸ away frame hreach
    have hrun := ih (fun r hr => away r (.create preparation hr)) fun ht hv hc => by
      rw [(sameOutside_prepareCreation preparation).getAccount_eq (by simpa using Ne.symm htarget)]
      exact funded.1 ht hv hc
    simp only [BurnStart.state, BurnStart.substate] at hrun ⊢
    rw [(createdAccounts_depositCode deposit).2]
    refine ⟨(KeptOrWipedEmpty.of_sameOutside (sameOutside_prepareCreation preparation)
      (by simpa using Ne.symm htarget)).trans (hrun.1.trans ?_), hrun.2⟩
    rcases kept with hk | hk
    · rw [hk]
      exact .refl _ _
    · -- The code goes to the new account, the current target of the frame that ends the run.
      have hat : evm.message.currentTarget ≠ address := by
        rw [run.message_eq]
        exact htarget
      exact .of_sameOutside (sameOutside_setCode hk) (by simpa using Ne.symm hat)

variable [LawfulGasMeter Meter]

/-- A call that reaches no frame at `address` keeps its storage, or wipes an empty account.

A move of value from `address` must start where the account has a nonce.

An account empty at the end was empty at the start, and the call marks it only if it was marked.
-/
theorem keptOrWipedEmpty_processMessage_of_away {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended)
    (away : RunsAway address (.call message state substate meter))
    (funded : SenderHasNonce address message state) :
    KeptOrWipedEmpty address state ended.val.state ∧
      (address ∉ substate.accountsToDelete → address ∉ ended.val.substate.accountsToDelete) := by
  obtain ⟨log, run⟩ := (processMessage_runBurns message.gas).1 message state substate meter held
    rfl ended h
  exact run.keptOrWipedEmpty away funded

/-- A creation that reaches no frame at `address` keeps its storage, or wipes an empty account.

A move of value from `address` must start where the account has a nonce.

The creation must run the code of no account.

An account empty at the end was empty at the start, and the creation marks it only if it was.
-/
theorem keptOrWipedEmpty_processCreateMessage_of_away {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processCreateMessage fork message state substate meter held = .ok ended)
    (away : RunsAway address (.create message state substate meter))
    (funded : SenderHasNonce address message state) (creates : message.codeAddress = none) :
    KeptOrWipedEmpty address state ended.val.state ∧
      (address ∉ substate.accountsToDelete → address ∉ ended.val.substate.accountsToDelete) := by
  obtain ⟨log, run⟩ := (processMessage_runBurns message.gas).2 message state substate meter held
    rfl ended h
  exact run.keptOrWipedEmpty away ⟨funded, creates⟩

end EthLib.Execution.Evm
