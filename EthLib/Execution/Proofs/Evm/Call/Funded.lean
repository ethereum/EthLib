module

public import EthLib.Execution.Proofs.Evm.Call.StateErrors

/-!
# Proofs: a funded call or creation never fails for a balance below an amount

A message moves its value from its caller to its target when it starts.

That move fails when the caller holds less than the value.

CALL and CALLCODE send a message only when the caller holds the value.

So does a creation, and the rise of the caller's nonce that follows keeps its balance.

DELEGATECALL moves no value, and STATICCALL moves the value 0.

A creation prepares its new address, and that keeps every balance.

No step fails for a balance below the amount it takes.

So a message whose caller holds its value never fails for a balance below an amount.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- Whether the caller of a message holds, in a state, the value that the message moves. -/
def Funded (message : Message fork) (state : TransactionState) : Prop :=
  message.shouldTransferValue = true → message.value ≤ (state.getAccount message.caller).balance

/-! ## The messages that a step sends -/

/-- The end of a call instruction sends only a message funded in the state of its caller. -/
private theorem funded_finishCall {kind : CallKind} {call : CallOperands} {callee : Callee}
    {subCall newAccount expandBy : Nat} {evm caller : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : finishCall kind call callee subCall newAccount expandBy evm =
      .ok (.child caller message resume)) : Funded message caller.state := by
  unfold Evm.finishCall at h
  split at h
  · cases h
  dsimp only at h
  split at h
  · obtain ⟨_, -, hc⟩ := Base.map_ok_iff.mp h
    cases hc
  · rename_i hfunds
    unfold Evm.genericCall at h
    dsimp only at h
    split at h
    · obtain ⟨_, -, hc⟩ := Base.map_ok_iff.mp h
      cases hc
    · cases h
      intro transfers
      by_cases hk : kind = .delegatecall
      · simp [hk] at transfers
      · simp only [hk, ↓reduceIte]
        exact BitVec.not_lt.mp hfunds

/-- A step of a call instruction sends only a message funded in the state of its caller. -/
private theorem funded_callStep {kind : CallKind} {evm caller : Evm fork Meter}
    {message : Message fork} {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : callStep kind evm = .ok (.child caller message resume)) : Funded message caller.state := by
  unfold Evm.callStep at h
  obtain ⟨⟨call, e1⟩, -, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h; cases h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨_, hc⟩
  · obtain ⟨⟨callee, e4⟩, -, h⟩ := Base.bind_ok_iff.mp h
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨_, hc⟩
    · obtain ⟨⟨subCall, e5⟩, -, h⟩ := Base.bind_ok_iff.mp h
      exact funded_finishCall h
    · cases hc
  · cases hc

/-- A launch of a creation sends only a message funded in the state of its caller.

It checks that the caller holds the value, and the rise of the caller's nonce keeps its balance. -/
private theorem funded_launchCreate {evm caller : Evm fork Meter} {value : Base.U256}
    {initCode : ByteArray} {salt : Option Base.U256} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : launchCreate evm value initCode salt = .ok (.child caller message resume)) :
    Funded message caller.state := by
  unfold Evm.launchCreate at h
  dsimp only at h
  split at h
  · obtain ⟨_, -, hc⟩ := Base.map_ok_iff.mp h
    cases hc
  rename_i hcheck
  obtain ⟨address, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with hr | ⟨_, hc⟩
  · obtain ⟨e1, h1, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨e2, h2, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨state, hstate, hr⟩ := Base.bind_ok_iff.mp hr
    split at hr
    · cases hr
      intro _
      have c2 : StaticStep
          (recordAccountRead { evm with returnData := .empty } evm.message.currentTarget) e2 :=
        ((staticStep_accessAddress _ address).trans (staticStep_recordAccountRead _ address)).trans
          (.of_sameContext ((chargeStateGas_sameContext h1).trans (chargeGas_sameContext h2)))
      dsimp only
      rw [(State.TransactionState.getAccount_incrementNonce (Base.mapError_ok_iff.mp hstate)).1,
        getAccount_of_staticStep c2]
      exact BitVec.not_lt.mp fun hlt => hcheck (.inl hlt)
    · obtain ⟨_, -, hr⟩ := Base.bind_ok_iff.mp hr
      cases hr
  · cases hc

/-- A step of CREATE or CREATE2 sends only a message funded in the state of its caller. -/
private theorem funded_createStep {create2 : Bool} {evm caller : Evm fork Meter}
    {message : Message fork} {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : createStep create2 evm = .ok (.child caller message resume)) :
    Funded message caller.state := by
  obtain ⟨_, _, _, _, _, _, -, -, -, -, -, launched⟩ := createStep_eq_ok h
  exact funded_launchCreate launched

/-- An instruction that may send a message sends only a funded one. -/
private theorem funded_messageInstruction {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} {evm caller : Evm fork Meter}
    {message : Message fork} {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hrun : messageInstruction fork op = some run)
    (h : run evm = .ok (.child caller message resume)) : Funded message caller.state := by
  unfold Evm.messageInstruction at hrun
  rcases orElse_eq_some hrun with hc | hc
  · cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals (try split at hc) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hc) <;>
      (try subst hc)
    all_goals first
      | cases hc
      | exact funded_callStep h
  · cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals (try split at hc) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hc) <;>
      (try subst hc)
    all_goals first
      | cases hc
      | exact funded_createStep h

/-- Each message that a successful step sends is funded in the state of its caller frame. -/
theorem step_eq_child_funded {evm caller : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : step fork evm = .ok (.child caller message resume)) : Funded message caller.state := by
  unfold Evm.step at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · obtain ⟨_, -, hc⟩ := Base.map_ok_iff.mp h
        cases hc
      · split at h
        · exact funded_messageInstruction (by assumption) h
        · cases h
  · obtain ⟨_, -, hc⟩ := Base.map_ok_iff.mp h
    cases hc

/-! ## A run of a frame -/

omit [GasMeter Meter] in
/-- A push fails with no error of the state. -/
private theorem pushWord_ne_state (evm : Evm fork Meter) (x : Base.U256)
    (s : State.StateError) : pushWord evm x ≠ .error (.state s) := by
  intro h
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · cases (Stack.push_eq_error_iff.mp h).2
  · cases h

/-- The resume of a caller after a message it sent fails with no error of the state. -/
theorem resume_ne_state {evm caller child : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : step fork evm = .ok (.child caller message resume)) (s : State.StateError) :
    resume child ≠ .error (.state s) := by
  intro hr
  rcases step_eq_child_resume h with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩
  · rcases Base.bind_eq_error hr with hr | ⟨_, -, hr⟩
    · exact pushWord_ne_state _ _ s hr
    · cases hr
  · rcases Base.bind_eq_error hr with hr | ⟨_, -, hr⟩
    · exact pushWord_ne_state _ _ s hr
    · cases hr

/-- A run of a frame never fails for a balance below an amount.

It holds when no funded message that the frame sends fails that way. -/
private theorem runFrame_ne_insufficientBalance [LawfulGasMeter Meter] {bound : Nat}
    {runChild : MessageRunner fork Meter bound}
    (never : ∀ caller message lt, Funded message caller.state →
      ∀ address, runChild caller message lt ≠ .error (.state (.insufficientBalance address)))
    {evm : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound} (address : Address) :
    runFrame (step fork) (step_decreases fork) bound runChild evm within ≠
      .error (.state (.insufficientBalance address)) := by
  fun_induction runFrame (step fork) (step_decreases fork) bound runChild evm within
  case case1 _ _ hstep _ =>
    intro h
    cases h
    exact step_ne_insufficientBalance _ address hstep
  case case3 hstep _ ih => exact ih
  case case4 hstep _ _ ran =>
    intro h
    cases h
    exact never _ _ _ (step_eq_child_funded hstep) address ran
  case case5 hstep _ _ _ _ _ resumed _ =>
    intro h
    cases h
    exact resume_ne_state hstep _ resumed
  case case7 hstep _ _ _ ran _ resumed _ ih => exact ih
  all_goals nofun

/-! ## Calls and creations -/

/-- The state that a message starts from keeps the balance of every account. -/
private theorem balance_startState (message : Message fork) (state : TransactionState)
    (other : Address) :
    ((startState fork message state).getAccount other).balance =
      (state.getAccount other).balance := by
  unfold startState
  split
  · by_cases same : other = message.currentTarget
    · rw [same, State.TransactionState.getAccount_touchAccount_self]
    · rw [State.TransactionState.getAccount_touchAccount same]
  · rfl

/-- The preparation of a creation keeps the balance of every account. -/
private theorem balance_prepareCreation {state prepared : TransactionState} {address : Address}
    (h : prepareCreation fork state address = .ok prepared) (other : Address) :
    (prepared.getAccount other).balance = (state.getAccount other).balance := by
  have marked : ((state.destroyStorage address).markAccountCreated address).getAccount other =
      state.getAccount other := rfl
  unfold prepareCreation at h
  split at h
  · have hinc := Base.mapError_ok_iff.mp h
    by_cases same : other = address
    · subst same
      rw [(State.TransactionState.getAccount_incrementNonce hinc).1, marked]
    · unfold State.TransactionState.getAccount
      rw [(State.TransactionState.getAccount_incrementNonce hinc).2 other same]
      rfl
  · cases h
    rw [marked]

/-- A write of the state that succeeds gives the frame no error of the state. -/
theorem mapError_ne_of_isOk {α : Type} {x : Except State.StateError α}
    (hx : ∃ a, x = .ok a) (e : State.StateError) :
    x.mapError EvmError.state ≠ .error (.state e) := by
  obtain ⟨a, rfl⟩ := hx
  nofun

/-- A move of the value of a funded message fails with no lack of balance. -/
private theorem moveEther_ne_insufficientBalance {message : Message fork}
    {state : TransactionState} (funded : Funded message state)
    (transfers : message.shouldTransferValue = true) (address : Address) :
    state.moveEther fork message.caller message.currentTarget message.value ≠
      .error (.insufficientBalance address) := by
  intro h
  have hle := funded transfers
  by_cases same : message.caller = message.currentTarget
  · rw [← same] at h
    exact absurd hle (BitVec.not_le.mpr (State.TransactionState.moveEther_self_eq_error.mp h).1)
  · rcases (State.TransactionState.moveEther_eq_error same).mp h with ⟨hlt, -⟩ | ⟨-, -, hc⟩
    · exact absurd hle (BitVec.not_le.mpr hlt)
    · cases hc

/-- A funded call or creation never fails for a balance below an amount.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
theorem processMessage_ne_insufficientBalance_of_gas [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n → Funded message state →
      ∀ address, processMessage fork message state substate meter held ≠
        .error (.state (.insufficientBalance address))) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n → Funded message state →
      ∀ address, processCreateMessage fork message state substate meter held ≠
        .error (.state (.insufficientBalance address))) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    -- Each message that a frame sends has less gas, so a funded one never fails this way.
    have never : ∀ (caller : Evm fork Meter) (child : Message fork), child.gas < n →
        Funded child caller.state → ∀ address, (match child.target with
          | some _ => processMessage (Meter := Meter) fork child caller.state caller.substate.child
          | none => processCreateMessage (Meter := Meter) fork child caller.state
            caller.substate.child) ≠ .error (.state (.insufficientBalance address)) := by
      intro caller child lt funded address h
      split at h
      · exact (ih child.gas lt).1 child _ _ _ _ rfl funded address h
      · exact (ih child.gas lt).2 child _ _ _ _ rfl funded address h
    have call : ∀ (message : Message fork) (state : TransactionState) (substate : Substate)
        (meter : Meter) (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
        Funded message state → ∀ address, processMessage fork message state substate meter held ≠
          .error (.state (.insufficientBalance address)) := by
      intro message state substate meter held hn funded address h
      have start : Funded message (startState fork message state) := fun transfers => by
        rw [balance_startState]
        exact funded transfers
      rw [processMessage] at h
      simp only [Except.map] at h
      split at h
      · rename_i hdo
        cases h
        -- The run of the frame never fails this way.
        have ran : ∀ {entry : TransactionState} {e} {substate' : Substate}
            (h : runFrame (step fork) (step_decreases fork) message.gas
              (fun caller child _ => match child.target with
                | some _ => processMessage fork child caller.state caller.substate.child
                | none => processCreateMessage fork child caller.state caller.substate.child)
              (startFrame message entry substate' meter) held = .error e),
            e ≠ .state (.insufficientBalance address) := fun hrun he => by
          subst he
          exact runFrame_ne_insufficientBalance
            (fun caller child lt => never caller child (hn ▸ lt)) address hrun
        split at hdo
        · rename_i transfers
          rcases Base.bind_eq_error hdo with hm | ⟨entry, -, hdo⟩
          · cases hx : (startState fork message state).moveEther fork message.caller
                message.currentTarget message.value with
            | ok a => rw [hx] at hm; cases hm
            | error e' =>
              rw [hx] at hm
              cases hm
              exact moveEther_ne_insufficientBalance start transfers.1 address hx
          repeat' split at hdo
          all_goals first
            | (cases hdo; done)
            | (rename_i hrun; cases hdo; exact ran hrun rfl)
        · rcases Base.bind_eq_error hdo with hm | ⟨entry, -, hdo⟩
          · cases hm
          repeat' split at hdo
          all_goals first
            | (cases hdo; done)
            | (rename_i hrun; cases hdo; exact ran hrun rfl)
      · cases h
    refine ⟨call, fun message state substate meter held hn funded address h => ?_⟩
    rw [processCreateMessage] at h
    rcases Base.bind_eq_error h with hp | ⟨prepared, hprep, h⟩
    · unfold prepareCreation at hp
      split at hp
      · exact mapError_ne_of_isOk (State.TransactionState.incrementNonce_isOk _ _ _) _ hp
      · cases hp
    have ready : Funded message prepared := fun transfers => by
      rw [balance_prepareCreation hprep]
      exact funded transfers
    rcases Base.bind_eq_error h with hm | ⟨⟨evm, used⟩, -, h⟩
    · exact call message prepared substate meter held hn ready address hm
    split at h
    split at h
    · rename_i hdep
      cases h
      unfold depositCode at hdep
      dsimp only at hdep
      repeat' split at hdep
      all_goals first
        | (cases hdep; done)
        | (rcases Base.bind_eq_error hdep with hs | ⟨_, -, hs⟩
           · exact mapError_ne_of_isOk (State.TransactionState.setCode_isOk _ _ _ _) _ hs
           · cases hs)
    · cases h

/-- A call whose caller holds its value never fails for a balance below an amount. -/
theorem processMessage_ne_insufficientBalance [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} (funded : Funded message state)
    (address : Address) :
    processMessage fork message state substate meter held ≠
      .error (.state (.insufficientBalance address)) :=
  (processMessage_ne_insufficientBalance_of_gas message.gas).1 message state substate meter held
    rfl funded address

/-- A creation whose caller holds its value never fails for a balance below an amount. -/
theorem processCreateMessage_ne_insufficientBalance [LawfulGasMeter Meter]
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} (funded : Funded message state)
    (address : Address) :
    processCreateMessage fork message state substate meter held ≠
      .error (.state (.insufficientBalance address)) :=
  (processMessage_ne_insufficientBalance_of_gas message.gas).2 message state substate meter held
    rfl funded address

end EthLib.Execution.Evm
