module

public import EthLib.Execution.Proofs.Evm.Call.NoncesFit
public import EthLib.Execution.Proofs.Evm.Interpreter
import EthLib.Execution.Proofs.Evm.Call.ContractAddress

/-!
# Proofs: a call or a creation aborts only with an error of the state

Four kinds of error abort a run: an error of the state, an encoding, an opcode and a fork.

Every opcode of a fork has an instruction there, so no step fails for an unspecified opcode.

No step fails for a fork whose rules are not yet specified.

Only CREATE encodes, to find the address of its new account from the sender and its nonce.

That encoding succeeds for every nonce below `2^256`.

EIP-2681 bounds every nonce by `2^64 - 1`, and every call keeps that bound.

So does every creation whose address starts with a nonce below `2^64 - 1`.

So a run from a state whose nonces fit aborts only with an error of the state.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## Results that abort only with an error of the state -/

/-- The error is no unspecified opcode, no failure of encoding and no unspecified fork. -/
private def Harmless : EvmError → Prop
  | .unspecifiedOpcode _ | .encoding _ | .forkNotYetSpecified _ => False
  | _ => True

/-- A harmless error that aborts is an error of the state. -/
private theorem Harmless.state {e : EvmError} (h : Harmless e) (aborts : e.aborts = true) :
    ∃ error, e = .state error := by
  cases e <;> first | exact ⟨_, rfl⟩ | exact h.elim | cases aborts

/-- The result fails only with a harmless error. -/
private def Fine {α : Type} (r : Except EvmError α) : Prop :=
  ∀ e, r = .error e → Harmless e

/-- A success is fine. -/
private theorem Fine.ok {α : Type} (a : α) : Fine (.ok a : Except EvmError α) :=
  fun _ h => by cases h

/-- A pure result is fine. -/
private theorem Fine.pure {α : Type} (a : α) : Fine (Pure.pure a : Except EvmError α) :=
  fun _ h => by cases h

/-- A throw of a harmless error is fine. -/
private theorem Fine.throw {α : Type} {e : EvmError} (h : Harmless e) :
    Fine (MonadExcept.throw e : Except EvmError α) :=
  fun _ he => by cases he; exact h

/-- A failure with a harmless error is fine. -/
private theorem Fine.error {α : Type} {e : EvmError} (h : Harmless e) :
    Fine (.error e : Except EvmError α) :=
  fun _ he => by cases he; exact h

/-- A sequence is fine when its first part is, and its rest after it. -/
private theorem Fine.bind {α β : Type} {x : Except EvmError α} {f : α → Except EvmError β}
    (hx : Fine x) (hf : ∀ a, x = .ok a → Fine (f a)) : Fine (x >>= f) := by
  intro e h
  rcases Base.bind_eq_error h with h | ⟨a, ha, h⟩
  · exact hx e h
  · exact hf a ha e h

/-- A map of a fine result is fine. -/
private theorem Fine.map {α β : Type} {x : Except EvmError α} (f : α → β) (hx : Fine x) :
    Fine (f <$> x) := by
  intro e h
  cases hx' : x with
  | error e' => rw [hx'] at h; cases h; exact hx _ hx'
  | ok a => rw [hx'] at h; cases h

/-- Every failure of the state, as an error of the frame, is fine. -/
private theorem Fine.mapError_state {α : Type} (x : Except State.StateError α) :
    Fine (x.mapError EvmError.state) := by
  intro e he
  cases hx : x with
  | error e' => rw [hx] at he; cases he; trivial
  | ok a => rw [hx] at he; cases he

omit [GasMeter Meter] in
/-- A pop is fine. -/
private theorem fine_popWord (evm : Evm fork Meter) : Fine (popWord evm) := by
  refine Fine.bind (fun e h => ?_) fun _ _ => Fine.pure _
  rw [(Stack.pop_eq_error_iff.mp h).2]
  trivial

omit [GasMeter Meter] in
/-- A push is fine. -/
private theorem fine_pushWord (evm : Evm fork Meter) (x : Base.U256) : Fine (pushWord evm x) := by
  refine Fine.bind (fun e h => ?_) fun _ _ => Fine.pure _
  rw [(Stack.push_eq_error_iff.mp h).2]
  trivial

/-- A charge of gas is fine. -/
private theorem fine_chargeGas [LawfulGasMeter Meter] (evm : Evm fork Meter) (amount : Nat) :
    Fine (chargeGas evm amount) := by
  refine Fine.bind (fun e h => ?_) fun _ _ => Fine.pure _
  rw [LawfulGasMeter.charge_error h]
  trivial

/-- A charge of state gas is fine. -/
private theorem fine_chargeStateGas [LawfulGasMeter Meter] (evm : Evm fork Meter)
    (amount : Nat) : Fine (chargeStateGas evm amount) := by
  refine Fine.bind (fun e h => ?_) fun _ _ => Fine.pure _
  rw [LawfulGasMeter.chargeState_error h]
  trivial

/-- A charge of gas and of memory is fine. -/
private theorem fine_chargeGasAndMemory [LawfulGasMeter Meter] (evm : Evm fork Meter)
    (cost : Nat) (ranges : List (Base.U256 × Base.U256)) :
    Fine (chargeGasAndMemory evm cost ranges) :=
  Fine.bind (fine_chargeGas _ _) fun _ _ => Fine.pure _

/-- A check of gas is fine. -/
private theorem fine_checkGas (evm : Evm fork Meter) (amount : Nat) :
    Fine (checkGas evm amount) := by
  unfold checkGas
  split
  · exact Fine.throw trivial
  · exact Fine.pure _

omit [GasMeter Meter] in
/-- The pops of the topics of a log are fine. -/
private theorem fine_popTopics (n : Nat) : ∀ evm : Evm fork Meter, Fine (popTopics evm n) := by
  induction n with
  | zero => exact fun _ => Fine.pure _
  | succ n ih =>
    exact fun _ => Fine.bind (fine_popWord _) fun _ _ =>
      Fine.bind (ih _) fun _ _ => Fine.pure _

/-- The rest of an instruction that keeps its reads is fine when the rest is. -/
private theorem Fine.keepReads {α : Type} {evm : Evm fork Meter} {halted : Evm fork Meter → α}
    {rest : Except EvmError α} (h : Fine rest) : Fine (keepReads evm halted rest) := by
  intro e he
  unfold Evm.keepReads at he
  split at he
  · split at he
    · cases he
      exact h _ rfl
    · cases he
  · cases he

/-- Walk a sequence of fine parts. -/
local macro "fine" : tactic =>
  `(tactic| repeat' (first
    | exact Fine.ok _
    | exact Fine.pure _
    | exact fine_popWord _
    | exact fine_pushWord _ _
    | exact fine_chargeGas _ _
    | exact fine_chargeStateGas _ _
    | exact fine_chargeGasAndMemory _ _ _
    | exact fine_checkGas _ _
    | exact fine_popTopics _ _
    | exact Fine.mapError_state _
    | exact Fine.throw trivial
    | exact Fine.error trivial
    | refine Fine.bind ?_ fun _ _ => ?_
    | refine Fine.map _ ?_
    | refine Fine.keepReads ?_
    | split))

/-! ## The instructions that send no message -/

/-- Each instruction that only touches the stack is fine. -/
private theorem fine_stackOnlyStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : stackOnlyStep fork op = some run) (evm : Evm fork Meter) : Fine (run evm) := by
  cases op <;> simp only [stackOnlyStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | (simp only [unaryOp, binaryOp, ternaryOp, expStep, keccak256Step, popStep, pushN, dupN,
        swapN, dupnStep, swapnStep, exchangeStep]
       fine)

/-- Each instruction of control flow is fine. -/
private theorem fine_controlFlowStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : controlFlowStep op = some run) (evm : Evm fork Meter) : Fine (run evm) := by
  cases op <;> simp only [controlFlowStep, Option.some.injEq, reduceCtorEq] at hstep <;>
    subst hstep <;> simp only [stopStep, jumpStep, jumpiStep, readFrame, jumpdestStep] <;> fine

/-- Each instruction of memory and of the input data is fine. -/
private theorem fine_memoryDataStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : memoryDataStep op = some run) (evm : Evm fork Meter) : Fine (run evm) := by
  cases op <;> simp only [memoryDataStep, Option.some.injEq, reduceCtorEq] at hstep <;>
    subst hstep <;>
    simp only [mloadStep, mstoreStep, mstore8Step, mcopyStep, calldataloadStep, copyToMemory,
      returndatacopyStep, readFrame] <;> fine

/-- Each instruction that returns is fine. -/
private theorem fine_returnOpStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : returnOpStep fork op = some run) (evm : Evm fork Meter) : Fine (run evm) := by
  cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | (simp only [returnStep, revertStep, haltWithOutput]; fine)

/-- Each instruction of the environment is fine. -/
private theorem fine_environmentStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : environmentStep fork op = some run) (evm : Evm fork Meter) : Fine (run evm) := by
  cases op <;> simp only [environmentStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | (simp only [blockhashStep, blobhashStep, readFrame]; fine)

/-- Each instruction that reads another account is fine. -/
private theorem fine_accountStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : accountStep fork op = some run) (evm : Evm fork Meter) : Fine (run evm) := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | (simp only [balanceStep, extcodehashStep, extcodesizeStep, extcodecopyStep, accountCode,
        readFrame]; fine)

/-- Each instruction of a log is fine. -/
private theorem fine_logOpStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : logOpStep op = some run) (evm : Evm fork Meter) : Fine (run evm) := by
  cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  simp only [logStep]
  fine

/-- Each instruction of transient storage is fine. -/
private theorem fine_transientStorageStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : transientStorageStep fork op = some run) (evm : Evm fork Meter) :
    Fine (run evm) := by
  cases op <;> simp only [transientStorageStep, reduceCtorEq] at hstep <;> split at hstep <;>
    simp only [Option.some.injEq, reduceCtorEq] at hstep <;> subst hstep <;>
    simp only [tloadStep, tstoreStep] <;> fine

/-- Each instruction of storage is fine. -/
private theorem fine_storageStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : storageStep op = some run) (evm : Evm fork Meter) : Fine (run evm) := by
  cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hstep <;>
    subst hstep <;> simp only [sloadStep, sstoreStep] <;> fine

/-- SELFDESTRUCT is fine. -/
private theorem fine_selfdestructOpStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : selfdestructOpStep fork op = some run) (evm : Evm fork Meter) : Fine (run evm) := by
  cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  simp only [selfdestructStep, finishSelfdestruct]
  fine

/-- An instruction that gives the next frame is fine. -/
private theorem fine_instruction [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hrun : instruction fork op = some run) (evm : Evm fork Meter) : Fine (run evm) := by
  unfold Evm.instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact fine_stackOnlyStep hf evm
  rcases orElse_eq_some hrun with hf | hrun
  · exact fine_controlFlowStep hf evm
  rcases orElse_eq_some hrun with hf | hrun
  · exact fine_memoryDataStep hf evm
  rcases orElse_eq_some hrun with hf | hrun
  · exact fine_returnOpStep hf evm
  rcases orElse_eq_some hrun with hf | hrun
  · exact fine_environmentStep hf evm
  rcases orElse_eq_some hrun with hf | hrun
  · exact fine_accountStep hf evm
  rcases orElse_eq_some hrun with hf | hrun
  · exact fine_storageStep hf evm
  rcases orElse_eq_some hrun with hf | hrun
  · exact fine_transientStorageStep hf evm
  rcases orElse_eq_some hrun with hf | hf
  · exact fine_logOpStep hf evm
  · exact fine_selfdestructOpStep hf evm

/-! ## The calls and the creations -/

/-- A step of a call instruction is fine. -/
private theorem fine_callStep [LawfulGasMeter Meter] {kind : CallKind} (evm : Evm fork Meter) :
    Fine (callStep kind evm) := by
  simp only [callStep, popCallOperands, popCallValue, accessDelegation, accountCode, payCall,
    finishCall, genericCall, skipCall]
  fine

/-- The launch of a creation from a frame whose nonces fit is fine.

The nonce of the sender is below `2^256`, so its address encodes. -/
private theorem fine_launchCreate [LawfulGasMeter Meter] {evm : Evm fork Meter}
    {value : Base.U256} {initCode : ByteArray} {salt : Option Base.U256}
    (hfit : evm.state.NoncesFit) : Fine (launchCreate evm value initCode salt) := by
  have read := stepRules_noncesFit.static
    (staticStep_recordAccountRead { evm with returnData := .empty } evm.message.currentTarget) hfit
  unfold launchCreate
  dsimp only
  split
  · fine
  refine Fine.bind ?_ fun _ _ => ?_
  · unfold creationAddress
    split
    · exact Fine.ok _
    · obtain ⟨address, ha⟩ := createAddress_ok evm.message.currentTarget
        (Nat.lt_of_le_of_lt (read evm.message.currentTarget) (by decide))
      rw [ha]
      exact Fine.ok _
  · fine

/-- A step of CREATE or CREATE2 from a frame whose nonces fit is fine. -/
private theorem fine_createStep [LawfulGasMeter Meter] {create2 : Bool} {evm : Evm fork Meter}
    (hfit : evm.state.NoncesFit) : Fine (createStep create2 evm) := by
  unfold createStep
  dsimp only
  split
  · exact Fine.bind (Fine.throw trivial) fun _ h => by cases h
  refine Fine.bind (fine_popWord _) fun ⟨_, e1⟩ h1 => ?_
  refine Fine.bind (fine_popWord _) fun ⟨_, e2⟩ h2 => ?_
  refine Fine.bind (fine_popWord _) fun ⟨_, e3⟩ h3 => ?_
  refine Fine.bind (by unfold popSalt; fine) fun ⟨_, e4⟩ h4 => ?_
  refine Fine.bind (fine_chargeGasAndMemory _ _ _) fun e5 h5 => ?_
  dsimp only at h2 h3 h4 h5
  have salted : SameContext e3 e4 := by
    unfold popSalt at h4
    split at h4
    · obtain ⟨⟨_, _⟩, hp, h4⟩ := Base.bind_ok_iff.mp h4
      cases h4
      exact popWord_sameContext hp
    · cases h4
      exact ⟨rfl, rfl, rfl, rfl⟩
  have fit : e5.state.NoncesFit := by
    have same : e5.state = evm.state := (chargeGasAndMemory_sameContext h5).state.trans
      (salted.state.trans ((popWord_sameContext h3).state.trans
        ((popWord_sameContext h2).state.trans (popWord_sameContext h1).state)))
    exact same ▸ hfit
  unfold genericCreate
  split
  · exact Fine.error trivial
  split
  · exact Fine.error trivial
  exact fine_launchCreate fit

/-- An instruction that may send a message, from a frame whose nonces fit, is fine. -/
private theorem fine_messageInstruction [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)}
    (hrun : messageInstruction fork op = some run) {evm : Evm fork Meter}
    (hfit : evm.state.NoncesFit) : Fine (run evm) := by
  unfold Evm.messageInstruction at hrun
  rcases orElse_eq_some hrun with hc | hc
  · cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals (try split at hc) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hc) <;>
      (try subst hc)
    all_goals first
      | cases hc
      | exact fine_callStep evm
  · cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals (try split at hc) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hc) <;>
      (try subst hc)
    all_goals first
      | cases hc
      | exact fine_createStep hfit

/-- A step from a frame whose nonces fit is fine. -/
private theorem fine_step [LawfulGasMeter Meter] {evm : Evm fork Meter}
    (hfit : evm.state.NoncesFit) : Fine (step fork evm) := by
  unfold step
  split
  · dsimp only
    split
    · exact Fine.throw trivial
    · rename_i op decoded
      split
      · exact Fine.map _ (fine_instruction (by assumption) evm)
      · rename_i hi
        split
        · exact fine_messageInstruction (by assumption) hfit
        · rename_i hm
          rcases instruction_or_messageInstruction_isSome (Meter := Meter)
            (since_le_of_ofByte_eq_some decoded) with h | h
          · rw [hi] at h
            cases h
          · rw [hm] at h
            cases h
  · exact Fine.map _ (Fine.ok _)

/-- A step from a frame whose nonces fit aborts only with an error of the state. -/
theorem step_aborts_state [LawfulGasMeter Meter] {evm : Evm fork Meter} {e : EvmError}
    (hfit : evm.state.NoncesFit) (h : step fork evm = .error e) (aborts : e.aborts = true) :
    ∃ error, e = .state error :=
  (fine_step hfit e h).state aborts

/-! ## A run of a frame -/

/-- The resume of a caller after a message it sent is fine. -/
private theorem fine_resume [LawfulGasMeter Meter] {evm caller child : Evm fork Meter}
    {message : Message fork} {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : step fork evm = .ok (.child caller message resume)) : Fine (resume child) := by
  rcases step_eq_child_resume h with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩
  · simp only [resumeCall]
    fine
  · simp only [resumeCreate]
    fine

/-- A run of a frame whose nonces fit fails only with an error of the state.

Each message that the runner runs from such a state must fail only with an error of the state.

Each message that the runner completes must keep every nonce within the bound.

For a creation, both are needed only when its address starts with a nonce of at most 1. -/
private theorem runFrame_state [LawfulGasMeter Meter] {bound : Nat}
    {runChild : MessageRunner fork Meter bound}
    (never : ∀ caller message lt e, caller.state.NoncesFit →
      (message.target = none → (caller.state.getAccount message.currentTarget).nonce ≤ 1) →
      runChild caller message lt = .error e → ∃ error, e = .state error)
    (keeps : ∀ caller message lt ended, runChild caller message lt = .ok ended →
      caller.state.NoncesFit →
      (message.target = none → (caller.state.getAccount message.currentTarget).nonce ≤ 1) →
      ended.val.state.NoncesFit)
    {evm : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound}
    (hfit : evm.state.NoncesFit) (e : EvmError)
    (h : runFrame (step fork) (step_decreases fork) bound runChild evm within = .error e) :
    ∃ error, e = .state error := by
  fun_induction runFrame (step fork) (step_decreases fork) bound runChild evm within
  case case1 hstep aborts =>
    cases h
    exact (fine_step hfit _ hstep).state aborts
  case case3 hstep _ ih => exact ih (stepRules_noncesFit.step hstep hfit) h
  case case4 hstep _ _ ran =>
    cases h
    exact never _ _ _ _ ((stepRules_noncesFit.step hstep).1 hfit)
      (step_eq_child_create_nonce_le hstep) ran
  case case5 hstep _ _ _ _ _ resumed aborts =>
    cases h
    exact (fine_resume hstep _ resumed).state aborts
  case case7 hstep _ _ _ ran _ resumed _ ih =>
    refine ih ?_ h
    rw [(sameContext_of_step_eq_child hstep resumed).state, state_incorporateChild]
    exact keeps _ _ _ _ ran ((stepRules_noncesFit.step hstep).1 hfit)
      (step_eq_child_create_nonce_le hstep)
  all_goals cases h

/-! ## The calls and the creations of a run -/

/-- A failure of the state, as an error of the frame, is an error of the state. -/
theorem mapError_state_eq_error {α : Type} {x : Except State.StateError α}
    {e : EvmError} (h : x.mapError EvmError.state = .error e) : ∃ error, e = .state error := by
  cases hx : x with
  | error e' => rw [hx] at h; cases h; exact ⟨_, rfl⟩
  | ok a => rw [hx] at h; cases h

/-- The state that a message starts its frame from keeps every nonce within the bound. -/
private theorem noncesFit_startState {message : Message fork} {state : TransactionState}
    (hfit : state.NoncesFit) : (startState fork message state).NoncesFit := by
  unfold startState
  split
  · intro other
    by_cases hne : other = message.currentTarget
    · subst hne
      rw [TransactionState.getAccount_touchAccount_self]
      exact hfit _
    · rw [TransactionState.getAccount_touchAccount hne]
      exact hfit _
  · exact hfit

/-- A move of ether keeps every nonce within the bound. -/
private theorem noncesFit_moveEther {tx tx' : TransactionState} {sender recipient : Base.Address}
    {amount : Base.U256} (h : tx.moveEther fork sender recipient amount = .ok tx')
    (hfit : tx.NoncesFit) : tx'.NoncesFit :=
  fun address => (TransactionState.moveEther_nonce_codeHash h address).1 ▸ hfit address

/-- Every call and creation from a state whose nonces fit fails only with an error of the state.

A creation must start at an address whose nonce is below `2^64 - 1`.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
private theorem processMessage_state_of_gas [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n → state.NoncesFit →
      ∀ e, processMessage fork message state substate meter held = .error e →
        ∃ error, e = .state error) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n → state.NoncesFit →
      (state.getAccount message.currentTarget).nonce < MAX_NONCE →
      ∀ e, processCreateMessage fork message state substate meter held = .error e →
        ∃ error, e = .state error) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    -- Each message that the frame sends has less gas, so it fails only so and keeps the bound.
    have never : ∀ (caller : Evm fork Meter) (child : Message fork), child.gas < n →
        caller.state.NoncesFit →
        (child.target = none → (caller.state.getAccount child.currentTarget).nonce ≤ 1) →
        ∀ e, (match child.target with
          | some _ => processMessage (Meter := Meter) fork child caller.state caller.substate.child
          | none => processCreateMessage (Meter := Meter) fork child caller.state
            caller.substate.child) = .error e → ∃ error, e = .state error := by
      intro caller child lt hfit hnonce e h
      split at h
      · exact (ih child.gas lt).1 child _ _ _ _ rfl hfit e h
      · rename_i hnone
        exact (ih child.gas lt).2 child _ _ _ _ rfl hfit
          (Nat.lt_of_le_of_lt (hnonce hnone) (by decide)) e h
    have keeps : ∀ (caller : Evm fork Meter) (child : Message fork) ended, (match child.target with
          | some _ => processMessage (Meter := Meter) fork child caller.state caller.substate.child
          | none => processCreateMessage (Meter := Meter) fork child caller.state
            caller.substate.child) = .ok ended → caller.state.NoncesFit →
        (child.target = none → (caller.state.getAccount child.currentTarget).nonce ≤ 1) →
        ended.val.state.NoncesFit := by
      intro caller child ended h hfit hnonce
      split at h
      · exact noncesFit_processMessage hfit h
      · rename_i hnone
        exact noncesFit_processCreateMessage hfit
          (Nat.lt_of_le_of_lt (hnonce hnone) (by decide)) h
    have call : ∀ (message : Message fork) (state : TransactionState) (substate : Substate)
        (meter : Meter) (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
        state.NoncesFit → ∀ e, processMessage fork message state substate meter held = .error e →
        ∃ error, e = .state error := by
      intro message state substate meter held hn hfit e h
      have start : (startState fork message state).NoncesFit := noncesFit_startState hfit
      rw [processMessage] at h
      simp only [Except.map] at h
      split at h
      · rename_i hdo
        cases h
        -- The frame starts from a state whose nonces fit, so its run fails only so.
        have ran : ∀ {entry : TransactionState}, entry.NoncesFit → ∀ {e} {substate' : Substate}
            (h : runFrame (step fork) (step_decreases fork) message.gas
              (fun caller child _ => match child.target with
                | some _ => processMessage fork child caller.state caller.substate.child
                | none => processCreateMessage fork child caller.state caller.substate.child)
              (startFrame message entry substate' meter) held = .error e),
            ∃ error, e = .state error := fun entered _ _ hrun =>
          runFrame_state (fun caller child lt e hfit hnonce =>
              never caller child (hn ▸ lt) hfit hnonce e)
            (fun caller child _ ended ran => keeps caller child ended ran) entered _ hrun
        split at hdo
        · rcases Base.bind_eq_error hdo with hm | ⟨entry, hentry, hdo⟩
          · exact mapError_state_eq_error hm
          have entered := noncesFit_moveEther (Base.mapError_ok_iff.mp hentry) start
          repeat' split at hdo
          all_goals first
            | (cases hdo; done)
            | (rename_i hrun; cases hdo; exact ran entered hrun)
        · rcases Base.bind_eq_error hdo with hm | ⟨entry, hentry, hdo⟩
          · cases hm
          cases hentry
          repeat' split at hdo
          all_goals first
            | (cases hdo; done)
            | (rename_i hrun; cases hdo; exact ran start hrun)
      · cases h
    refine ⟨call, fun message state substate meter held hn hfit htarget e h => ?_⟩
    rw [processCreateMessage] at h
    rcases Base.bind_eq_error h with hp | ⟨prepared, hprep, h⟩
    · unfold prepareCreation at hp
      split at hp
      · exact mapError_state_eq_error hp
      · cases hp
    have marked : ((state.destroyStorage message.currentTarget).markAccountCreated
        message.currentTarget).NoncesFit :=
      NoncesFit.of_nonceLe (NonceLe.of_getAccountOptional fun _ => rfl) hfit
    have ready : prepared.NoncesFit := by
      unfold prepareCreation at hprep
      split at hprep
      · exact noncesFit_incrementNonce marked (Nat.ne_of_lt htarget)
          (Base.mapError_ok_iff.mp hprep)
      · cases hprep
        exact marked
    rcases Base.bind_eq_error h with hm | ⟨⟨evm, used⟩, -, h⟩
    · exact call message prepared substate meter held hn ready e hm
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
           · exact mapError_state_eq_error hs
           · cases hs)
    · cases h

/-- A call from a state whose nonces fit fails only with an error of the state. -/
theorem processMessage_eq_error [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {e : EvmError} (hfit : state.NoncesFit)
    (h : processMessage fork message state substate meter held = .error e) :
    ∃ error, e = .state error :=
  (processMessage_state_of_gas message.gas).1 message state substate meter held rfl hfit e h

/-- A creation from a state whose nonces fit fails only with an error of the state.

Its address must start with a nonce below `2^64 - 1`. -/
theorem processCreateMessage_eq_error [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {e : EvmError} (hfit : state.NoncesFit)
    (htarget : (state.getAccount message.currentTarget).nonce < MAX_NONCE)
    (h : processCreateMessage fork message state substate meter held = .error e) :
    ∃ error, e = .state error :=
  (processMessage_state_of_gas message.gas).2 message state substate meter held rfl hfit htarget
    e h

end EthLib.Execution.Evm
