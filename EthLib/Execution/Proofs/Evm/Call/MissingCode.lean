module

public import EthLib.Execution.Proofs.Evm.Call.Codes

/-!
# Proofs: no call or creation aborts for a missing code, on a state that holds every code

A run aborts with a missing code when it looks up a code hash whose code the state lacks.

Only EXTCODESIZE, EXTCODECOPY and the call instructions look up code.

Each looks up the code of an account in the state of its frame, or that of its delegate.

Every change of the state in a step fails only with an error other than a missing code.

A lawful meter fails a charge only for lack of gas, so no charge fails with a missing code.

So a step from a frame whose state holds the code of every account never aborts for a missing code.

A caller resumes from its child with no lookup of code.

Every call and creation keeps the code of each account available.

So every frame of a run holds every code, and no call or creation aborts for a missing code.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork Hash32)
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Transactions (HasCodes hasCodes_incrementNonce hasCodes_moveEther
  hasCodes_of_getCode hasCodes_touchAccount)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## Results with no missing code -/

/-- The result is not a failure for a missing code. -/
private def NoMiss {α : Type} (r : Except EvmError α) : Prop :=
  ∀ c, r ≠ .error (.state (.missingCode c))

/-- A success has no missing code. -/
private theorem NoMiss.ok {α : Type} (a : α) : NoMiss (.ok a : Except EvmError α) :=
  fun _ h => by cases h

/-- A pure result has no missing code. -/
private theorem NoMiss.pure {α : Type} (a : α) : NoMiss (Pure.pure a : Except EvmError α) :=
  fun _ h => by cases h

/-- A throw of another error has no missing code. -/
private theorem NoMiss.throw {α : Type} {e : EvmError} (h : ∀ c, e ≠ .state (.missingCode c)) :
    NoMiss (MonadExcept.throw e : Except EvmError α) :=
  fun c he => h c (by cases he; rfl)

/-- A failure with another error has no missing code. -/
private theorem NoMiss.error {α : Type} {e : EvmError} (h : ∀ c, e ≠ .state (.missingCode c)) :
    NoMiss (.error e : Except EvmError α) :=
  fun c he => h c (by cases he; rfl)

/-- A sequence has no missing code when its first part has none, nor its rest after it. -/
private theorem NoMiss.bind {α β : Type} {x : Except EvmError α} {f : α → Except EvmError β}
    (hx : NoMiss x) (hf : ∀ a, x = .ok a → NoMiss (f a)) : NoMiss (x >>= f) := by
  intro c h
  rcases Base.bind_eq_error h with h | ⟨a, ha, h⟩
  · exact hx c h
  · exact hf a ha c h

/-- A map of a result with no missing code has none. -/
private theorem NoMiss.map {α β : Type} {x : Except EvmError α} (f : α → β) (hx : NoMiss x) :
    NoMiss (f <$> x) := by
  intro c h
  cases hx' : x with
  | error e => rw [hx'] at h; cases h; exact hx c hx'
  | ok a => rw [hx'] at h; cases h

omit [GasMeter Meter] in
/-- A pop has no missing code. -/
private theorem noMiss_popWord (evm : Evm fork Meter) : NoMiss (popWord evm) := by
  refine NoMiss.bind (fun c h => ?_) fun _ _ => NoMiss.pure _
  cases (Stack.pop_eq_error_iff.mp h).2

omit [GasMeter Meter] in
/-- A push has no missing code. -/
private theorem noMiss_pushWord (evm : Evm fork Meter) (x : Base.U256) :
    NoMiss (pushWord evm x) := by
  refine NoMiss.bind (fun c h => ?_) fun _ _ => NoMiss.pure _
  cases (Stack.push_eq_error_iff.mp h).2

/-- A charge of gas has no missing code. -/
private theorem noMiss_chargeGas [LawfulGasMeter Meter] (evm : Evm fork Meter) (amount : Nat) :
    NoMiss (chargeGas evm amount) := by
  refine NoMiss.bind (fun c h => ?_) fun _ _ => NoMiss.pure _
  cases LawfulGasMeter.charge_error h

/-- A charge of state gas has no missing code. -/
private theorem noMiss_chargeStateGas [LawfulGasMeter Meter] (evm : Evm fork Meter)
    (amount : Nat) : NoMiss (chargeStateGas evm amount) := by
  refine NoMiss.bind (fun c h => ?_) fun _ _ => NoMiss.pure _
  cases LawfulGasMeter.chargeState_error h

/-- A charge of gas and of memory has no missing code. -/
private theorem noMiss_chargeGasAndMemory [LawfulGasMeter Meter] (evm : Evm fork Meter)
    (cost : Nat) (ranges : List (Base.U256 × Base.U256)) :
    NoMiss (chargeGasAndMemory evm cost ranges) :=
  NoMiss.bind (noMiss_chargeGas _ _) fun _ _ => NoMiss.pure _

/-- A check of gas has no missing code. -/
private theorem noMiss_checkGas (evm : Evm fork Meter) (amount : Nat) :
    NoMiss (checkGas evm amount) := by
  unfold checkGas
  split
  · exact NoMiss.throw nofun
  · exact NoMiss.pure _

omit [GasMeter Meter] in
/-- The pops of the topics of a log have no missing code. -/
private theorem noMiss_popTopics (n : Nat) : ∀ evm : Evm fork Meter, NoMiss (popTopics evm n) := by
  induction n with
  | zero => exact fun _ => NoMiss.pure _
  | succ n ih =>
    exact fun _ => NoMiss.bind (noMiss_popWord _) fun _ _ =>
      NoMiss.bind (ih _) fun _ _ => NoMiss.pure _

/-- A write of the state that fails with no missing code has none as an error of the frame. -/
private theorem NoMiss.mapError_state {α : Type} {x : Except State.StateError α}
    (h : ∀ c, x ≠ .error (.missingCode c)) : NoMiss (x.mapError EvmError.state) := by
  intro c hc
  cases hx : x with
  | error e => rw [hx] at hc; cases hc; exact h c hx
  | ok a => rw [hx] at hc; cases hc

/-- A change of an account has no missing code when the change to the account has none. -/
theorem modifyState_ne_missingCode {tx : TransactionState} {address : Base.Address}
    {f : State.Account → Except State.StateError State.Account}
    (hf : ∀ account c, f account ≠ .error (.missingCode c)) (c : Hash32) :
    tx.modifyState fork address f ≠ .error (.missingCode c) := by
  intro h
  rcases Base.bind_eq_error h with h | ⟨a, -, h⟩
  · exact hf _ c h
  · dsimp only at h
    split at h <;> cases h

/-- A debit fails with no missing code. -/
private theorem debit_ne_missingCode (address : Base.Address) (amount : Base.U256)
    (account : State.Account) (c : Hash32) :
    State.Account.debit address amount account ≠ .error (.missingCode c) := by
  unfold State.Account.debit
  split <;> nofun

/-- A credit fails with no missing code. -/
private theorem credit_ne_missingCode (address : Base.Address) (amount : Base.U256)
    (account : State.Account) (c : Hash32) :
    State.Account.credit address amount account ≠ .error (.missingCode c) := by
  unfold State.Account.credit
  split <;> nofun

/-- A move of ether fails with no missing code. -/
private theorem moveEther_ne_missingCode (tx : TransactionState) (sender recipient : Base.Address)
    (amount : Base.U256) (c : Hash32) :
    tx.moveEther fork sender recipient amount ≠ .error (.missingCode c) := by
  intro h
  rcases Base.bind_eq_error h with h | ⟨a, -, h⟩
  · exact modifyState_ne_missingCode (debit_ne_missingCode _ _) c h
  · exact modifyState_ne_missingCode (credit_ne_missingCode _ _) c h

/-- A write of storage fails with no missing code. -/
private theorem setStorage_ne_missingCode (tx : TransactionState) (address : Base.Address)
    (key : Base.Bytes32) (value : Base.U256) (c : Hash32) :
    tx.setStorage address key value ≠ .error (.missingCode c) := by
  unfold TransactionState.setStorage
  split <;> nofun

/-- A write of code fails with no missing code. -/
private theorem setCode_ne_missingCode (tx : TransactionState) (address : Base.Address)
    (code : ByteArray) (c : Hash32) : tx.setCode fork address code ≠ .error (.missingCode c) := by
  unfold TransactionState.setCode
  exact modifyState_ne_missingCode (fun _ _ h => by cases h) c

/-- A rise of a nonce fails with no missing code. -/
private theorem incrementNonce_ne_missingCode (tx : TransactionState) (address : Base.Address)
    (c : Hash32) : tx.incrementNonce fork address ≠ .error (.missingCode c) :=
  modifyState_ne_missingCode (fun _ _ h => by cases h) c

/-- A move of the balance of a destroyed account fails with no missing code. -/
private theorem selfdestructTransfer_ne_missingCode (tx : TransactionState)
    (originator beneficiary : Base.Address) (c : Hash32) :
    selfdestructTransfer fork tx originator beneficiary ≠ .error (.missingCode c) := by
  intro h
  unfold selfdestructTransfer at h
  split at h
  · rcases Base.bind_eq_error h with h | ⟨a, -, h⟩
    · exact moveEther_ne_missingCode _ _ _ _ c h
    · split at h
      · exact modifyState_ne_missingCode (fun _ _ h => by cases h) c h
      · cases h
  · rcases Base.bind_eq_error h with h | ⟨a, -, h⟩
    · exact modifyState_ne_missingCode (credit_ne_missingCode _ _) c h
    · exact modifyState_ne_missingCode (fun _ _ h => by cases h) c h

/-- The rest of an instruction that keeps its reads has no missing code when the rest has none. -/
private theorem NoMiss.keepReads {α : Type} {evm : Evm fork Meter} {halted : Evm fork Meter → α}
    {rest : Except EvmError α} (h : NoMiss rest) : NoMiss (keepReads evm halted rest) := by
  intro c hc
  unfold Evm.keepReads at hc
  split at hc
  · split at hc
    · cases hc
      exact h c rfl
    · cases hc
  · cases hc

/-- A failure of encoding is not a missing code. -/
private theorem NoMiss.mapError_encoding {α : Type} (x : Except Serialization.Rlp.RlpError α) :
    NoMiss (x.mapError EvmError.encoding) := by
  intro c hc
  cases hx : x with
  | error e => rw [hx] at hc; cases hc
  | ok a => rw [hx] at hc; cases hc

/-- Walk a sequence of parts, each with no missing code. -/
local macro "no_miss" : tactic =>
  `(tactic| repeat' (first
    | exact NoMiss.ok _
    | exact NoMiss.pure _
    | exact noMiss_popWord _
    | exact noMiss_pushWord _ _
    | exact noMiss_chargeGas _ _
    | exact noMiss_chargeStateGas _ _
    | exact noMiss_chargeGasAndMemory _ _ _
    | exact noMiss_checkGas _ _
    | exact noMiss_popTopics _ _
    | exact NoMiss.throw nofun
    | exact NoMiss.error nofun
    | refine NoMiss.bind ?_ fun _ _ => ?_
    | refine NoMiss.map _ ?_
    | refine NoMiss.keepReads ?_
    | exact NoMiss.mapError_state (setStorage_ne_missingCode _ _ _ _)
    | exact NoMiss.mapError_state (incrementNonce_ne_missingCode _ _)
    | exact NoMiss.mapError_state (selfdestructTransfer_ne_missingCode _ _ _)
    | exact NoMiss.mapError_encoding _
    | split))

/-! ## The instructions that read no code -/

/-- Each instruction that only touches the stack has no missing code. -/
private theorem noMiss_stackOnlyStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : stackOnlyStep fork op = some run) (evm : Evm fork Meter) : NoMiss (run evm) := by
  cases op <;> simp only [stackOnlyStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | (simp only [unaryOp, binaryOp, ternaryOp, expStep, keccak256Step, popStep, pushN, dupN,
        swapN, dupnStep, swapnStep, exchangeStep]
       no_miss)

/-- Each instruction of control flow has no missing code. -/
private theorem noMiss_controlFlowStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : controlFlowStep op = some run) (evm : Evm fork Meter) : NoMiss (run evm) := by
  cases op <;> simp only [controlFlowStep, Option.some.injEq, reduceCtorEq] at hstep <;>
    subst hstep <;> simp only [stopStep, jumpStep, jumpiStep, readFrame, jumpdestStep] <;> no_miss

/-- Each instruction of memory and of the input data has no missing code. -/
private theorem noMiss_memoryDataStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : memoryDataStep op = some run) (evm : Evm fork Meter) : NoMiss (run evm) := by
  cases op <;> simp only [memoryDataStep, Option.some.injEq, reduceCtorEq] at hstep <;>
    subst hstep <;>
    simp only [mloadStep, mstoreStep, mstore8Step, mcopyStep, calldataloadStep, copyToMemory,
      returndatacopyStep, readFrame] <;> no_miss

/-- Each instruction that returns has no missing code. -/
private theorem noMiss_returnOpStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : returnOpStep fork op = some run) (evm : Evm fork Meter) : NoMiss (run evm) := by
  cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | (simp only [returnStep, revertStep, haltWithOutput]; no_miss)

/-- Each instruction of the environment has no missing code. -/
private theorem noMiss_environmentStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : environmentStep fork op = some run) (evm : Evm fork Meter) : NoMiss (run evm) := by
  cases op <;> simp only [environmentStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | (simp only [blockhashStep, blobhashStep, readFrame]; no_miss)

/-- Each instruction of a log has no missing code. -/
private theorem noMiss_logOpStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : logOpStep op = some run) (evm : Evm fork Meter) : NoMiss (run evm) := by
  cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  simp only [logStep]
  no_miss

/-- Each instruction of transient storage has no missing code. -/
private theorem noMiss_transientStorageStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : transientStorageStep fork op = some run) (evm : Evm fork Meter) :
    NoMiss (run evm) := by
  cases op <;> simp only [transientStorageStep, reduceCtorEq] at hstep <;> split at hstep <;>
    simp only [Option.some.injEq, reduceCtorEq] at hstep <;> subst hstep <;>
    simp only [tloadStep, tstoreStep] <;> no_miss

/-- Each instruction of storage has no missing code. -/
private theorem noMiss_storageStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : storageStep op = some run) (evm : Evm fork Meter) : NoMiss (run evm) := by
  cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hstep <;>
    subst hstep <;> simp only [sloadStep, sstoreStep] <;> no_miss

/-! ## The instructions that read code -/

/-- A static step keeps the code of each account available. -/
private theorem hasCodes_static {a b : Evm fork Meter} (h : StaticStep a b)
    (available : HasCodes a.state) : HasCodes b.state :=
  (stepRules_hasCodes.static h).2.1 available

omit [GasMeter Meter] in
/-- A read of code from a state that holds every code has no missing code. -/
private theorem noMiss_accountCode {evm : Evm fork Meter} (available : HasCodes evm.state)
    (address : Base.Address) : NoMiss (accountCode evm address) := by
  obtain ⟨code, hc⟩ := available address
  intro c h
  simp [accountCode, hc, Except.mapError] at h

/-- EXTCODESIZE from a state that holds every code has no missing code. -/
private theorem noMiss_extcodesizeStep [LawfulGasMeter Meter] {evm : Evm fork Meter}
    (available : HasCodes evm.state) : NoMiss (extcodesizeStep evm) := by
  refine NoMiss.bind (noMiss_popWord _) fun ⟨w, e1⟩ h1 => ?_
  refine NoMiss.bind (noMiss_chargeGas _ _) fun e2 h2 => ?_
  refine NoMiss.bind (noMiss_accountCode (hasCodes_static ?_ available) _) fun _ _ => ?_
  · exact (((StaticStep.of_sameContext (popWord_sameContext h1)).trans
      (staticStep_accessAddress e1 _)).trans (.of_sameContext (chargeGas_sameContext h2))).trans
      (staticStep_recordAccountRead _ _)
  · no_miss

/-- EXTCODECOPY from a state that holds every code has no missing code. -/
private theorem noMiss_extcodecopyStep [LawfulGasMeter Meter] {evm : Evm fork Meter}
    (available : HasCodes evm.state) : NoMiss (extcodecopyStep evm) := by
  refine NoMiss.bind (noMiss_popWord _) fun ⟨_, e1⟩ h1 => ?_
  refine NoMiss.bind (noMiss_popWord _) fun ⟨_, e2⟩ h2 => ?_
  refine NoMiss.bind (noMiss_popWord _) fun ⟨_, e3⟩ h3 => ?_
  refine NoMiss.bind (noMiss_popWord _) fun ⟨_, e4⟩ h4 => ?_
  refine NoMiss.bind (noMiss_chargeGasAndMemory _ _ _) fun e5 h5 => ?_
  refine NoMiss.bind (noMiss_accountCode (hasCodes_static ?_ available) _) fun _ _ => ?_
  · exact (((((((StaticStep.of_sameContext (popWord_sameContext h1)).trans
      (.of_sameContext (popWord_sameContext h2))).trans
      (.of_sameContext (popWord_sameContext h3))).trans
      (.of_sameContext (popWord_sameContext h4))).trans (staticStep_accessAddress e4 _)).trans
      (.of_sameContext (chargeGasAndMemory_sameContext h5))).trans
      (staticStep_recordAccountRead _ _))
  · no_miss

/-- Each instruction that reads another account, from a state with every code, has none missing. -/
private theorem noMiss_accountStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : accountStep fork op = some run) {evm : Evm fork Meter}
    (available : HasCodes evm.state) : NoMiss (run evm) := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | exact noMiss_extcodesizeStep available
    | exact noMiss_extcodecopyStep available
    | (simp only [balanceStep, extcodehashStep, readFrame]; no_miss)

/-- The access to a delegate from a state that holds every code has no missing code. -/
private theorem noMiss_accessDelegation {evm : Evm fork Meter} (available : HasCodes evm.state)
    (address : Base.Address) (known : Nat) : NoMiss (accessDelegation evm address known) := by
  refine NoMiss.bind (noMiss_accountCode available _) fun code _ => ?_
  dsimp only
  split
  · refine NoMiss.bind (noMiss_checkGas _ _) fun _ _ => ?_
    refine NoMiss.bind (noMiss_accountCode (hasCodes_static
      ((staticStep_accessAddress _ _).trans (staticStep_recordAccountRead _ _)) available) _)
      fun _ _ => NoMiss.pure _
  · exact NoMiss.pure _

/-- SELFDESTRUCT has no missing code. -/
private theorem noMiss_selfdestructOpStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : selfdestructOpStep fork op = some run) (evm : Evm fork Meter) : NoMiss (run evm) := by
  cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  simp only [selfdestructStep, finishSelfdestruct]
  no_miss

/-- An instruction that gives the next frame, from a state with every code, has none missing. -/
private theorem noMiss_instruction [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hrun : instruction fork op = some run)
    {evm : Evm fork Meter} (available : HasCodes evm.state) : NoMiss (run evm) := by
  unfold Evm.instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact noMiss_stackOnlyStep hf evm
  rcases orElse_eq_some hrun with hf | hrun
  · exact noMiss_controlFlowStep hf evm
  rcases orElse_eq_some hrun with hf | hrun
  · exact noMiss_memoryDataStep hf evm
  rcases orElse_eq_some hrun with hf | hrun
  · exact noMiss_returnOpStep hf evm
  rcases orElse_eq_some hrun with hf | hrun
  · exact noMiss_environmentStep hf evm
  rcases orElse_eq_some hrun with hf | hrun
  · exact noMiss_accountStep hf available
  rcases orElse_eq_some hrun with hf | hrun
  · exact noMiss_storageStep hf evm
  rcases orElse_eq_some hrun with hf | hrun
  · exact noMiss_transientStorageStep hf evm
  rcases orElse_eq_some hrun with hf | hf
  · exact noMiss_logOpStep hf evm
  · exact noMiss_selfdestructOpStep hf evm

/-! ## The calls and the creations -/

/-- A step of a call instruction from a state that holds every code has no missing code. -/
private theorem noMiss_callStep [LawfulGasMeter Meter] {kind : CallKind} {evm : Evm fork Meter}
    (available : HasCodes evm.state) : NoMiss (callStep kind evm) := by
  unfold callStep
  refine NoMiss.bind (by simp only [popCallOperands, popCallValue]; no_miss)
    fun ⟨call, e1⟩ h1 => ?_
  dsimp only
  split
  · exact NoMiss.bind (NoMiss.throw nofun) fun _ h => by cases h
  refine NoMiss.bind (noMiss_checkGas _ _) fun _ _ => ?_
  refine NoMiss.keepReads (NoMiss.bind (noMiss_accessDelegation (hasCodes_static ?_ available) _ _)
    fun _ _ => ?_)
  · exact (((staticStep_popCallOperands h1).1.trans (staticStep_accessAddress e1 _)).trans
      (staticStep_recordAccountRead _ _))
  · simp only [payCall, finishCall, genericCall, skipCall]
    no_miss

/-- A step of CREATE or CREATE2 has no missing code. -/
private theorem noMiss_createStep [LawfulGasMeter Meter] {create2 : Bool} (evm : Evm fork Meter) :
    NoMiss (createStep create2 evm) := by
  simp only [createStep, popSalt, genericCreate, launchCreate, creationAddress, skipCall]
  no_miss

/-- An instruction that may send a message, from a state with every code, has none missing. -/
private theorem noMiss_messageInstruction [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)}
    (hrun : messageInstruction fork op = some run) {evm : Evm fork Meter}
    (available : HasCodes evm.state) : NoMiss (run evm) := by
  unfold Evm.messageInstruction at hrun
  rcases orElse_eq_some hrun with hc | hc
  · cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals (try split at hc) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hc) <;>
      (try subst hc)
    all_goals first
      | cases hc
      | exact noMiss_callStep available
  · cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals (try split at hc) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hc) <;>
      (try subst hc)
    all_goals first
      | cases hc
      | exact noMiss_createStep evm

/-- A step from a frame whose state holds every code never aborts for a missing code. -/
theorem step_ne_missingCode [LawfulGasMeter Meter] {evm : Evm fork Meter}
    (available : HasCodes evm.state) (codeHash : Hash32) :
    step fork evm ≠ .error (.state (.missingCode codeHash)) := by
  unfold step
  split
  · dsimp only
    split
    · nofun
    · split
      · exact NoMiss.map _ (noMiss_instruction (by assumption) available) codeHash
      · split
        · exact noMiss_messageInstruction (by assumption) available codeHash
        · nofun
  · exact NoMiss.map _ (NoMiss.ok _) codeHash

/-! ## A run of a frame -/

/-- The resume of a caller after a message it sent has no missing code. -/
private theorem noMiss_resume [LawfulGasMeter Meter] {evm caller child : Evm fork Meter}
    {message : Message fork} {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : step fork evm = .ok (.child caller message resume)) : NoMiss (resume child) := by
  rcases step_eq_child_resume h with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩
  · simp only [resumeCall]
    no_miss
  · simp only [resumeCreate]
    no_miss

/-- A run of a frame from a state that holds every code never aborts for a missing code.

Each message that the runner runs from such a state must never abort for a missing code.

Each message that the runner completes must leave a state that holds every code. -/
private theorem runFrame_ne_missingCode [LawfulGasMeter Meter] {bound : Nat}
    {runChild : MessageRunner fork Meter bound}
    (never : ∀ caller message lt, HasCodes caller.state → NoMiss (runChild caller message lt))
    (keeps : ∀ caller message lt ended, runChild caller message lt = .ok ended →
      HasCodes caller.state → HasCodes ended.val.state)
    {evm : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound}
    (available : HasCodes evm.state) :
    NoMiss (runFrame (step fork) (step_decreases fork) bound runChild evm within) := by
  fun_induction runFrame (step fork) (step_decreases fork) bound runChild evm within
  case case1 _ _ hstep _ =>
    intro c h
    cases h
    exact step_ne_missingCode available c hstep
  case case3 hstep _ ih => exact ih ((stepRules_hasCodes.step hstep).2.1 available)
  case case4 hstep _ _ ran =>
    intro c h
    cases h
    exact never _ _ _ ((stepRules_hasCodes.step hstep).1.2.1 available) c ran
  case case5 hstep _ _ _ _ _ resumed _ =>
    intro c h
    cases h
    exact noMiss_resume hstep c resumed
  case case7 hstep _ _ _ ran _ resumed _ ih =>
    refine ih ?_
    rw [(sameContext_of_step_eq_child hstep resumed).state, state_incorporateChild]
    exact keeps _ _ _ _ ran ((stepRules_hasCodes.step hstep).1.2.1 available)
  all_goals exact NoMiss.ok _

/-- No call or creation from a state that holds every code aborts for a missing code.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
theorem processMessage_ne_missingCode_of_gas [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n → HasCodes state →
      ∀ codeHash, processMessage fork message state substate meter held ≠
        .error (.state (.missingCode codeHash))) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n → HasCodes state →
      ∀ codeHash, processCreateMessage fork message state substate meter held ≠
        .error (.state (.missingCode codeHash))) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    -- Each message that the frame sends has less gas, so it never aborts this way and keeps codes.
    have never : ∀ (caller : Evm fork Meter) (child : Message fork), child.gas < n →
        HasCodes caller.state → NoMiss (match child.target with
          | some _ => processMessage (Meter := Meter) fork child caller.state caller.substate.child
          | none => processCreateMessage (Meter := Meter) fork child caller.state
            caller.substate.child) := by
      intro caller child lt available c h
      split at h
      · exact (ih child.gas lt).1 child _ _ _ _ rfl available c h
      · exact (ih child.gas lt).2 child _ _ _ _ rfl available c h
    have keeps : ∀ (caller : Evm fork Meter) (child : Message fork) ended, (match child.target with
          | some _ => processMessage (Meter := Meter) fork child caller.state caller.substate.child
          | none => processCreateMessage (Meter := Meter) fork child caller.state
            caller.substate.child) = .ok ended → HasCodes caller.state →
        HasCodes ended.val.state := by
      intro caller child ended h available
      split at h
      · exact hasCodes_processMessage h available
      · exact hasCodes_processCreateMessage h available
    have call : ∀ (message : Message fork) (state : TransactionState) (substate : Substate)
        (meter : Meter) (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
        HasCodes state → NoMiss (processMessage fork message state substate meter held) := by
      intro message state substate meter held hn available c h
      have start : HasCodes (startState fork message state) := by
        unfold startState
        split
        · exact hasCodes_touchAccount _ available
        · exact available
      rw [processMessage] at h
      simp only [Except.map] at h
      split at h
      · rename_i hdo
        cases h
        -- The frame starts from a state with every code, so its run never aborts this way.
        have ran : ∀ {entry : TransactionState}, HasCodes entry → ∀ {e} {substate' : Substate}
            (h : runFrame (step fork) (step_decreases fork) message.gas
              (fun caller child _ => match child.target with
                | some _ => processMessage fork child caller.state caller.substate.child
                | none => processCreateMessage fork child caller.state caller.substate.child)
              (startFrame message entry substate' meter) held = .error e),
            e ≠ .state (.missingCode c) := fun entered _ _ hrun he => by
          subst he
          exact runFrame_ne_missingCode (fun caller child lt => never caller child (hn ▸ lt))
            (fun caller child _ ended ran => keeps caller child ended ran) entered c hrun
        split at hdo
        · rcases Base.bind_eq_error hdo with hm | ⟨entry, hentry, hdo⟩
          · exact NoMiss.mapError_state (moveEther_ne_missingCode _ _ _ _) c hm
          have entered := hasCodes_moveEther (Base.mapError_ok_iff.mp hentry) start
          repeat' split at hdo
          all_goals first
            | (cases hdo; done)
            | (rename_i hrun; cases hdo; exact ran entered hrun rfl)
        · rcases Base.bind_eq_error hdo with hm | ⟨entry, hentry, hdo⟩
          · cases hm
          cases hentry
          repeat' split at hdo
          all_goals first
            | (cases hdo; done)
            | (rename_i hrun; cases hdo; exact ran start hrun rfl)
      · cases h
    refine ⟨fun message state substate meter held hn available c => call message state substate
      meter held hn available c, fun message state substate meter held hn available c h => ?_⟩
    rw [processCreateMessage] at h
    rcases Base.bind_eq_error h with hp | ⟨prepared, hprep, h⟩
    · unfold prepareCreation at hp
      split at hp
      · exact NoMiss.mapError_state (incrementNonce_ne_missingCode _ _) c hp
      · cases hp
    have marked : HasCodes ((state.destroyStorage message.currentTarget).markAccountCreated
        message.currentTarget) := hasCodes_of_getCode (fun _ => rfl) (fun _ => .inl rfl) available
    have ready : HasCodes prepared := by
      unfold prepareCreation at hprep
      split at hprep
      · exact hasCodes_incrementNonce (Base.mapError_ok_iff.mp hprep) marked
      · cases hprep
        exact marked
    rcases Base.bind_eq_error h with hm | ⟨⟨evm, used⟩, -, h⟩
    · exact call message prepared substate meter held hn ready c hm
    split at h
    split at h
    · rename_i hdep
      cases h
      unfold depositCode at hdep
      dsimp only at hdep
      repeat' split at hdep
      all_goals first
        | (cases hdep; done)
        | exact NoMiss.bind (NoMiss.mapError_state (setCode_ne_missingCode _ _ _))
            (fun _ _ => NoMiss.pure _) c hdep
    · cases h

/-- A call from a state that holds the code of every account never aborts for a missing code. -/
theorem processMessage_ne_missingCode [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} (available : HasCodes state)
    (codeHash : Hash32) :
    processMessage fork message state substate meter held ≠
      .error (.state (.missingCode codeHash)) :=
  (processMessage_ne_missingCode_of_gas message.gas).1 message state substate meter held rfl
    available codeHash

/-- A creation from a state that holds every code never aborts for a missing code. -/
theorem processCreateMessage_ne_missingCode [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} (available : HasCodes state)
    (codeHash : Hash32) :
    processCreateMessage fork message state substate meter held ≠
      .error (.state (.missingCode codeHash)) :=
  (processMessage_ne_missingCode_of_gas message.gas).2 message state substate meter held rfl
    available codeHash

end EthLib.Execution.Evm
