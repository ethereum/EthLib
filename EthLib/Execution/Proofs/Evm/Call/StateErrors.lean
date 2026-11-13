module

public import EthLib.Execution.Proofs.Evm.Call.StepRules
public import EthLib.Execution.Proofs.Evm.Interpreter

/-!
# Proofs: the errors of the state with which a step fails

A step changes the state only through a few writes, and each write fails in its own way.

A lawful meter fails a charge only for lack of gas.

A lookup of code fails when the state lacks the code of a code hash.

SSTORE fails when the address it runs at has no account in the state.

SELFDESTRUCT credits its beneficiary, which fails when that balance would reach `2^256`.

It moves the whole balance of its account, so it never lacks the amount.

So a step fails with an error of the state only for missing code, an absent account or an overflow.

In particular no step fails for a balance below the amount it takes.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork Hash32)
open EthLib.Execution.State (StateError TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## Results that fail only with the errors of the state of a step -/

/-- The error of the state is one of the three with which a step may fail.

The account at the target must be absent for its error to count. -/
private def Allowed (target : Address) (account : Option State.Account) (e : StateError) :
    Prop :=
  (∃ codeHash, e = .missingCode codeHash) ∨ (e = .noAccount target ∧ account = none) ∨
    ∃ address, e = .balanceOverflow address

/-- The result fails with an error of the state only in one of the three allowed ways. -/
private def Cls (target : Address) (account : Option State.Account) {α : Type}
    (r : Except EvmError α) : Prop :=
  ∀ e, r = .error (.state e) → Allowed target account e

variable {t : Address} {o : Option State.Account}

/-- A success is allowed. -/
private theorem Cls.ok {α : Type} (a : α) : Cls t o (.ok a : Except EvmError α) :=
  fun _ h => by cases h

/-- A pure result is allowed. -/
private theorem Cls.pure {α : Type} (a : α) : Cls t o (Pure.pure a : Except EvmError α) :=
  fun _ h => by cases h

/-- A throw of an error that is not of the state is allowed. -/
private theorem Cls.throw {α : Type} {e : EvmError} (h : ∀ s, e ≠ .state s) :
    Cls t o (MonadExcept.throw e : Except EvmError α) :=
  fun s he => (h s (by cases he; rfl)).elim

/-- A failure with an error that is not of the state is allowed. -/
private theorem Cls.error {α : Type} {e : EvmError} (h : ∀ s, e ≠ .state s) :
    Cls t o (.error e : Except EvmError α) :=
  fun s he => (h s (by cases he; rfl)).elim

/-- A sequence is allowed when its first part is, and its rest after it. -/
private theorem Cls.bind {α β : Type} {x : Except EvmError α} {f : α → Except EvmError β}
    (hx : Cls t o x) (hf : ∀ a, x = .ok a → Cls t o (f a)) : Cls t o (x >>= f) := by
  intro e h
  rcases Base.bind_eq_error h with h | ⟨a, ha, h⟩
  · exact hx e h
  · exact hf a ha e h

/-- A map of an allowed result is allowed. -/
private theorem Cls.map {α β : Type} {x : Except EvmError α} (f : α → β) (hx : Cls t o x) :
    Cls t o (f <$> x) := by
  intro e h
  cases hx' : x with
  | error e' => rw [hx'] at h; cases h; exact hx _ hx'
  | ok a => rw [hx'] at h; cases h

/-- A write of the state is allowed when each of its failures is allowed. -/
private theorem Cls.mapError_state {α : Type} {x : Except StateError α}
    (h : ∀ s, x = .error s → Allowed t o s) : Cls t o (x.mapError EvmError.state) := by
  intro e he
  cases hx : x with
  | error e' => rw [hx] at he; cases he; exact h _ hx
  | ok a => rw [hx] at he; cases he

/-- A failure of encoding is allowed. -/
private theorem Cls.mapError_encoding {α : Type} (x : Except Serialization.Rlp.RlpError α) :
    Cls t o (x.mapError EvmError.encoding) := by
  intro e he
  cases hx : x with
  | error e' => rw [hx] at he; cases he
  | ok a => rw [hx] at he; cases he

/-- The rest of an instruction that keeps its reads is allowed when the rest is. -/
private theorem Cls.keepReads {α : Type} {evm : Evm fork Meter} {halted : Evm fork Meter → α}
    {rest : Except EvmError α} (h : Cls t o rest) : Cls t o (keepReads evm halted rest) :=
  fun e he => h e (keepReads_eq_error.mp he).1

omit [GasMeter Meter] in
/-- A pop is allowed. -/
private theorem cls_popWord (evm : Evm fork Meter) : Cls t o (popWord evm) := by
  refine Cls.bind (fun e h => ?_) fun _ _ => Cls.pure _
  cases (Stack.pop_eq_error_iff.mp h).2

omit [GasMeter Meter] in
/-- A push is allowed. -/
private theorem cls_pushWord (evm : Evm fork Meter) (x : Base.U256) :
    Cls t o (pushWord evm x) := by
  refine Cls.bind (fun e h => ?_) fun _ _ => Cls.pure _
  cases (Stack.push_eq_error_iff.mp h).2

/-- A charge of gas is allowed. -/
private theorem cls_chargeGas [LawfulGasMeter Meter] (evm : Evm fork Meter) (amount : Nat) :
    Cls t o (chargeGas evm amount) := by
  refine Cls.bind (fun e h => ?_) fun _ _ => Cls.pure _
  cases LawfulGasMeter.charge_error h

/-- A charge of state gas is allowed. -/
private theorem cls_chargeStateGas [LawfulGasMeter Meter] (evm : Evm fork Meter)
    (amount : Nat) : Cls t o (chargeStateGas evm amount) := by
  refine Cls.bind (fun e h => ?_) fun _ _ => Cls.pure _
  cases LawfulGasMeter.chargeState_error h

/-- A charge of gas and of memory is allowed. -/
private theorem cls_chargeGasAndMemory [LawfulGasMeter Meter] (evm : Evm fork Meter)
    (cost : Nat) (ranges : List (Base.U256 × Base.U256)) :
    Cls t o (chargeGasAndMemory evm cost ranges) :=
  Cls.bind (cls_chargeGas _ _) fun _ _ => Cls.pure _

/-- A check of gas is allowed. -/
private theorem cls_checkGas (evm : Evm fork Meter) (amount : Nat) :
    Cls t o (checkGas evm amount) := by
  unfold checkGas
  split
  · exact Cls.throw nofun
  · exact Cls.pure _

omit [GasMeter Meter] in
/-- The pops of the topics of a log are allowed. -/
private theorem cls_popTopics (n : Nat) : ∀ evm : Evm fork Meter, Cls t o (popTopics evm n) := by
  induction n with
  | zero => exact fun _ => Cls.pure _
  | succ n ih =>
    exact fun _ => Cls.bind (cls_popWord _) fun _ _ =>
      Cls.bind (ih _) fun _ _ => Cls.pure _

omit [GasMeter Meter] in
/-- A read of code fails only for a missing code. -/
private theorem cls_accountCode (evm : Evm fork Meter) (address : Address) :
    Cls t o (accountCode evm address) := by
  refine Cls.mapError_state fun s h => .inl ?_
  unfold State.TransactionState.getCode at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · unfold State.State.getCode at h
        split at h
        · cases h
        · split at h
          · cases h
          · cases h
            exact ⟨_, rfl⟩

/-- A rise of a nonce never fails. -/
private theorem cls_incrementNonce (tx : TransactionState) (address : Address) :
    Cls t o ((tx.incrementNonce fork address).mapError EvmError.state) := by
  refine Cls.mapError_state fun s h => ?_
  obtain ⟨_, h'⟩ := State.TransactionState.incrementNonce_isOk fork tx address
  rw [h'] at h
  cases h

/-- A move of the balance of a destroyed account fails only when a balance would overflow.

It moves the whole balance that it reads, so it never lacks that amount. -/
private theorem selfdestructTransfer_eq_error (tx : TransactionState)
    (originator beneficiary : Address) {s : StateError}
    (h : selfdestructTransfer fork tx originator beneficiary = .error s) :
    ∃ address, s = .balanceOverflow address := by
  unfold selfdestructTransfer at h
  split at h
  · rcases Base.bind_eq_error h with h | ⟨a, -, h⟩
    · by_cases same : originator = beneficiary
      · subst same
        exact absurd (State.TransactionState.moveEther_self_eq_error.mp h).1
          (BitVec.lt_irrefl _)
      · rcases (State.TransactionState.moveEther_eq_error same).mp h with ⟨hlt, -⟩ | ⟨-, -, rfl⟩
        · exact absurd hlt (BitVec.lt_irrefl _)
        · exact ⟨_, rfl⟩
    · split at h
      · cases State.TransactionState.modifyState_eq_error.mp h
      · cases h
  · rcases Base.bind_eq_error h with h | ⟨a, -, h⟩
    · have h := State.TransactionState.modifyState_eq_error.mp h
      unfold State.Account.credit at h
      split at h
      · cases h
      · cases h
        exact ⟨_, rfl⟩
    · cases State.TransactionState.modifyState_eq_error.mp h

/-- A move of the balance of a destroyed account is allowed. -/
private theorem cls_selfdestructTransfer (tx : TransactionState)
    (originator beneficiary : Address) :
    Cls t o ((selfdestructTransfer fork tx originator beneficiary).mapError EvmError.state) :=
  Cls.mapError_state fun _ h => .inr (.inr (selfdestructTransfer_eq_error _ _ _ h))

/-- Walk a sequence of allowed parts. -/
local macro "cls" : tactic =>
  `(tactic| repeat' (first
    | exact Cls.ok _
    | exact Cls.pure _
    | exact cls_popWord _
    | exact cls_pushWord _ _
    | exact cls_chargeGas _ _
    | exact cls_chargeStateGas _ _
    | exact cls_chargeGasAndMemory _ _ _
    | exact cls_checkGas _ _
    | exact cls_popTopics _ _
    | exact cls_accountCode _ _
    | exact cls_incrementNonce _ _
    | exact cls_selfdestructTransfer _ _ _
    | exact Cls.mapError_encoding _
    | exact Cls.throw nofun
    | exact Cls.error nofun
    | refine Cls.bind ?_ fun _ _ => ?_
    | refine Cls.map _ ?_
    | refine Cls.keepReads ?_
    | split))

/-! ## SSTORE -/

/-- SSTORE fails with an error of the state only for an absent account at its target.

The pops, the access, the read and the charges before the write keep that account. -/
private theorem cls_sstoreStep [LawfulGasMeter Meter] (evm : Evm fork Meter) :
    Cls evm.message.currentTarget (evm.state.getAccountOptional evm.message.currentTarget)
      (sstoreStep evm) := by
  intro s h
  unfold Evm.sstoreStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  rcases Base.bind_eq_error h with h | ⟨⟨k, e1⟩, h1, h⟩
  · exact cls_popWord evm s h
  rcases Base.bind_eq_error h with h | ⟨⟨n, e2⟩, h2, h⟩
  · exact cls_popWord e1 s h
  have c2 : StaticStep evm e2 :=
    .of_sameContext ((popWord_sameContext h1).trans (popWord_sameContext h2))
  dsimp only at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rcases hpair : accessStorageKey e2 e2.message.currentTarget (Base.U256.toBeBytes k) with
    ⟨cold, e3⟩
  have ha :
      StaticStep evm (recordStorageRead e3 e2.message.currentTarget (Base.U256.toBeBytes k)) := by
    have := staticStep_accessStorageKey e2 e2.message.currentTarget (Base.U256.toBeBytes k)
    rw [hpair] at this
    exact (c2.trans this).trans (staticStep_recordStorageRead _ _ _)
  simp only [hpair] at h
  have h := (keepReads_eq_error.mp h).1
  rcases Base.bind_eq_error h with h | ⟨e4, h4, h⟩
  · exact cls_chargeGas _ _ s h
  rcases Base.bind_eq_error h with h | ⟨e5, h5, h⟩
  · exact cls_chargeStateGas _ _ s h
  have m5 : StaticStep evm e5 :=
    ha.trans (.of_sameContext ((sameContext_refillStateGas _ _).trans
      ((chargeGas_sameContext h4).trans (chargeStateGas_sameContext h5))))
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rcases Base.bind_eq_error h with h | ⟨st, -, h⟩
  · cases hx : e5.state.setStorage e2.message.currentTarget (Base.U256.toBeBytes k) n with
    | ok a => rw [hx] at h; cases h
    | error e' =>
      rw [hx] at h
      cases h
      obtain ⟨hnone, rfl⟩ :=
        (State.TransactionState.setStorage_eq_error_iff _ _ _ _ _).mp hx
      have hmsg : e2.message = evm.message := c2.message
      refine .inr (.inl ⟨by rw [hmsg], ?_⟩)
      rw [← (m5.state evm.message.currentTarget List.not_mem_nil).1, ← hmsg]
      exact hnone
  · cases h

/-! ## The instructions that give the next frame -/

/-- Each instruction that only touches the stack is allowed. -/
private theorem cls_stackOnlyStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : stackOnlyStep fork op = some run) (evm : Evm fork Meter) : Cls t o (run evm) := by
  cases op <;> simp only [stackOnlyStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | (simp only [unaryOp, binaryOp, ternaryOp, expStep, keccak256Step, popStep, pushN, dupN,
        swapN, dupnStep, swapnStep, exchangeStep]
       cls)

/-- Each instruction of control flow is allowed. -/
private theorem cls_controlFlowStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : controlFlowStep op = some run) (evm : Evm fork Meter) : Cls t o (run evm) := by
  cases op <;> simp only [controlFlowStep, Option.some.injEq, reduceCtorEq] at hstep <;>
    subst hstep <;> simp only [stopStep, jumpStep, jumpiStep, readFrame, jumpdestStep] <;> cls

/-- Each instruction of memory and of the input data is allowed. -/
private theorem cls_memoryDataStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : memoryDataStep op = some run) (evm : Evm fork Meter) : Cls t o (run evm) := by
  cases op <;> simp only [memoryDataStep, Option.some.injEq, reduceCtorEq] at hstep <;>
    subst hstep <;>
    simp only [mloadStep, mstoreStep, mstore8Step, mcopyStep, calldataloadStep, copyToMemory,
      returndatacopyStep, readFrame] <;> cls

/-- Each instruction that returns is allowed. -/
private theorem cls_returnOpStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : returnOpStep fork op = some run) (evm : Evm fork Meter) : Cls t o (run evm) := by
  cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | (simp only [returnStep, revertStep, haltWithOutput]; cls)

/-- Each instruction of the environment is allowed. -/
private theorem cls_environmentStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : environmentStep fork op = some run) (evm : Evm fork Meter) : Cls t o (run evm) := by
  cases op <;> simp only [environmentStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | (simp only [blockhashStep, blobhashStep, readFrame]; cls)

/-- Each instruction that reads another account is allowed. -/
private theorem cls_accountStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : accountStep fork op = some run) (evm : Evm fork Meter) : Cls t o (run evm) := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hstep
  all_goals (try split at hstep) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hstep) <;>
    (try subst hstep)
  all_goals first
    | cases hstep
    | (simp only [balanceStep, extcodehashStep, extcodesizeStep, extcodecopyStep, readFrame]; cls)

/-- Each instruction of a log is allowed. -/
private theorem cls_logOpStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : logOpStep op = some run) (evm : Evm fork Meter) : Cls t o (run evm) := by
  cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  simp only [logStep]
  cls

/-- Each instruction of transient storage is allowed. -/
private theorem cls_transientStorageStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : transientStorageStep fork op = some run) (evm : Evm fork Meter) :
    Cls t o (run evm) := by
  cases op <;> simp only [transientStorageStep, reduceCtorEq] at hstep <;> split at hstep <;>
    simp only [Option.some.injEq, reduceCtorEq] at hstep <;> subst hstep <;>
    simp only [tloadStep, tstoreStep] <;> cls

/-- Each instruction of storage is allowed, at the target of its frame and the account there. -/
private theorem cls_storageStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : storageStep op = some run) (evm : Evm fork Meter) :
    Cls evm.message.currentTarget (evm.state.getAccountOptional evm.message.currentTarget)
      (run evm) := by
  cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hstep <;>
    subst hstep
  · simp only [sloadStep]
    cls
  · exact cls_sstoreStep evm

/-- SELFDESTRUCT is allowed. -/
private theorem cls_selfdestructOpStep [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : selfdestructOpStep fork op = some run) (evm : Evm fork Meter) :
    Cls t o (run evm) := by
  cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  simp only [selfdestructStep, finishSelfdestruct]
  cls

/-- An instruction that gives the next frame is allowed at the target of its frame. -/
private theorem cls_instruction [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hrun : instruction fork op = some run) (evm : Evm fork Meter) :
    Cls evm.message.currentTarget (evm.state.getAccountOptional evm.message.currentTarget)
      (run evm) := by
  unfold Evm.instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact cls_stackOnlyStep hf evm
  rcases orElse_eq_some hrun with hf | hrun
  · exact cls_controlFlowStep hf evm
  rcases orElse_eq_some hrun with hf | hrun
  · exact cls_memoryDataStep hf evm
  rcases orElse_eq_some hrun with hf | hrun
  · exact cls_returnOpStep hf evm
  rcases orElse_eq_some hrun with hf | hrun
  · exact cls_environmentStep hf evm
  rcases orElse_eq_some hrun with hf | hrun
  · exact cls_accountStep hf evm
  rcases orElse_eq_some hrun with hf | hrun
  · exact cls_storageStep hf evm
  rcases orElse_eq_some hrun with hf | hrun
  · exact cls_transientStorageStep hf evm
  rcases orElse_eq_some hrun with hf | hf
  · exact cls_logOpStep hf evm
  · exact cls_selfdestructOpStep hf evm

/-! ## The calls and the creations -/

/-- A step of a call instruction is allowed. -/
private theorem cls_callStep [LawfulGasMeter Meter] {kind : CallKind} (evm : Evm fork Meter) :
    Cls t o (callStep kind evm) := by
  simp only [callStep, popCallOperands, popCallValue, accessDelegation, payCall, finishCall,
    genericCall, skipCall]
  cls

/-- A step of CREATE or CREATE2 is allowed. -/
private theorem cls_createStep [LawfulGasMeter Meter] {create2 : Bool} (evm : Evm fork Meter) :
    Cls t o (createStep create2 evm) := by
  simp only [createStep, popSalt, genericCreate, launchCreate, creationAddress, skipCall]
  cls

/-- An instruction that may send a message is allowed. -/
private theorem cls_messageInstruction [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)}
    (hrun : messageInstruction fork op = some run) (evm : Evm fork Meter) :
    Cls t o (run evm) := by
  unfold Evm.messageInstruction at hrun
  rcases orElse_eq_some hrun with hc | hc
  · cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals (try split at hc) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hc) <;>
      (try subst hc)
    all_goals first
      | cases hc
      | exact cls_callStep evm
  · cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals (try split at hc) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hc) <;>
      (try subst hc)
    all_goals first
      | cases hc
      | exact cls_createStep evm

/-! ## A step -/

/-- A step fails with an error of the state only in three ways.

It fails for a missing code.

It fails for no account at the address it runs at, which has none in the state of the frame.

It fails for a balance that would reach `2^256`. -/
theorem step_eq_error_state [LawfulGasMeter Meter] {evm : Evm fork Meter} {e : StateError}
    (h : step fork evm = .error (.state e)) :
    (∃ codeHash, e = .missingCode codeHash) ∨
      (e = .noAccount evm.message.currentTarget ∧
        evm.state.getAccountOptional evm.message.currentTarget = none) ∨
      ∃ address, e = .balanceOverflow address := by
  refine (show Cls evm.message.currentTarget
    (evm.state.getAccountOptional evm.message.currentTarget) (step fork evm) from ?_) e h
  unfold step
  split
  · dsimp only
    split
    · exact Cls.throw nofun
    · split
      · exact Cls.map _ (cls_instruction (by assumption) evm)
      · split
        · exact cls_messageInstruction (by assumption) evm
        · exact Cls.throw nofun
  · exact Cls.map _ (Cls.ok _)

/-- No step fails for a balance below the amount that it takes. -/
theorem step_ne_insufficientBalance [LawfulGasMeter Meter] (evm : Evm fork Meter)
    (address : Address) : step fork evm ≠ .error (.state (.insufficientBalance address)) := by
  intro h
  rcases step_eq_error_state h with ⟨_, h⟩ | ⟨h, -⟩ | ⟨_, h⟩ <;> cases h

end EthLib.Execution.Evm
