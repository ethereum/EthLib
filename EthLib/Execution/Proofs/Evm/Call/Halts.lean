module

public import EthLib.Execution.Proofs.Evm.Call.Run

/-!
# Proofs: a frame that ends a call or a creation halts only with an error that does not abort

A frame records the error that stopped it, or none when it succeeded.

An error that aborts the whole execution never stops one frame: the run fails with it instead.

A step that fails with any other error halts its frame with that error.

REVERT halts its frame with its own error, which does not abort.

A failed precompile halts its frame with its own error.

A lawful meter that cannot charge halts it for lack of gas.

A creation that cannot deposit its code halts for lack of gas, or for code that starts with 0xEF.

So the error of every frame that a call or a creation returns does not abort.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The error of a frame after a step -/

/-- The second frame keeps the error of the first, or records an error that does not abort. -/
private def ErrKept (a b : Evm fork Meter) : Prop :=
  b.error = a.error ∨ ∃ e, b.error = some e ∧ e.aborts = false

/-- What a step gives keeps the error of the frame, and so does the frame that resumes. -/
private def ResultKept (evm : Evm fork Meter) : StepResult fork Meter → Prop
  | .next after => ErrKept evm after
  | .child caller _ resume =>
    ErrKept evm caller ∧ ∀ child after, resume child = .ok after → ErrKept evm after

/-- The frame records no error, or one that does not abort. -/
private def NoAbort (evm : Evm fork Meter) : Prop :=
  ∀ e, evm.error = some e → e.aborts = false

omit [GasMeter Meter] in
/-- The relation holds from any frame with the same error. -/
private theorem ErrKept.of_error_eq {a a' b : Evm fork Meter} (he : a'.error = a.error)
    (h : ErrKept a' b) : ErrKept a b := by
  unfold ErrKept at *
  rw [← he]
  exact h

omit [GasMeter Meter] in
/-- A result that keeps the error of one frame keeps that of any frame with the same error. -/
private theorem ResultKept.of_error_eq {a a' : Evm fork Meter} {r : StepResult fork Meter}
    (he : a'.error = a.error) (h : ResultKept a' r) : ResultKept a r := by
  cases r with
  | next after => exact ErrKept.of_error_eq he h
  | child caller message resume =>
    exact ⟨ErrKept.of_error_eq he h.1, fun c x hr => ErrKept.of_error_eq he (h.2 c x hr)⟩

omit [GasMeter Meter] in
/-- A frame related to one with no error that aborts has none either. -/
private theorem ErrKept.noAbort {a b : Evm fork Meter} (h : ErrKept a b) (ha : NoAbort a) :
    NoAbort b := by
  intro e he
  rcases h with h | ⟨e', h, h'⟩
  · exact ha e (h ▸ he)
  · rw [h] at he
    cases he
    exact h'

/-- The rest of an instruction that keeps its reads gives its result, or halts without abort. -/
private theorem keepReads_ok {α : Type} {evm : Evm fork Meter} {halted : Evm fork Meter → α}
    {rest : Except EvmError α} {result : α} (h : keepReads evm halted rest = .ok result) :
    rest = .ok result ∨ ∃ e, e.aborts = false ∧ result = halted (exceptionalHalt evm e) := by
  unfold keepReads at h
  split at h
  · split at h
    · cases h
    · cases h
      exact .inr ⟨_, Bool.eq_false_iff.mpr ‹_›, rfl⟩
  · cases h
    exact .inl rfl

/-- A bind on a success applies the continuation. -/
private theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a : Except ε α) >>= f = f a := rfl

omit [GasMeter Meter] in
/-- The pops of the topics of a log keep the error. -/
private theorem error_popTopics {evm : Evm fork Meter} {n : Nat}
    {r : List Base.Hash32 × Evm fork Meter} (h : popTopics evm n = .ok r) :
    r.2.error = evm.error := by
  induction n generalizing evm r with
  | zero => cases h; rfl
  | succ k ih =>
    simp only [popTopics, popWord, bind_assoc, pure_bind] at h
    obtain ⟨_, _, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have := ih h1
    exact this

set_option hygiene false in
/-- Unfold an instruction into its parts, split it, and relate each frame it gives. -/
local macro "errkept_tac" : tactic => `(tactic| (
  simp only [binaryOp, unaryOp, ternaryOp, expStep, keccak256Step, popStep, pushN, dupN, swapN,
    dupnStep, swapnStep, exchangeStep, popWord, pushWord, chargeGas, chargeStateGas,
    refillStateGas, chargeGasAndMemory, readFrame, advance, recordAccountRead, recordStorageRead,
    stopStep, jumpStep, jumpiStep, jumpdestStep, mloadStep, mstoreStep, mstore8Step, mcopyStep,
    calldataloadStep, copyToMemory, returndatacopyStep, haltWithOutput, returnStep, revertStep,
    blockhashStep, blobhashStep, balanceStep, extcodesizeStep, extcodecopyStep, extcodehashStep,
    accessAddress, accessStorageKey, accountCode, sloadStep, sstoreStep, tloadStep, tstoreStep,
    logStep, selfdestructStep, finishSelfdestruct, checkGas, bind_assoc, pure_bind] at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := Base.bind_ok_iff.mp h)
    | (rcases keepReads_ok h with h | ⟨_, _, rfl⟩)
    | split at h)
  all_goals first
    | (cases h; done)
    | (cases h; exact .inl rfl)
    | (exact .inr ⟨_, rfl, ‹_›⟩)
    | (cases h; exact .inr ⟨_, rfl, rfl⟩)))

set_option hygiene false in
/-- Pick the instruction of an opcode from a table, for each opcode. -/
local macro "pick_tac " table:ident : tactic => `(tactic| (
  cases op <;> simp only [$table:ident, reduceCtorEq] at hf
  all_goals (try split at hf) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hf) <;>
    (try subst hf)
  all_goals try cases hf))

/-- Each instruction of the stack, and KECCAK256, keeps the error. -/
private theorem errKept_stackOnly {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} (hf : stackOnlyStep fork op = some f)
    {evm after : Evm fork Meter} (h : f evm = .ok after) : ErrKept evm after := by
  pick_tac stackOnlyStep
  all_goals errkept_tac

/-- Each instruction that moves or reads the program counter keeps the error. -/
private theorem errKept_controlFlow {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} (hf : controlFlowStep op = some f)
    {evm after : Evm fork Meter} (h : f evm = .ok after) : ErrKept evm after := by
  pick_tac controlFlowStep
  all_goals errkept_tac

/-- Each instruction of memory and of the call data keeps the error. -/
private theorem errKept_memoryData {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} (hf : memoryDataStep op = some f)
    {evm after : Evm fork Meter} (h : f evm = .ok after) : ErrKept evm after := by
  pick_tac memoryDataStep
  all_goals errkept_tac

/-- RETURN keeps the error, and REVERT records its own, which does not abort. -/
private theorem errKept_returnOp {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} (hf : returnOpStep fork op = some f)
    {evm after : Evm fork Meter} (h : f evm = .ok after) : ErrKept evm after := by
  pick_tac returnOpStep
  all_goals errkept_tac

/-- Each instruction that reads the environment keeps the error. -/
private theorem errKept_environment {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hf : environmentStep fork op = some f) {evm after : Evm fork Meter}
    (h : f evm = .ok after) : ErrKept evm after := by
  pick_tac environmentStep
  all_goals errkept_tac

/-- Each instruction that reads an account keeps the error, or halts without abort. -/
private theorem errKept_account {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} (hf : accountStep fork op = some f)
    {evm after : Evm fork Meter} (h : f evm = .ok after) : ErrKept evm after := by
  pick_tac accountStep
  all_goals errkept_tac

/-- SLOAD and SSTORE keep the error, or halt without abort. -/
private theorem errKept_storage {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} (hf : storageStep op = some f)
    {evm after : Evm fork Meter} (h : f evm = .ok after) : ErrKept evm after := by
  pick_tac storageStep
  all_goals errkept_tac

/-- TLOAD and TSTORE keep the error. -/
private theorem errKept_transient {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hf : transientStorageStep fork op = some f) {evm after : Evm fork Meter}
    (h : f evm = .ok after) : ErrKept evm after := by
  pick_tac transientStorageStep
  all_goals errkept_tac

/-- Each LOG instruction keeps the error. -/
private theorem errKept_log {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} (hf : logOpStep op = some f)
    {evm after : Evm fork Meter} (h : f evm = .ok after) : ErrKept evm after := by
  pick_tac logOpStep
  simp only [logStep, popWord, chargeGasAndMemory, chargeGas, advance, bind_assoc, pure_bind] at h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, hp, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · cases h
  · cases h
    have := error_popTopics hp
    exact .inl this

/-- SELFDESTRUCT keeps the error, or halts without abort. -/
private theorem errKept_selfdestruct {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hf : selfdestructOpStep fork op = some f) {evm after : Evm fork Meter}
    (h : f evm = .ok after) : ErrKept evm after := by
  pick_tac selfdestructOpStep
  all_goals errkept_tac

/-- Each instruction that gives the next frame keeps the error, or halts without abort. -/
private theorem errKept_instruction {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hrun : instruction fork op = some run) {evm after : Evm fork Meter}
    (h : run evm = .ok after) : ErrKept evm after := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact errKept_stackOnly hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact errKept_controlFlow hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact errKept_memoryData hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact errKept_returnOp hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact errKept_environment hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact errKept_account hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact errKept_storage hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact errKept_transient hf h
  rcases orElse_eq_some hrun with hf | hf
  · exact errKept_log hf h
  · exact errKept_selfdestruct hf h

/-! ## Calls and creations -/

set_option hygiene false in
/-- Unfold the end of a call or a creation, split it, and relate each result and resume. -/
local macro "errkept_msg_tac" : tactic => `(tactic| (
  simp only [pushWord, chargeGas, chargeStateGas, refillStateGas, advance, recordAccountRead,
    accessAddress, genericCall, skipCall, bind_assoc, pure_bind, map_bind, map_pure] at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := Base.bind_ok_iff.mp h)
    | (obtain ⟨_, _, h⟩ := Base.map_ok_iff.mp h)
    | (rcases keepReads_ok h with h | ⟨_, _, rfl⟩)
    | split at h)
  all_goals first
    | (cases h; done)
    | (cases h; exact .inl rfl)
    | (exact .inr ⟨_, rfl, ‹_›⟩)
    | (cases h; refine ⟨.inl rfl, fun child after h => ?_⟩
       simp only [resumeCall, resumeCreate, incorporateChild, pushWord, refillStateGas, advance,
         bind_assoc, pure_bind] at h
       repeat' (first | (obtain ⟨_, _, h⟩ := Base.bind_ok_iff.mp h) | split at h)
       all_goals first | (cases h; done) | (cases h; exact .inl rfl))))

omit [GasMeter Meter] in
/-- A pop keeps the error. -/
private theorem error_popWord {evm : Evm fork Meter} {r : Base.U256 × Evm fork Meter}
    (h : popWord evm = .ok r) : r.2.error = evm.error := by
  simp only [popWord] at h
  obtain ⟨_, _, h⟩ := Base.bind_ok_iff.mp h
  cases h
  rfl

omit [GasMeter Meter] in
/-- The pops of the operands of a call keep the error. -/
private theorem error_popCallOperands {kind : CallKind} {evm : Evm fork Meter}
    {r : CallOperands × Evm fork Meter} (h : popCallOperands kind evm = .ok r) :
    r.2.error = evm.error := by
  simp only [popCallOperands, popCallValue, popWord, bind_assoc, pure_bind] at h
  repeat' (first
    | (split at h <;> try simp only [bind_assoc, pure_bind, ok_bind] at h)
    | (obtain ⟨_, _, h⟩ := Base.bind_ok_iff.mp h))
  all_goals cases h; rfl

/-- The access to a delegate keeps the error. -/
private theorem error_accessDelegation {evm : Evm fork Meter} {address : Base.Address}
    {known : Nat} {r : Callee × Evm fork Meter} (h : accessDelegation evm address known = .ok r) :
    r.2.error = evm.error := by
  simp only [accessDelegation, accessAddress, accountCode, checkGas, recordAccountRead] at h
  repeat' (first | (obtain ⟨_, _, h⟩ := Base.bind_ok_iff.mp h) | split at h)
  all_goals first | (cases h; done) | (cases h; rfl)

/-- The payment of a call keeps the error. -/
private theorem error_payCall {kind : CallKind} {call : CallOperands} {m x n : Nat}
    {evm : Evm fork Meter} {r : Nat × Evm fork Meter}
    (h : payCall kind call m x n evm = .ok r) : r.2.error = evm.error := by
  simp only [payCall, chargeGas, chargeStateGas, bind_assoc, pure_bind] at h
  repeat' (first | (obtain ⟨_, _, h⟩ := Base.bind_ok_iff.mp h) | split at h)
  all_goals first | (cases h; done) | (cases h; rfl)

/-- The end of a call instruction keeps the error, and so does the caller that resumes. -/
private theorem resultKept_finishCall {kind : CallKind} {call : CallOperands} {callee : Callee}
    {s n e : Nat} {evm : Evm fork Meter} {result : StepResult fork Meter}
    (h : finishCall kind call callee s n e evm = .ok result) : ResultKept evm result := by
  simp only [finishCall] at h
  errkept_msg_tac

/-- A call instruction keeps the error, or halts without abort. -/
private theorem resultKept_callStep {kind : CallKind} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : callStep kind evm = .ok result) :
    ResultKept evm result := by
  unfold callStep at h
  obtain ⟨⟨call, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  have err1 : e1.error = evm.error := error_popCallOperands h1
  dsimp only at h
  split at h
  · obtain ⟨_, h, -⟩ := Base.bind_ok_iff.mp h
    cases h
  rcases ha : accessAddress e1 call.address with ⟨cold, e2⟩
  have err2 : e2.error = e1.error := by
    have := congrArg (fun p => p.2.error) ha
    simp only [accessAddress] at this
    split at this <;> exact this.symm
  simp only [ha] at h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_ok h with h | ⟨e, he, rfl⟩
  · obtain ⟨p3, h3, h⟩ := Base.bind_ok_iff.mp h
    have err3 := error_accessDelegation h3
    rcases keepReads_ok h with h | ⟨e, he, rfl⟩
    · obtain ⟨p4, h4, h⟩ := Base.bind_ok_iff.mp h
      have err4 := error_payCall h4
      exact (resultKept_finishCall h).of_error_eq (err4.trans (err3.trans (err2.trans err1)))
    · exact .inr ⟨e, rfl, he⟩
  · exact .inr ⟨e, rfl, he⟩

/-- The launch of a creation keeps the error, and so does the creator that resumes. -/
private theorem resultKept_launchCreate {evm : Evm fork Meter} {value : Base.U256}
    {initCode : ByteArray} {salt : Option Base.U256} {result : StepResult fork Meter}
    (h : launchCreate evm value initCode salt = .ok result) : ResultKept evm result := by
  simp only [launchCreate] at h
  errkept_msg_tac

omit [GasMeter Meter] in
/-- The pop of the salt keeps the error. -/
private theorem error_popSalt {create2 : Bool} {evm : Evm fork Meter}
    {r : Option Base.U256 × Evm fork Meter} (h : popSalt create2 evm = .ok r) :
    r.2.error = evm.error := by
  unfold popSalt at h
  split at h
  · obtain ⟨p, hp, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact error_popWord hp
  · cases h
    rfl

/-- A charge of gas and memory keeps the error. -/
private theorem error_chargeGasAndMemory {evm after : Evm fork Meter} {cost : Nat}
    {ranges : List (Base.U256 × Base.U256)} (h : chargeGasAndMemory evm cost ranges = .ok after) :
    after.error = evm.error := by
  simp only [chargeGasAndMemory, chargeGas, bind_assoc, pure_bind] at h
  obtain ⟨_, _, h⟩ := Base.bind_ok_iff.mp h
  cases h
  rfl

/-- CREATE and CREATE2 keep the error, or halt without abort. -/
private theorem resultKept_createStep {create2 : Bool} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : createStep create2 evm = .ok result) :
    ResultKept evm result := by
  unfold createStep at h
  dsimp only at h
  split at h
  · obtain ⟨_, h, -⟩ := Base.bind_ok_iff.mp h
    cases h
  obtain ⟨p1, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨p2, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨p3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨p4, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
  have err := (error_chargeGasAndMemory h5).trans ((error_popSalt h4).trans
    ((error_popWord h3).trans ((error_popWord h2).trans (error_popWord h1))))
  unfold genericCreate at h
  split at h
  · cases h
  split at h
  · cases h
  exact (resultKept_launchCreate h).of_error_eq err

/-- Each instruction that may send a message keeps the error, or halts without abort. -/
private theorem resultKept_messageInstruction {op : Op}
    {f : Evm fork Meter → Except EvmError (StepResult fork Meter)}
    (hf : messageInstruction fork op = some f) {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : f evm = .ok result) : ResultKept evm result := by
  unfold messageInstruction at hf
  rcases orElse_eq_some hf with hf | hf
  · pick_tac callInstruction
    all_goals exact resultKept_callStep h
  · pick_tac createInstruction
    all_goals exact resultKept_createStep h

/-- Each step keeps the error, or halts without abort, and so does the frame that resumes. -/
private theorem resultKept_step {evm : Evm fork Meter} {result : StepResult fork Meter}
    (h : step fork evm = .ok result) : ResultKept evm result := by
  unfold step at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · rename_i hrun
        obtain ⟨after, hr, rfl⟩ := Base.map_ok_iff.mp h
        exact errKept_instruction hrun hr
      · split at h
        · exact resultKept_messageInstruction ‹_› h
        · cases h
  · obtain ⟨after, hr, rfl⟩ := Base.map_ok_iff.mp h
    simp only [stopStep, Except.ok.injEq] at hr
    subst hr
    exact .inl rfl

/-! ## Runs and messages -/

/-- A run from a frame with no error that aborts ends with none, whatever runs its messages. -/
private theorem noAbort_runFrame [LawfulGasMeter Meter] {bound : Nat}
    {runChild : MessageRunner fork Meter bound} {evm after : Evm fork Meter}
    {within : GasMeter.gasHeld evm.gas ≤ bound} (start : NoAbort evm)
    (h : runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok after) :
    NoAbort after := by
  fun_induction runFrame (step fork) (step_decreases fork) bound runChild evm within
  case case1 => cases h
  case case2 =>
    cases h
    rename_i hab
    intro e' he
    cases he
    exact Bool.eq_false_iff.mpr hab
  case case3 =>
    rename_i result _ ih
    exact ih ((resultKept_step result : ErrKept _ _).noAbort start) h
  case case4 => cases h
  case case5 => cases h
  case case6 =>
    cases h
    rename_i hab
    intro e' he
    cases he
    exact Bool.eq_false_iff.mpr hab
  case case7 =>
    rename_i hchild _ _ _ _ _ resumed _ ih
    exact ih (((resultKept_step hchild).2 _ _ resumed).noAbort start) h
  case case8 => cases h; exact start

/-- A precompile fails only for its own failure or for lack of gas, which do not abort. -/
private theorem noAbort_runPrecompile [LawfulGasMeter Meter] {address : Nat}
    {evm after : Evm fork Meter} (h : runPrecompile fork address evm = some after)
    (start : NoAbort evm) : NoAbort after := by
  unfold runPrecompile at h
  split at h
  · cases h
  · cases h
    intro e he
    cases he
    rfl
  · split at h
    · rename_i hc
      cases h
      intro e he
      cases he
      rw [LawfulGasMeter.charge_error hc]
      rfl
    · cases h
      exact start

/-- The rollback of a message keeps its error. -/
private theorem noAbort_rollbackOnError {snapshot : TransactionState} {evm : Evm fork Meter}
    (h : NoAbort evm) : NoAbort (rollbackOnError snapshot evm) := by
  unfold rollbackOnError
  split
  · exact h
  · exact h

/-- A lawful meter fails the deposit of code only for lack of gas. -/
private theorem chargeCodeDeposit_error [LawfulGasMeter Meter] {meter : Meter} {size : Nat}
    {e : EvmError} (h : chargeCodeDeposit fork meter size = .error e) : e = .outOfGas := by
  unfold chargeCodeDeposit at h
  split at h
  · cases h1 : GasMeter.charge meter (GasCosts.OPCODE_KECCAK256_PER_WORD * wordCount size) with
    | error e' =>
      rw [h1] at h
      cases h
      exact LawfulGasMeter.charge_error h1
    | ok m =>
      rw [h1] at h
      exact LawfulGasMeter.chargeState_error h
  · exact LawfulGasMeter.charge_error h

/-- The deposit of code records only an error that does not abort. -/
private theorem noAbort_depositCode [LawfulGasMeter Meter] {snapshot : TransactionState}
    {evm after : Evm fork Meter} (start : NoAbort evm)
    (h : depositCode fork snapshot evm = .ok after) : NoAbort after := by
  unfold depositCode at h
  dsimp only at h
  split at h
  · cases h
    exact start
  split at h
  · cases h
    intro e he
    cases he
    rfl
  split at h
  · cases h
    intro e he
    cases he
    rfl
  split at h
  · rename_i hc
    cases h
    split
    · intro e he
      cases he
      rw [chargeCodeDeposit_error hc]
      rfl
    · exact start
  split at h
  · cases h
    intro e he
    cases he
    rfl
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact start

/-- Every call and creation that returns a frame records no error that aborts. -/
private theorem processMessage_noAbort [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate)
      (meter : Meter) (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        NoAbort ended.val) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate)
      (meter : Meter) (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        NoAbort ended.val) :=
  processMessage_frame_byKind (F := fun a b => NoAbort a → NoAbort b)
    (Mcall := fun _ _ _ _ ended => NoAbort ended) (Mcreate := fun _ _ _ _ ended => NoAbort ended)
    (fun _ _ h start => noAbort_runFrame start h)
    (fun _ _ _ start => start)
    (fun _ _ h start => noAbort_runPrecompile h start)
    (fun _ hF => noAbort_rollbackOnError (hF fun _ he => by cases he))
    (fun _ hm hd => noAbort_depositCode hm hd) n

/-- The error that the frame of a call records, when the call returns, does not abort. -/
theorem error_processMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended) {e : EvmError}
    (he : ended.val.error = some e) : e.aborts = false :=
  (processMessage_noAbort message.gas).1 message state substate meter held rfl ended h e he

/-- The error that the frame of a creation records, when it returns, does not abort. -/
theorem error_processCreateMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processCreateMessage fork message state substate meter held = .ok ended)
    {e : EvmError} (he : ended.val.error = some e) : e.aborts = false :=
  (processMessage_noAbort message.gas).2 message state substate meter held rfl ended h e he

end EthLib.Execution.Evm
