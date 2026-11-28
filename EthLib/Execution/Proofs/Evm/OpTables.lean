module

public import EthLib.Execution.Proofs.Evm.OpTables.Instructions
public import EthLib.Execution.Proofs.Evm.OpTables.Messages
public import EthLib.Execution.Proofs.Evm.OpTables.FailsState
public import EthLib.Execution.Proofs.Evm.OpTables.FailsMessages
public import EthLib.Execution.Proofs.Evm.OpTables.Covers
public import EthLib.Execution.Proofs.Evm.Interpreter
public import EthLib.Execution.Proofs.Evm.Op

/-!
# Proofs: the step of every opcode follows its tables, at every fork

A step takes and leaves the words of its opcode, and pays its constant price, as the tables say.

So a step fails, or halts with an error, when the stack holds too few words or would hold too many.

It does so too when the frame holds less gas than the price.

A stack error comes only from the words of the tables, and a short stack never aborts the run.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)

variable {fork : Fork} {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]

/-- The step of a frame follows the tables of its opcode, at every fork.

The byte at the program counter decodes to `op`, whose immediate byte gives the words of the tables.

A step that succeeds takes those words and keeps the code.

It leaves its words and pays at least the constant price, or it halts with an error. -/
theorem step_followsTables {evm : Evm fork Meter} {op : Op} {takes leaves : Nat}
    {result : StepResult fork Meter} (hlt : evm.pc < evm.code.size)
    (hop : Op.ofByte fork evm.code[evm.pc] = some op)
    (hwords : op.stackWords (immediateByte evm.code evm.pc) = some (takes, leaves))
    (h : step fork evm = .ok result) :
    result.FollowsTables takes leaves (op.constantGas fork) evm := by
  unfold step at h
  rw [dite_eq_left_of_eq_true (eq_true hlt)] at h
  simp only [hop] at h
  split at h
  · -- An instruction that gives the next frame.
    rename_i run hrun
    obtain ⟨after, hr, rfl⟩ := Base.map_ok_iff.mp h
    exact instruction_follows hrun hwords hr
  · split at h
    · -- A call or a creation.
      rename_i run hrun
      exact messageInstruction_follows hrun hwords h
    · cases h

/-- A step fails when the immediate byte of its opcode encodes no words for the tables.

Its error halts the frame, and aborts nothing. -/
theorem step_eq_error_of_stackWords_eq_none {evm : Evm fork Meter} {op : Op}
    (hlt : evm.pc < evm.code.size) (hop : Op.ofByte fork evm.code[evm.pc] = some op)
    (hwords : op.stackWords (immediateByte evm.code evm.pc) = none) :
    ∃ e, e.aborts = false ∧ step fork evm = .error e := by
  -- Only DUPN, SWAPN and EXCHANGE read words from their immediate byte, from Glamsterdam.
  have since := (Op.ofByte_eq_some_iff.mp hop).2
  unfold step
  rw [dite_eq_left_of_eq_true (eq_true hlt)]
  simp only [hop]
  cases op <;> simp only [Op.stackWords, reduceCtorEq, Option.map_eq_none_iff] at hwords
  · have hi : instruction (Meter := Meter) fork .dupn = some dupnStep := by
      simp only [instruction, stackOnlyStep, show Fork.glamsterdam ≤ fork from since, ↓reduceIte]
      rfl
    obtain ⟨e, he, h⟩ := dupnStep_eq_error hwords
    exact ⟨e, he, by simp only [hi, h]; rfl⟩
  · have hi : instruction (Meter := Meter) fork .swapn = some swapnStep := by
      simp only [instruction, stackOnlyStep, show Fork.glamsterdam ≤ fork from since, ↓reduceIte]
      rfl
    obtain ⟨e, he, h⟩ := swapnStep_eq_error hwords
    exact ⟨e, he, by simp only [hi, h]; rfl⟩
  · have hi : instruction (Meter := Meter) fork .exchange = some exchangeStep := by
      simp only [instruction, stackOnlyStep, show Fork.glamsterdam ≤ fork from since, ↓reduceIte]
      rfl
    obtain ⟨e, he, h⟩ := exchangeStep_eq_error hwords
    exact ⟨e, he, by simp only [hi, h]; rfl⟩

/-- Each error of the step of a frame follows the tables of its opcode, at every fork.

A stack error comes only from the words of the tables, and a short stack halts the frame. -/
theorem step_failsByTables {evm : Evm fork Meter} {op : Op} {takes leaves : Nat} {e : EvmError}
    (hlt : evm.pc < evm.code.size) (hop : Op.ofByte fork evm.code[evm.pc] = some op)
    (hwords : op.stackWords (immediateByte evm.code evm.pc) = some (takes, leaves))
    (h : step fork evm = .error e) : FailsByTables takes leaves evm e := by
  unfold step at h
  rw [dite_eq_left_of_eq_true (eq_true hlt)] at h
  simp only [hop] at h
  split at h
  · -- An instruction that gives the next frame.
    rename_i run hrun
    cases hr : run evm with
    | error e' =>
      simp only [hr, Functor.map, Except.map, Except.error.injEq] at h
      subst h
      exact instruction_fails hrun hwords hr
    | ok after => simp [hr, Functor.map, Except.map] at h
  · rename_i hnone
    split at h
    · -- A call or a creation.
      rename_i run hrun
      exact messageInstruction_fails hrun hwords h
    · -- Every opcode of the fork has an instruction.
      rename_i hm
      rcases instruction_or_messageInstruction_isSome (Meter := Meter)
        (since_le_of_ofByte_eq_some hop) with hi | hi
      · simp [hnone] at hi
      · simp [hm] at hi

/-- A step halts the frame with an error when the stack holds fewer words than its opcode takes. -/
theorem step_eq_error_of_length_lt {evm : Evm fork Meter} {op : Op} {takes leaves : Nat}
    (hlt : evm.pc < evm.code.size) (hop : Op.ofByte fork evm.code[evm.pc] = some op)
    (hwords : op.stackWords (immediateByte evm.code evm.pc) = some (takes, leaves))
    (hlen : evm.stack.val.length < takes) :
    ∃ e, e.aborts = false ∧ step fork evm = .error e := by
  cases h : step fork evm with
  | error e => exact ⟨e, (step_failsByTables hlt hop hwords h).short hlen, rfl⟩
  | ok result =>
    -- Every result that succeeds has taken the words, which the stack lacks.
    have hf := step_followsTables hlt hop hwords h
    cases result with
    | next after => exact absurd hf.enough (Nat.not_le.mpr hlen)
    | child caller _ resume =>
      have := hf.taken
      omega

/-- A step fails with an underflow only when the stack holds fewer words than its opcode takes. -/
theorem length_lt_of_step_eq_stackUnderflow {evm : Evm fork Meter} {op : Op}
    {takes leaves : Nat} (hlt : evm.pc < evm.code.size)
    (hop : Op.ofByte fork evm.code[evm.pc] = some op)
    (hwords : op.stackWords (immediateByte evm.code evm.pc) = some (takes, leaves))
    (h : step fork evm = .error .stackUnderflow) : evm.stack.val.length < takes :=
  (step_failsByTables hlt hop hwords h).underflow rfl

/-- A step fails with an overflow only when the words of its opcode would overflow the stack. -/
theorem overflow_of_step_eq_stackOverflow {evm : Evm fork Meter} {op : Op}
    {takes leaves : Nat} (hlt : evm.pc < evm.code.size)
    (hop : Op.ofByte fork evm.code[evm.pc] = some op)
    (hwords : op.stackWords (immediateByte evm.code evm.pc) = some (takes, leaves))
    (h : step fork evm = .error .stackOverflow) :
    STACK_LIMIT + takes < evm.stack.val.length + leaves :=
  (step_failsByTables hlt hop hwords h).overflow rfl

/-- A step fails or halts with an error when its words would overflow the stack. -/
theorem step_halts_of_overflow {evm : Evm fork Meter} {op : Op} {takes leaves : Nat}
    (hlt : evm.pc < evm.code.size) (hop : Op.ofByte fork evm.code[evm.pc] = some op)
    (hwords : op.stackWords (immediateByte evm.code evm.pc) = some (takes, leaves))
    (hover : STACK_LIMIT + takes < evm.stack.val.length + leaves) :
    (∃ e, step fork evm = .error e) ∨
      ∃ mid e, e.aborts = false ∧ step fork evm = .ok (.next (exceptionalHalt mid e)) := by
  cases h : step fork evm with
  | error e => exact .inl ⟨e, rfl⟩
  | ok result =>
    have hf := step_followsTables hlt hop hwords h
    cases result with
    | next after =>
      rcases hf.goesOn with ⟨hlen, -⟩ | ⟨mid, e, he, -, -, rfl⟩
      · -- A stack holds at most 1024 words.
        have := after.stack.property
        unfold STACK_LIMIT at hover this
        omega
      · exact .inr ⟨mid, e, he, rfl⟩
    | child caller _ resume =>
      -- The caller has room for the words that it leaves.
      have := hf.taken
      have := hf.room
      omega

/-- A step fails or halts with an error when the frame holds less gas than the constant price.

The gas held is the gas left and what a rollback of state gas gives back. -/
theorem step_halts_of_gasHeld_lt {evm : Evm fork Meter} {op : Op}
    (hlt : evm.pc < evm.code.size) (hop : Op.ofByte fork evm.code[evm.pc] = some op)
    (hgas : GasMeter.gasHeld evm.gas < op.constantGas fork) :
    (∃ e, step fork evm = .error e) ∨
      ∃ mid e, e.aborts = false ∧ step fork evm = .ok (.next (exceptionalHalt mid e)) := by
  cases hw : op.stackWords (immediateByte evm.code evm.pc) with
  | none =>
    obtain ⟨e, -, he⟩ := step_eq_error_of_stackWords_eq_none hlt hop hw
    exact .inl ⟨e, he⟩
  | some words =>
    cases h : step fork evm with
    | error e => exact .inl ⟨e, rfl⟩
    | ok result =>
      have hf := step_followsTables hlt hop hw h
      cases result with
      | next after =>
        rcases hf.goesOn with ⟨-, hpay⟩ | ⟨mid, e, he, -, -, rfl⟩
        · omega
        · exact .inr ⟨mid, e, he, rfl⟩
      | child caller _ resume =>
        have := hf.pays
        omega

/-- A step fails or halts with an error when the gas left of the frame is below the constant price.

So a step that goes on had the gas left for its constant price.

The meter is that of Glamsterdam, whose gas held can exceed its gas left. -/
theorem step_halts_of_gasLeft_lt {evm : Evm fork StateGasMeter} {op : Op}
    (hlt : evm.pc < evm.code.size) (hop : Op.ofByte fork evm.code[evm.pc] = some op)
    (hgas : GasMeter.gasLeft evm.gas < op.constantGas fork) :
    (∃ e, step fork evm = .error e) ∨
      ∃ mid e, e.aborts = false ∧ step fork evm = .ok (.next (exceptionalHalt mid e)) := by
  cases h : step fork evm with
  | error e => exact .inl ⟨e, rfl⟩
  | ok result =>
    right
    unfold step at h
    rw [dite_eq_left_of_eq_true (eq_true hlt)] at h
    simp only [hop] at h
    split at h
    · -- An instruction that gives the next frame charges its price first, or halts.
      rename_i run hrun
      obtain ⟨after, hr, rfl⟩ := Base.map_ok_iff.mp h
      rcases instruction_covers hrun hr with hc | ⟨mid, e, he, rfl⟩
      · omega
      · exact ⟨mid, e, he, rfl⟩
    · split at h
      · -- A call or a creation charges its price first, or halts.
        rename_i run hrun
        rcases messageInstruction_covers hrun h with hc | ⟨mid, e, he, rfl⟩
        · omega
        · exact ⟨mid, e, he, rfl⟩
      · cases h

end EthLib.Execution.Evm
