module

public import EthLib.Execution.Evm.Interpreter

/-!
# Proofs: `Evm.Interpreter`

A step past the end of the code stops the frame, as STOP does.

A step on a byte that is no opcode at the fork fails with that byte.

The loop leaves a stopped frame as it is.

A step on a call or a creation runs it.

A step on an opcode with no instruction yet fails with an error that aborts the run.

No opcode lacks an instruction: each opcode has one at every fork from the fork that adds it.

So a step never fails at its dispatch with that error.

A step that fails halts the frame with no gas and no output, unless its error aborts the run.

Then the whole run fails with that error.

A step that succeeds lets the loop go on from the next frame.

Every run that succeeds ends with a stopped frame.

A run keeps the size of memory a multiple of 32 when each of its steps keeps it.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- A step past the end of the code stops the frame and moves past the end. -/
theorem step_of_size_le {evm : Evm fork Meter} (h : evm.code.size ≤ evm.pc) :
    step fork evm = .ok (.next (advance { evm with running := false })) := by
  simp [step, Nat.not_lt.mpr h, stopStep, Functor.map, Except.map]

/-- A step on a byte that is no opcode at the fork fails with that byte. -/
theorem step_of_ofByte_eq_none {evm : Evm fork Meter} (h : evm.pc < evm.code.size)
    (none : Op.ofByte fork evm.code[evm.pc] = none) :
    step fork evm = .error (.invalidOpcode evm.code[evm.pc]) := by
  simp [step, h, none, throw, throwThe, MonadExceptOf.throw]

/-- A step on a call or a creation runs it.

A step on an opcode with no instruction yet fails with an error that aborts the run. -/
theorem step_of_instruction_eq_none {evm : Evm fork Meter} {op : Op}
    (h : evm.pc < evm.code.size) (decoded : Op.ofByte fork evm.code[evm.pc] = some op)
    (noInstruction : instruction (Meter := Meter) fork op = none)
    (noMessage : messageInstruction (Meter := Meter) fork op = none) :
    step fork evm = .error (.unspecifiedOpcode evm.code[evm.pc]) := by
  simp [step, h, decoded, noInstruction, noMessage, throw, throwThe, MonadExceptOf.throw]

/-- A step on an opcode with an instruction runs that instruction. -/
theorem step_of_instruction {evm : Evm fork Meter} {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)} (h : evm.pc < evm.code.size)
    (decoded : Op.ofByte fork evm.code[evm.pc] = some op) (hrun : instruction fork op = some run) :
    step fork evm = .next <$> run evm := by
  simp [step, h, decoded, hrun]

/-- A step on a call or a creation runs it, and it may give a message to run first. -/
theorem step_of_messageInstruction {evm : Evm fork Meter} {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} (h : evm.pc < evm.code.size)
    (decoded : Op.ofByte fork evm.code[evm.pc] = some op)
    (noInstruction : instruction (Meter := Meter) fork op = none)
    (hrun : messageInstruction fork op = some run) :
    step fork evm = run evm := by
  simp [step, h, decoded, noInstruction, hrun]

/-- Every opcode has an instruction at each fork from the fork that adds it.

The instruction gives the next frame, or it may send a message, as a call or a creation does. -/
theorem instruction_or_messageInstruction_isSome {op : Op} (h : op.since ≤ fork) :
    (instruction (Meter := Meter) fork op).isSome ∨
      (messageInstruction (Meter := Meter) fork op).isSome := by
  cases op <;> simp only [Op.since] at h <;>
    simp [instruction, messageInstruction, stackOnlyStep, controlFlowStep, memoryDataStep,
      returnOpStep, environmentStep, accountStep, storageStep, transientStorageStep, logOpStep,
      selfdestructOpStep, callInstruction, createInstruction, h, HOrElse.hOrElse,
      OrElse.orElse, Option.orElse] <;>
    by_cases hp : Fork.paris ≤ fork <;> simp [hp]

/-- A byte decodes at a fork only to an opcode that the fork has. -/
theorem since_le_of_ofByte_eq_some {b : UInt8} {op : Op} (h : Op.ofByte fork b = some op) :
    op.since ≤ fork := by
  simp only [Op.ofByte, Option.filter_eq_some_iff] at h
  simpa using h.2

/-- A step on an opcode of the fork runs an instruction of that opcode.

So the step never takes the branch that fails with `unspecifiedOpcode`. -/
theorem step_of_ofByte_eq_some {evm : Evm fork Meter} {op : Op} (h : evm.pc < evm.code.size)
    (decoded : Op.ofByte fork evm.code[evm.pc] = some op) :
    (∃ run, instruction fork op = some run ∧ step fork evm = .next <$> run evm) ∨
      ∃ run, instruction (Meter := Meter) fork op = none ∧ messageInstruction fork op = some run ∧
        step fork evm = run evm := by
  rcases instruction_or_messageInstruction_isSome (Meter := Meter)
    (since_le_of_ofByte_eq_some decoded) with hi | hm
  · obtain ⟨run, hrun⟩ := Option.isSome_iff_exists.mp hi
    exact .inl ⟨run, hrun, step_of_instruction h decoded hrun⟩
  · cases hi : instruction (Meter := Meter) fork op with
    | some run => exact .inl ⟨run, rfl, step_of_instruction h decoded hi⟩
    | none =>
      obtain ⟨run, hrun⟩ := Option.isSome_iff_exists.mp hm
      exact .inr ⟨run, rfl, hrun, step_of_messageInstruction h decoded hi hrun⟩

section Loop

variable {step : Evm fork Meter → Except EvmError (StepResult fork Meter)}
  {decreases : ∀ {evm result}, evm.running = true → step evm = .ok result →
    result.Decreases evm}
  {bound : Nat}
  {runChild : MessageRunner fork Meter bound}

/-- The loop leaves a stopped frame as it is. -/
theorem runFrame_of_running_eq_false {evm : Evm fork Meter}
    {within : GasMeter.gasHeld evm.gas ≤ bound} (stopped : evm.running = false) :
    runFrame step decreases bound runChild evm within = .ok evm := by
  rw [runFrame]
  simp [stopped]

/-- A step that fails with an error that aborts makes the whole run fail with that error. -/
theorem runFrame_of_step_eq_abort {evm : Evm fork Meter}
    {within : GasMeter.gasHeld evm.gas ≤ bound} {e : EvmError}
    (running : evm.running = true) (failed : step evm = .error e) (aborts : e.aborts = true) :
    runFrame step decreases bound runChild evm within = .error e := by
  rw [runFrame]
  simp only [running, dite_true]
  split <;> simp_all

/-- A step that fails with any other error halts the frame exceptionally. -/
theorem runFrame_of_step_eq_error {evm : Evm fork Meter}
    {within : GasMeter.gasHeld evm.gas ≤ bound} {e : EvmError} (running : evm.running = true)
    (failed : step evm = .error e) (halts : e.aborts = false) :
    runFrame step decreases bound runChild evm within = .ok (exceptionalHalt evm e) := by
  rw [runFrame]
  simp only [running, dite_true]
  split <;> simp_all

/-- A step that gives the next frame lets the loop go on from it. -/
theorem runFrame_of_step_eq_next {evm after : Evm fork Meter}
    {within : GasMeter.gasHeld evm.gas ≤ bound} (running : evm.running = true)
    (next : step evm = .ok (.next after)) :
    runFrame step decreases bound runChild evm within =
      runFrame step decreases bound runChild after
        (Nat.le_trans (gasHeld_le_of_measure_lt
          (show measure after < measure evm from decreases running next)) within) := by
  rw [runFrame]
  simp only [running, dite_true]
  split <;> rename_i heq <;> rw [next] at heq <;> cases heq
  rfl

/-- Every run that succeeds ends with a stopped frame. -/
theorem running_runFrame {evm after : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound}
    (h : runFrame step decreases bound runChild evm within = .ok after) :
    after.running = false := by
  fun_induction runFrame step decreases bound runChild evm within
  all_goals first
    | (cases h; done)
    | (cases h; rfl)
    | (cases h; assumption)
    | (rename_i ih; exact ih h)
    | (cases h; simp_all)

/-- A run keeps the size of memory a multiple of 32 when each of its steps keeps it.

A step that gives a message must give a resume that keeps it too. -/
theorem size_runFrame_mod
    (next : ∀ {evm after : Evm fork Meter}, evm.memory.size % 32 = 0 →
      step evm = .ok (.next after) → after.memory.size % 32 = 0)
    (resumes : ∀ {evm caller child after : Evm fork Meter} {message : Message fork}
      {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}, evm.memory.size % 32 = 0 →
      step evm = .ok (.child caller message resume) → resume child = .ok after →
      after.memory.size % 32 = 0)
    {evm after : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound}
    (hmod : evm.memory.size % 32 = 0)
    (h : runFrame step decreases bound runChild evm within = .ok after) :
    after.memory.size % 32 = 0 := by
  fun_induction runFrame step decreases bound runChild evm within
  all_goals first
    | (cases h; done)
    | (cases h; exact hmod)
    | (rename_i result _ ih; exact ih (next hmod result) h)
    | (rename_i resumed _ ih; exact ih (resumes hmod (by assumption) resumed) h)

end Loop

/-- An exceptional halt leaves no gas. -/
theorem gasHeld_exceptionalHalt [LawfulGasMeter Meter] (evm : Evm fork Meter) (e : EvmError) :
    GasMeter.gasHeld (exceptionalHalt evm e).gas = 0 :=
  LawfulGasMeter.gasHeld_exhaust _

/-- An exceptional halt drops the output and records the error. -/
theorem exceptionalHalt_output (evm : Evm fork Meter) (e : EvmError) :
    (exceptionalHalt evm e).output = .empty ∧ (exceptionalHalt evm e).error = some e :=
  ⟨rfl, rfl⟩

end EthLib.Execution.Evm
