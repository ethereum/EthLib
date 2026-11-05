module

public import EthLib.Execution.Evm.Interpreter

/-!
# Proofs: `Evm.Interpreter`

A step past the end of the code stops the frame, as STOP does.

A step on a byte that is no opcode at the fork fails with that byte.

The loop leaves a stopped frame as it is.

A step on a call or a creation runs it.

A step on an opcode with no instruction yet fails with an error that aborts the run.

A step that fails halts the frame with no gas and no output, unless its error aborts the run.

Then the whole run fails with that error.

A step that succeeds lets the loop go on from the next frame.

Every run that succeeds ends with a stopped frame.
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

section Loop

variable {step : Evm fork Meter → Except EvmError (StepResult fork Meter)}
  {decreases : ∀ {evm result}, evm.running = true → step evm = .ok result →
    result.Decreases evm}
  {bound : Nat}
  {runChild : MessageRunner fork Meter bound}

/-- The loop leaves a stopped frame as it is. -/
theorem runFrame_of_running_eq_false {evm : Evm fork Meter}
    {within : GasMeter.gasLeft evm.gas ≤ bound} (stopped : evm.running = false) :
    runFrame step decreases bound runChild evm within = .ok evm := by
  rw [runFrame]
  simp [stopped]

/-- A step that fails with an error that aborts makes the whole run fail with that error. -/
theorem runFrame_of_step_eq_abort {evm : Evm fork Meter}
    {within : GasMeter.gasLeft evm.gas ≤ bound} {e : EvmError}
    (running : evm.running = true) (failed : step evm = .error e) (aborts : e.aborts = true) :
    runFrame step decreases bound runChild evm within = .error e := by
  rw [runFrame]
  simp only [running, dite_true]
  split <;> simp_all

/-- A step that fails with any other error halts the frame exceptionally. -/
theorem runFrame_of_step_eq_error {evm : Evm fork Meter}
    {within : GasMeter.gasLeft evm.gas ≤ bound} {e : EvmError} (running : evm.running = true)
    (failed : step evm = .error e) (halts : e.aborts = false) :
    runFrame step decreases bound runChild evm within = .ok (exceptionalHalt evm e) := by
  rw [runFrame]
  simp only [running, dite_true]
  split <;> simp_all

/-- A step that gives the next frame lets the loop go on from it. -/
theorem runFrame_of_step_eq_next {evm after : Evm fork Meter}
    {within : GasMeter.gasLeft evm.gas ≤ bound} (running : evm.running = true)
    (next : step evm = .ok (.next after)) :
    runFrame step decreases bound runChild evm within =
      runFrame step decreases bound runChild after
        (Nat.le_trans (gasLeft_le_of_measure_lt
          (show measure after < measure evm from decreases running next)) within) := by
  rw [runFrame]
  simp only [running, dite_true]
  split <;> rename_i heq <;> rw [next] at heq <;> cases heq
  rfl

/-- Every run that succeeds ends with a stopped frame. -/
theorem running_runFrame {evm after : Evm fork Meter} {within : GasMeter.gasLeft evm.gas ≤ bound}
    (h : runFrame step decreases bound runChild evm within = .ok after) :
    after.running = false := by
  fun_induction runFrame step decreases bound runChild evm within
  all_goals first
    | (cases h; done)
    | (cases h; rfl)
    | (cases h; assumption)
    | (rename_i ih; exact ih h)
    | (cases h; simp_all)

end Loop

/-- An exceptional halt leaves no gas. -/
theorem gasLeft_exceptionalHalt [LawfulGasMeter Meter] (evm : Evm fork Meter) (e : EvmError) :
    GasMeter.gasLeft (exceptionalHalt evm e).gas = 0 :=
  LawfulGasMeter.gasLeft_exhaust _

/-- An exceptional halt drops the output and records the error. -/
theorem exceptionalHalt_output (evm : Evm fork Meter) (e : EvmError) :
    (exceptionalHalt evm e).output = .empty ∧ (exceptionalHalt evm e).error = some e :=
  ⟨rfl, rfl⟩

end EthLib.Execution.Evm
