module

public import EthLib.Execution.Evm.Create
public import EthLib.Execution.Evm.SelfDestruct

/-!
# `Evm.Interpreter`

The execution of one frame: a step for each opcode, and a loop of steps until the frame stops.

A step runs the opcode at the program counter.

A position past the end of the code holds STOP.

A byte that is no opcode at the fork halts the frame.

An opcode with no instruction aborts the whole run, since nothing here gives its result.

A step gives the next frame, or a message to run first, for a call or a creation.

Such a step also says how the frame goes on from the frame that ends the message.

The loop runs that message through a parameter, so the recursion of messages is not here.

An exceptional halt consumes all the gas of the frame and drops its output.

REVERT keeps both.

A state that lacks data, such as the code of a code hash, also aborts the whole run.

Each step lowers the measure of the frame, so the loop ends with no bound on its number of steps.

A message gets less gas than its caller had, so the recursion of messages can end too.

The instructions are those of the forks up to BPO5, and Glamsterdam and Hegotá are not specified.

The Yellow Paper, Shanghai version, defines the loop in its section Execution Model.

Its section Message Call says that an exceptional halt leaves no gas.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The instruction of an opcode at fork `fork` that gives the next frame, or none.

The calls and the creations may give a message to run first, so they are not here. -/
def instruction (fork : Fork) (op : Op) :
    Option (Evm fork Meter → Except EvmError (Evm fork Meter)) :=
  stackOnlyStep fork op <|> controlFlowStep op <|> memoryDataStep op <|> returnOpStep fork op <|>
    environmentStep fork op <|> accountStep fork op <|> storageStep op <|>
    transientStorageStep fork op <|> logOpStep op <|> selfdestructOpStep fork op

/-- The step of a frame at fork `fork`: run the opcode at the program counter.

An opcode with no instruction yet fails with an error that aborts the run.

The frame must run. -/
def step (fork : Fork) (evm : Evm fork Meter) : Except EvmError (StepResult fork Meter) :=
  if h : evm.pc < evm.code.size then
    let byte := evm.code[evm.pc]
    match Op.ofByte fork byte with
    | none => throw (.invalidOpcode byte)
    | some op =>
      match instruction fork op with
      | some run => .next <$> run evm
      | none =>
        match messageInstruction fork op with
        | some run => run evm
        | none => throw (.unspecifiedOpcode byte)
  else .next <$> stopStep evm

/-- A choice among two instructions gives one of them. -/
private theorem orElse_eq_some {α : Type} {a b : Option α} {x : α}
    (h : (a <|> b) = some x) : a = some x ∨ b = some x := by
  cases a <;> simp_all [HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- Each instruction lowers the measure of a running frame. -/
theorem instruction_measure_lt [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hrun : instruction fork op = some run) (h : run evm = .ok after)
    (running : evm.running = true) : measure after < measure evm := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact stackOnlyStep_measure_lt hf h running
  rcases orElse_eq_some hrun with hf | hrun
  · exact controlFlowStep_measure_lt hf h running
  rcases orElse_eq_some hrun with hf | hrun
  · exact memoryDataStep_measure_lt hf h running
  rcases orElse_eq_some hrun with hf | hrun
  · exact returnOpStep_measure_lt hf h running
  rcases orElse_eq_some hrun with hf | hrun
  · exact environmentStep_measure_lt hf h running
  rcases orElse_eq_some hrun with hf | hrun
  · exact accountStep_measure_lt hf h running
  rcases orElse_eq_some hrun with hf | hrun
  · exact storageStep_measure_lt hf h running
  rcases orElse_eq_some hrun with hf | hrun
  · exact transientStorageStep_measure_lt hf h running
  rcases orElse_eq_some hrun with hf | hf
  · exact logOpStep_measure_lt hf h running
  · exact selfdestructOpStep_measure_lt hf h running

/-- Each step of a running frame lowers its measure. -/
theorem step_decreases [LawfulGasMeter Meter] (fork : Fork) {evm : Evm fork Meter}
    {result : StepResult fork Meter} (running : evm.running = true)
    (h : step fork evm = .ok result) : result.Decreases evm := by
  unfold step at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · rename_i hop
        cases hr : ‹Evm fork Meter → Except EvmError (Evm fork Meter)› evm with
        | error => simp [hr, Functor.map, Except.map] at h
        | ok after =>
          simp only [hr, Functor.map, Except.map, Except.ok.injEq] at h
          subst h
          exact instruction_measure_lt hop hr running
      · split at h
        · rename_i hcall
          exact messageInstruction_decreases hcall h running
        · cases h
  · simp only [stopStep, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    exact measure_lt_of_stop (Nat.le_refl _) rfl running

/-- A frame whose measure drops has no more gas. -/
theorem gasHeld_le_of_measure_lt {a b : Evm fork Meter} (h : measure b < measure a) :
    GasMeter.gasHeld b.gas ≤ GasMeter.gasHeld a.gas := by
  unfold measure at h
  have := Bool.toNat_le a.running
  omega

/-- A runner of the messages with less gas than `bound`.

From a calling frame, it runs a message and gives the frame that ends it, with at most its gas.

It fails only with an error that aborts the run. -/
abbrev MessageRunner (fork : Fork) (Meter : Type) [GasMeter Meter] (bound : Nat) : Type :=
  (caller : Evm fork Meter) → (message : Message fork) → message.gas < bound →
    Except EvmError { child : Evm fork Meter // GasMeter.gasHeld child.gas ≤ message.gas }

/-- The frame after an exceptional halt: it stops with no gas, no output and the error. -/
def exceptionalHalt (evm : Evm fork Meter) (error : EvmError) : Evm fork Meter :=
  { evm with
    gas := GasMeter.exhaust evm.gas
    running := false
    output := .empty
    error := some error }

/-- Run the frame `evm` until it stops, with the steps of `step`, which lower its measure.

A message gets the gas below `bound`, which is at least the gas of the frame.

A runner of messages runs each message that a step asks for.

A step that fails halts the frame exceptionally, unless its error aborts the whole run. -/
def runFrame (step : Evm fork Meter → Except EvmError (StepResult fork Meter))
    (decreases : ∀ {evm result}, evm.running = true → step evm = .ok result →
      result.Decreases evm)
    (bound : Nat)
    (runChild : MessageRunner fork Meter bound)
    (evm : Evm fork Meter) (within : GasMeter.gasHeld evm.gas ≤ bound) :
    Except EvmError (Evm fork Meter) :=
  if running : evm.running then
    match result : step evm with
    | .error e => if e.aborts then .error e else .ok (exceptionalHalt evm e)
    | .ok (.next after) =>
      have lower : measure after < measure evm := decreases running result
      runFrame step decreases bound runChild after
        (Nat.le_trans (gasHeld_le_of_measure_lt lower) within)
    | .ok (.child caller message resume) =>
      have lower := decreases running result
      match runChild caller message (Nat.lt_of_lt_of_le lower.1 within) with
      | .error e => .error e
      | .ok ⟨child, used⟩ =>
        match resumed : resume child with
        | .error e => if e.aborts then .error e else .ok (exceptionalHalt evm e)
        | .ok after =>
          have lower : measure after < measure evm := lower.2 child after used resumed
          runFrame step decreases bound runChild after
            (Nat.le_trans (gasHeld_le_of_measure_lt lower) within)
  else .ok evm
termination_by measure evm

/-- A run ends with no more gas than the frame it starts from.

The recursion of messages needs this bound, so that a message gives back at most its own gas. -/
theorem gasHeld_runFrame_le [LawfulGasMeter Meter]
    {step : Evm fork Meter → Except EvmError (StepResult fork Meter)}
    {decreases : ∀ {evm result}, evm.running = true → step evm = .ok result →
      result.Decreases evm}
    {bound : Nat}
    {runChild : MessageRunner fork Meter bound}
    {evm after : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound}
    (h : runFrame step decreases bound runChild evm within = .ok after) :
    GasMeter.gasHeld after.gas ≤ GasMeter.gasHeld evm.gas := by
  fun_induction runFrame step decreases bound runChild evm within
  all_goals first
    | (cases h; done)
    | (cases h; simp only [exceptionalHalt, LawfulGasMeter.gasHeld_exhaust]; omega)
    | (cases h; exact Nat.le_refl _)
    | (rename_i lower ih; exact Nat.le_trans (ih h) (gasHeld_le_of_measure_lt lower))

end EthLib.Execution.Evm
