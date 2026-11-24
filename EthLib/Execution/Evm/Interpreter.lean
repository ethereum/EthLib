module

public import EthLib.Execution.Evm.Call.Create
public import EthLib.Execution.Evm.Instructions.SelfDestruct

/-!
# `Evm.Interpreter`

The execution of one frame: a step for each opcode, and a loop of steps until the frame stops.

The Yellow Paper, Shanghai version, defines the loop in its section Execution Model.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The instruction of an opcode at fork `fork` that gives the next frame, or none.

The calls and the creations may give a message to run first, so they are not here.

The instructions are those of the forks up to Glamsterdam, and Hegotá is not specified. -/
def instruction (fork : Fork) (op : Op) :
    Option (Evm fork Meter → Except EvmError (Evm fork Meter)) :=
  stackOnlyStep fork op <|> controlFlowStep op <|> memoryDataStep op <|> returnOpStep fork op <|>
    environmentStep fork op <|> accountStep fork op <|> storageStep op <|>
    transientStorageStep fork op <|> logOpStep op <|> selfdestructOpStep fork op

/-- The step of a frame at fork `fork`: run the opcode at the program counter.

An opcode with no instruction yet fails with an error that aborts the run.

The frame must run. -/
def step (fork : Fork) (evm : Evm fork Meter) : Except EvmError (StepResult fork Meter) :=
  -- Yellow Paper §9.4.1: `w = I_b[mu_{pc}]` if `mu_{pc} < ||I_b||`.
  if h : evm.pc < evm.code.size then
    let byte := evm.code[evm.pc]
    match Op.ofByte fork byte with
    -- §9.4.2: `delta_w = ∅` for a byte that is no instruction at the fork, so `Z` holds.
    | none => throw (.invalidOpcode byte)
    | some op =>
      -- Yellow Paper §9.5: `O` applies the instruction `w`, as Appendix H defines it.
      match instruction fork op with
      | some run => .next <$> run evm
      | none =>
        -- A call or a creation runs a message first, so its step gives that message.
        --
        -- Such a step also says how the frame goes on from the frame that ends the message.
        match messageInstruction fork op with
        | some run => run evm
        -- An opcode with no instruction yet aborts the whole run.
        --
        -- Nothing here gives its result, and the source has no such case.
        | none => throw (.unspecifiedOpcode byte)
  -- `w = STOP` otherwise.
  else .next <$> stopStep evm

/-- A choice among two instructions gives one of them. -/
theorem orElse_eq_some {α : Type} {a b : Option α} {x : α}
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

/-- An exceptional halt leaves no gas, as the section Message Call of the Yellow Paper says. -/
theorem gasHeld_exceptionalHalt [LawfulGasMeter Meter] (evm : Evm fork Meter) (e : EvmError) :
    GasMeter.gasHeld (exceptionalHalt evm e).gas = 0 :=
  LawfulGasMeter.gasHeld_exhaust _

/-- A runner of the messages with less gas than `bound`, in the monad `M`.

From a calling frame, it runs a message and gives the frame that ends it, with at most its gas.

By convention, it fails only with an error that aborts the run.

The type does not enforce this; the proofs assume it of the runners they reason about. -/
abbrev MessageRunnerIn (M : Type → Type) (fork : Fork) (Meter : Type) [GasMeter Meter]
    (bound : Nat) : Type :=
  (caller : Evm fork Meter) → (message : Message fork) → message.gas < bound →
    M { child : Evm fork Meter // GasMeter.gasHeld child.gas ≤ message.gas }

/-- A runner of the messages with less gas than `bound`, in the monad of errors. -/
abbrev MessageRunner (fork : Fork) (Meter : Type) [GasMeter Meter] (bound : Nat) : Type :=
  MessageRunnerIn (Except EvmError) fork Meter bound

/-- An observer of the steps in the monad `M`: it sees each frame that runs, and its step.

It gives nothing back to the run.

An observer that fails stops the run. -/
abbrev StepObserver (M : Type → Type) (fork : Fork) (Meter : Type) : Type :=
  Evm fork Meter → Except EvmError (StepResult fork Meter) → M Unit

/-- Run the frame `evm` until it stops, in the monad `M`, with the steps of `step`.

Each step lowers the measure of the frame.

The observer sees each step, before the loop acts on it.

A message gets the gas below `bound`, which is at least the gas of the frame.

The frame that ends the run has at most the gas `bound`. -/
@[specialize]
def runFrameWith [LawfulGasMeter Meter] {M : Type → Type} [Monad M] [MonadExceptOf EvmError M]
    (observe : StepObserver M fork Meter)
    (step : Evm fork Meter → Except EvmError (StepResult fork Meter))
    (decreases : ∀ {evm result}, evm.running = true → step evm = .ok result →
      result.Decreases evm)
    (bound : Nat)
    (runChild : MessageRunnerIn M fork Meter bound)
    (evm : Evm fork Meter) (within : GasMeter.gasHeld evm.gas ≤ bound) :
    M { after : Evm fork Meter // GasMeter.gasHeld after.gas ≤ bound } :=
  -- Yellow Paper §9.4: `X` cycles until `Z` holds or `H` gives an output.
  if running : evm.running then
    match result : step evm with
    -- `Z` holds, or a check that a later EIP adds fails: no output, and §8 gives `g' = 0`.
    --
    -- A step that fails halts the frame exceptionally.
    --
    -- An exceptional halt consumes all the gas of the frame and drops its output.
    | .error e => do
      observe evm (.error e)
      -- An error that aborts the whole run is no halt of the frame.
      --
      -- The source has no such case.
      --
      -- An opcode with no instruction aborts the run.
      --
      -- So does a state that lacks data, such as the code of a code hash.
      --
      -- So does a number from the environment that no word holds, which an instruction would push.
      if e.aborts then throw e
      else pure ⟨exceptionalHalt evm e, by rw [gasHeld_exceptionalHalt]; exact Nat.zero_le _⟩
    -- `X(O(sigma, mu, A, I))`: the next cycle, from the frame after the step.
    | .ok (.next after) => do
      observe evm (.ok (.next after))
      -- Each step lowers the measure of the frame.
      have lower : measure after < measure evm := decreases running result
      runFrameWith observe step decreases bound runChild after
        (Nat.le_trans (gasHeld_le_of_measure_lt lower) within)
    -- A call or a creation: the message runs, then the step goes on from its result.
    | .ok (.child caller message resume) => do
      observe evm (.ok (.child caller message resume))
      have lower := decreases running result
      -- The runner of messages, a parameter, runs the message that the step asks for.
      --
      -- So the recursion of messages is not here.
      --
      -- A message gets less gas than its caller had, so the recursion of messages can end too.
      let ⟨child, used⟩ ← runChild caller message (Nat.lt_of_lt_of_le lower.1 within)
      match resumed : resume child with
      -- The rest of the step can still halt the frame, or abort the run, as above.
      | .error e =>
        if e.aborts then throw e
        else pure ⟨exceptionalHalt evm e, by rw [gasHeld_exceptionalHalt]; exact Nat.zero_le _⟩
      | .ok after =>
        have lower : measure after < measure evm := lower.2 child after used resumed
        runFrameWith observe step decreases bound runChild after
          (Nat.le_trans (gasHeld_le_of_measure_lt lower) within)
  -- `H(mu, I) ≠ ∅`: the frame halted, normally or by REVERT, and is the result.
  --
  -- REVERT keeps both the gas left and the output.
  else pure ⟨evm, within⟩
-- Each step lowers the measure, so the loop ends with no bound on its number of steps.
termination_by measure evm

/-- Run the frame `evm` until it stops, with the steps of `step`, which lower its measure.

It is the loop with no observer, in the monad of errors.

A message gets the gas below `bound`, which is at least the gas of the frame.

A runner of messages runs each message that a step asks for.

A step that fails halts the frame exceptionally, unless its error aborts the whole run. -/
def runFrame [LawfulGasMeter Meter]
    (step : Evm fork Meter → Except EvmError (StepResult fork Meter))
    (decreases : ∀ {evm result}, evm.running = true → step evm = .ok result →
      result.Decreases evm)
    (bound : Nat)
    (runChild : MessageRunner fork Meter bound)
    (evm : Evm fork Meter) (within : GasMeter.gasHeld evm.gas ≤ bound) :
    Except EvmError (Evm fork Meter) :=
  Subtype.val <$> runFrameWith (fun _ _ => pure ()) step decreases bound runChild evm within

end EthLib.Execution.Evm
