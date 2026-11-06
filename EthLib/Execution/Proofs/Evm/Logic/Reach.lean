module

public import EthLib.Execution.Proofs.Evm.Interpreter

/-!
# Proofs: the frames that a frame reaches without a message

A program logic over EVM bytecode reasons about the frames that one frame goes through.

A step of the frame runs the opcode at the program counter, with `step` of the interpreter.

It gives the next frame, or a failure that halts the frame exceptionally, as the loop does.

A step that asks for a message, a call or a creation, has no rule here.

So the relation covers frames that send no message, and says nothing past a call.

External calls and reentrancy are out of the scope of this logic.

`runFrame`, the loop of the interpreter, follows these steps.

So a frame that reaches a stopped frame is the result of `runFrame`.

That holds whatever its runner of messages and its bound on their gas.

The bound only limits the gas of a message, and no step here sends one.

The loop also stops by the measure of the frame, not by a count of steps.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- One step of a running frame that sends no message.

It gives the next frame, or halts the frame on an error that does not abort the run. -/
inductive Step (fork : Fork) : Evm fork Meter → Evm fork Meter → Prop where
  /-- The step gives the next frame. -/
  | next {evm after : Evm fork Meter} : evm.running = true →
      step fork evm = .ok (.next after) → Step fork evm after
  /-- The step fails with an error that does not abort, so the frame halts exceptionally. -/
  | halt {evm : Evm fork Meter} {e : EvmError} : evm.running = true →
      step fork evm = .error e → e.aborts = false → Step fork evm (exceptionalHalt evm e)

/-- The frames that a frame reaches by steps that send no message, itself included. -/
inductive Reaches (fork : Fork) : Evm fork Meter → Evm fork Meter → Prop where
  /-- A frame reaches itself. -/
  | refl (evm : Evm fork Meter) : Reaches fork evm evm
  /-- A step, then the frames that its result reaches. -/
  | step {a b c : Evm fork Meter} : Step fork a b → Reaches fork b c → Reaches fork a c

namespace Reaches

/-- A single step reaches its result. -/
theorem single {a b : Evm fork Meter} (h : Step fork a b) : Reaches fork a b :=
  .step h (.refl b)

/-- The frames reached from a reached frame are reached. -/
theorem trans {a b c : Evm fork Meter} (hab : Reaches fork a b) (hbc : Reaches fork b c) :
    Reaches fork a c := by
  induction hab with
  | refl => exact hbc
  | step h _ ih => exact .step h (ih hbc)

/-- A predicate that every step keeps holds at every reached frame. -/
theorem invariant {R : Evm fork Meter → Prop} (keeps : ∀ {a b}, Step fork a b → R a → R b)
    {a b : Evm fork Meter} (h : Reaches fork a b) (start : R a) : R b := by
  induction h with
  | refl => exact start
  | step hs _ ih => exact ih (keeps hs start)

end Reaches

/-- A stopped frame takes no step. -/
theorem Step.running {a b : Evm fork Meter} (h : Step fork a b) : a.running = true := by
  cases h <;> assumption

/-- A stopped frame reaches only itself. -/
theorem Reaches.eq_of_stopped {a b : Evm fork Meter} (h : Reaches fork a b)
    (stopped : a.running = false) : b = a := by
  cases h with
  | refl => rfl
  | step hs _ => rw [hs.running] at stopped; cases stopped

/-- A step gives one frame: the relation follows the function `step`. -/
theorem Step.deterministic {a b c : Evm fork Meter} (hb : Step fork a b) (hc : Step fork a c) :
    b = c := by
  cases hb with
  | next _ hb => cases hc with
    | next _ hc => rw [hb] at hc; cases hc; rfl
    | halt _ hc _ => rw [hb] at hc; cases hc
  | halt _ hb _ => cases hc with
    | next _ hc => rw [hb] at hc; cases hc
    | halt _ hc _ => rw [hb] at hc; cases hc; rfl

/-- Two stopped frames that one frame reaches are one frame. -/
theorem Reaches.stopped_unique {a b c : Evm fork Meter} (hb : Reaches fork a b)
    (hc : Reaches fork a c) (sb : b.running = false) (sc : c.running = false) : b = c := by
  induction hb generalizing c with
  | refl => exact (hc.eq_of_stopped sb).symm
  | step hs _ ih =>
    cases hc with
    | refl => rw [hs.running] at sc; cases sc
    | step hs' hc' =>
      rw [Step.deterministic hs hs'] at *
      exact ih hc' sb sc

/-! ## The loop of the interpreter -/

/-- A frame that reaches a stopped frame runs to it in the loop of the interpreter.

It holds for every bound on the gas of messages and every runner of messages.

No step of the reach sends a message. -/
theorem runFrame_of_reaches [LawfulGasMeter Meter] {bound : Nat}
    {runChild : MessageRunner fork Meter bound} {evm stopped : Evm fork Meter}
    (h : Reaches fork evm stopped) (halted : stopped.running = false)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok stopped := by
  induction h with
  | refl => exact runFrame_of_running_eq_false halted
  | step hs _ ih =>
    cases hs with
    | next running next =>
      rw [runFrame_of_step_eq_next running next]
      exact ih halted _
    | halt running failed halts =>
      rename_i rest
      rw [runFrame_of_step_eq_error running failed halts]
      -- The halted frame is stopped, so the rest of the reach is that frame itself.
      exact congrArg Except.ok (rest.eq_of_stopped rfl).symm

end EthLib.Execution.Evm.Logic
