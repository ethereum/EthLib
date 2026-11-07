module

public import EthLib.Execution.Proofs.Evm.Interpreter

/-!
# Proofs: the frames that a frame reaches without a message

A program logic over EVM bytecode reasons about the frames that one frame goes through.

The frames that a frame reaches are those of a chain of steps, for any relation of steps.

The facts about such chains hold for every relation, so the steps with messages share them.

A step of the frame runs the opcode at the program counter, with the step of the interpreter.

It gives the next frame, or a failure that halts the frame exceptionally, as the loop does.

A step that asks for a message, a call or a creation, has no rule here.

So the relation covers frames that send no message, and says nothing past a call.

The frames that send messages have their own relation, under a runner of messages.

The loop of the interpreter follows the steps of any relation that it runs alike at both ends.

So a frame that reaches a stopped frame by steps without a message is the result of the loop.

That holds whatever its runner of messages and its bound on their gas.

The bound only limits the gas of a message, and no step here sends one.

The loop also stops by the measure of the frame, not by a count of steps.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork)

variable {fork : Fork} {Meter : Type}

/-- The frames that a frame reaches by the steps of a relation, itself included. -/
inductive Reaches (S : Evm fork Meter → Evm fork Meter → Prop) :
    Evm fork Meter → Evm fork Meter → Prop where
  /-- A frame reaches itself. -/
  | refl (evm : Evm fork Meter) : Reaches S evm evm
  /-- A step, then the frames that its result reaches. -/
  | step {a b c : Evm fork Meter} : S a b → Reaches S b c → Reaches S a c

namespace Reaches

variable {S S' : Evm fork Meter → Evm fork Meter → Prop}

/-- A single step reaches its result. -/
theorem single {a b : Evm fork Meter} (h : S a b) : Reaches S a b :=
  .step h (.refl b)

/-- The frames reached from a reached frame are reached. -/
theorem trans {a b c : Evm fork Meter} (hab : Reaches S a b) (hbc : Reaches S b c) :
    Reaches S a c := by
  induction hab with
  | refl => exact hbc
  | step h _ ih => exact .step h (ih hbc)

/-- A frame reached by the steps of a relation is reached by the steps of a larger one. -/
theorem mono (larger : ∀ {a b}, S a b → S' a b) {a b : Evm fork Meter} (h : Reaches S a b) :
    Reaches S' a b := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (larger hs) ih

/-- A predicate that every step keeps holds at every reached frame. -/
theorem invariant {R : Evm fork Meter → Prop} (keeps : ∀ {a b}, S a b → R a → R b)
    {a b : Evm fork Meter} (h : Reaches S a b) (start : R a) : R b := by
  induction h with
  | refl => exact start
  | step hs _ ih => exact ih (keeps hs start)

/-- A stopped frame reaches only itself, when only a running frame takes a step. -/
theorem eq_of_stopped (running : ∀ {a b}, S a b → a.running = true) {a b : Evm fork Meter}
    (h : Reaches S a b) (stopped : a.running = false) : b = a := by
  cases h with
  | refl => rfl
  | step hs _ => rw [running hs] at stopped; cases stopped

/-- Two stopped frames that one frame reaches are one frame, when the steps are deterministic.

Only a running frame may take a step. -/
theorem stopped_unique (running : ∀ {a b}, S a b → a.running = true)
    (deterministic : ∀ {a b c}, S a b → S a c → b = c) {a b c : Evm fork Meter}
    (hb : Reaches S a b) (hc : Reaches S a c) (sb : b.running = false)
    (sc : c.running = false) : b = c := by
  induction hb generalizing c with
  | refl => exact (hc.eq_of_stopped running sb).symm
  | step hs _ ih =>
    cases hc with
    | refl => rw [running hs] at sc; cases sc
    | step hs' hc' =>
      rw [deterministic hs hs'] at *
      exact ih hc' sb sc

end Reaches

variable [GasMeter Meter]

/-- One step of a running frame that sends no message.

It gives the next frame, or halts the frame on an error that does not abort the run. -/
inductive Step (fork : Fork) : Evm fork Meter → Evm fork Meter → Prop where
  /-- The step gives the next frame. -/
  | next {evm after : Evm fork Meter} : evm.running = true →
      step fork evm = .ok (.next after) → Step fork evm after
  /-- The step fails with an error that does not abort, so the frame halts exceptionally. -/
  | halt {evm : Evm fork Meter} {e : EvmError} : evm.running = true →
      step fork evm = .error e → e.aborts = false → Step fork evm (exceptionalHalt evm e)

/-- A reached frame holds at most the gas of the frame it starts from, when each step does. -/
theorem Reaches.gasHeld_le {S : Evm fork Meter → Evm fork Meter → Prop}
    (le : ∀ {a b}, S a b → GasMeter.gasHeld b.gas ≤ GasMeter.gasHeld a.gas)
    {a b : Evm fork Meter} (h : Reaches S a b) :
    GasMeter.gasHeld b.gas ≤ GasMeter.gasHeld a.gas :=
  h.invariant (R := fun c => GasMeter.gasHeld c.gas ≤ GasMeter.gasHeld a.gas)
    (fun hs hle => Nat.le_trans (le hs) hle) (Nat.le_refl _)

/-- A stopped frame takes no step. -/
theorem Step.running {a b : Evm fork Meter} (h : Step fork a b) : a.running = true := by
  cases h <;> assumption

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

/-- A step holds at most the gas of the frame it starts from. -/
theorem Step.gasHeld_le [LawfulGasMeter Meter] {a b : Evm fork Meter} (h : Step fork a b) :
    GasMeter.gasHeld b.gas ≤ GasMeter.gasHeld a.gas := by
  cases h with
  | next running next =>
    exact gasHeld_le_of_measure_lt (show measure _ < measure _ from
      step_decreases fork running next)
  | halt => rw [gasHeld_exceptionalHalt]; omega

/-! ## The loop of the interpreter -/

section Loop

variable [LawfulGasMeter Meter] {bound : Nat} {runChild : MessageRunner fork Meter bound}

/-- The loop runs a frame as it runs each frame that the frame reaches.

Each step must hold at most the gas of its frame, and the loop must run its two frames alike. -/
theorem runFrame_eq_of_reaches {S : Evm fork Meter → Evm fork Meter → Prop}
    (le : ∀ {a b}, S a b → GasMeter.gasHeld b.gas ≤ GasMeter.gasHeld a.gas)
    (same : ∀ {a b} (h : S a b) (within : GasMeter.gasHeld a.gas ≤ bound),
      runFrame (step fork) (step_decreases fork) bound runChild a within =
        runFrame (step fork) (step_decreases fork) bound runChild b
          (Nat.le_trans (le h) within))
    {evm mid : Evm fork Meter} (h : Reaches S evm mid)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    runFrame (step fork) (step_decreases fork) bound runChild evm within =
      runFrame (step fork) (step_decreases fork) bound runChild mid
        (Nat.le_trans (h.gasHeld_le le) within) := by
  induction h with
  | refl => rfl
  | step hs _ ih => exact (same hs within).trans (ih _)

/-- The loop runs a frame as it runs the frame that its step without a message gives.

That holds for every bound on the gas of messages and every runner of messages. -/
theorem Step.runFrame_eq {a b : Evm fork Meter} (h : Step fork a b)
    (within : GasMeter.gasHeld a.gas ≤ bound) :
    runFrame (step fork) (step_decreases fork) bound runChild a within =
      runFrame (step fork) (step_decreases fork) bound runChild b
        (Nat.le_trans h.gasHeld_le within) := by
  cases h with
  | next running next => exact runFrame_of_step_eq_next running next
  | halt running failed halts =>
    rw [runFrame_of_step_eq_error running failed halts, runFrame_of_running_eq_false rfl]

/-- A frame that reaches a stopped frame runs to it in the loop of the interpreter.

It holds for every bound on the gas of messages and every runner of messages.

No step of the reach sends a message. -/
theorem runFrame_of_reaches {evm stopped : Evm fork Meter} (h : Reaches (Step fork) evm stopped)
    (halted : stopped.running = false) (within : GasMeter.gasHeld evm.gas ≤ bound) :
    runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok stopped :=
  (runFrame_eq_of_reaches Step.gasHeld_le Step.runFrame_eq h within).trans
    (runFrame_of_running_eq_false halted)

end Loop

end EthLib.Execution.Evm.Logic
