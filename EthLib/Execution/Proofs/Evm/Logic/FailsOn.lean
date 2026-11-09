module

public import EthLib.Execution.Proofs.Evm.Logic.Message

/-!
# Proofs: triples whose runner may fail, on a named set of messages

A triple under an assumption asks the runner of messages to fail only with an error that aborts.

Its run may then end at a frame whose runner fails on any message that the frame sends.

The triples here ask nothing of the errors of the runner.

They name instead the messages on which the runner may fail.

That set is a condition on the frame that sends the message and on the message.

A runner meets an assumption in the weak sense when each frame that it gives meets the assumption.

It may fail on any message, with any error.

Take a runner that meets the assumption in this sense.

Then each frame of the precondition reaches a frame of the postcondition.

Or it reaches a frame that sends a message of the named set, and the runner fails on that message.

The run of such a frame fails with the error of the runner.

A runner that meets the assumption, as a triple under it asks, also meets it in the weak sense.

So each triple here is also a triple under the same assumption.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The frame sends a message of `S`, and the runner fails on it, with any error.

`S` is a condition on the frame that sends the message and on the message. -/
def AbortsOn (S : Evm fork Meter → Message fork → Prop) (bound : Nat)
    (runChild : MessageRunner fork Meter bound) (evm : Evm fork Meter) : Prop :=
  evm.running = true ∧ ∃ caller message resume,
    step fork evm = .ok (.child caller message resume) ∧ S caller message ∧
      ∃ lt e, runChild caller message lt = .error e

/-- Each frame that the runner gives meets the assumption `callee`.

The runner may fail on any message, with any error. -/
def MeetsOk {bound : Nat} (callee : Evm fork Meter → Message fork → Evm fork Meter → Prop)
    (runChild : MessageRunner fork Meter bound) : Prop :=
  ∀ caller message lt child, runChild caller message lt = .ok child →
    callee caller message child.1

/-- Under every runner whose frames meet `callee`, each frame of `P` reaches a frame of `Q`.

Or it reaches a frame that sends a message of `S`, and the runner fails on that message.

That holds for every bound on the gas of messages, at least the gas of the frame. -/
def HoareOn (fork : Fork) (callee : Evm fork Meter → Message fork → Evm fork Meter → Prop)
    (S : Evm fork Meter → Message fork → Prop) (P Q : Evm fork Meter → Prop) : Prop :=
  ∀ bound (runChild : MessageRunner fork Meter bound), MeetsOk callee runChild →
    ∀ evm, P evm → GasMeter.gasHeld evm.gas ≤ bound →
      ∃ after, Reaches (StepBy fork bound runChild) evm after ∧
        (Q after ∨ AbortsOn S bound runChild after)

/-- A triple whose runner may fail on the messages of `S`, to a stopped frame of `Q`. -/
def SpecOn (fork : Fork) (callee : Evm fork Meter → Message fork → Evm fork Meter → Prop)
    (S : Evm fork Meter → Message fork → Prop) (P Q : Evm fork Meter → Prop) : Prop :=
  HoareOn fork callee S P fun evm => evm.running = false ∧ Q evm

variable {callee : Evm fork Meter → Message fork → Evm fork Meter → Prop}
  {S : Evm fork Meter → Message fork → Prop}

/-- A runner that meets an assumption also meets it in the weak sense. -/
theorem Meets.meetsOk {bound : Nat} {runChild : MessageRunner fork Meter bound}
    (h : Meets callee runChild) : MeetsOk callee runChild :=
  h.ok

/-- A frame whose runner fails on a message of `S` is a frame whose runner fails on its message. -/
theorem AbortsOn.abortsBy {bound : Nat} {runChild : MessageRunner fork Meter bound}
    {evm : Evm fork Meter} (h : AbortsOn S bound runChild evm) : AbortsBy fork bound runChild evm :=
  let ⟨running, caller, message, resume, sent, _, lt, e, failed⟩ := h
  ⟨running, caller, message, resume, sent, lt, e, failed⟩

namespace HoareOn

/-- A triple with no message holds for every set of messages. -/
theorem of_hoare {P Q : Evm fork Meter → Prop} (h : Hoare fork P Q) : HoareOn fork callee S P Q :=
  fun _ _ _ evm hp _ =>
    let ⟨after, hreach, hq⟩ := h evm hp
    ⟨after, hreach.mono fun hs => .step hs, .inl hq⟩

/-- A step that sends a message of `S`, to a frame of `Q` from every frame that ends it.

From each frame of `P`, the step asks for a message, and the message is in `S`.

Each frame that ends the message with at most its gas, and that meets the assumption, resumes.

The resume gives a frame of `Q`, or fails with an error that does not abort.

Then the frame halts exceptionally with that error, and the halted frame is in `Q`. -/
theorem of_child [LawfulGasMeter Meter] {P Q : Evm fork Meter → Prop}
    (h : ∀ evm, P evm → evm.running = true ∧ ∃ caller message resume,
      step fork evm = .ok (.child caller message resume) ∧ S caller message ∧
      ∀ child, GasMeter.gasHeld child.gas ≤ message.gas → callee caller message child →
        (∃ after, resume child = .ok after ∧ Q after) ∨
          ∃ e, resume child = .error e ∧ e.aborts = false ∧ Q (exceptionalHalt evm e)) :
    HoareOn fork callee S P Q := by
  intro bound runChild meets evm hp within
  obtain ⟨running, caller, message, resume, sent, hS, hresume⟩ := h evm hp
  have lt : message.gas < bound := by
    have := (step_decreases fork running sent).1
    omega
  cases ran : runChild caller message lt with
  | error e =>
    exact ⟨evm, .refl evm, .inr ⟨running, caller, message, resume, sent, hS, lt, e, ran⟩⟩
  | ok child =>
    rcases hresume child.1 child.2 (meets caller message lt child ran) with
      ⟨after, resumed, hq⟩ | ⟨e, failed, halts, hq⟩
    · exact ⟨after, .single (.child running sent lt ran resumed), .inl hq⟩
    · exact ⟨_, .single (.childHalt running sent lt ran failed halts), .inl hq⟩

/-- Sequence: reach the middle condition, then the postcondition from it. -/
theorem seq [LawfulGasMeter Meter] {P Q R : Evm fork Meter → Prop}
    (first : HoareOn fork callee S P Q) (second : HoareOn fork callee S Q R) :
    HoareOn fork callee S P R := by
  intro bound runChild meets evm hp within
  obtain ⟨mid, hmid, hq | aborted⟩ := first bound runChild meets evm hp within
  · obtain ⟨after, hafter, hr⟩ := second bound runChild meets mid hq
      (Nat.le_trans (hmid.gasHeld_le StepBy.gasHeld_le) within)
    exact ⟨after, hmid.trans hafter, hr⟩
  · exact ⟨mid, hmid, .inr aborted⟩

/-- Consequence: a stronger precondition and a weaker postcondition. -/
theorem consequence {P P' Q Q' : Evm fork Meter → Prop} (h : HoareOn fork callee S P Q)
    (pre : ∀ evm, P' evm → P evm) (post : ∀ evm, Q evm → Q' evm) :
    HoareOn fork callee S P' Q' := fun bound runChild meets evm hp within =>
  let ⟨after, hreach, hq⟩ := h bound runChild meets evm (pre evm hp) within
  ⟨after, hreach, hq.imp_left (post after)⟩

/-- A larger set of messages keeps a triple. -/
theorem mono_S {S' : Evm fork Meter → Message fork → Prop} {P Q : Evm fork Meter → Prop}
    (h : HoareOn fork callee S P Q)
    (larger : ∀ caller message, S caller message → S' caller message) :
    HoareOn fork callee S' P Q := fun bound runChild meets evm hp within =>
  let ⟨after, hreach, hq⟩ := h bound runChild meets evm hp within
  ⟨after, hreach, hq.imp_right fun ⟨running, caller, message, resume, sent, hS, rest⟩ =>
    ⟨running, caller, message, resume, sent, larger caller message hS, rest⟩⟩

/-- Such a triple is a triple under the same assumption.

A runner that meets the assumption fails only with an error that aborts, on any message. -/
theorem toUnder {P Q : Evm fork Meter → Prop} (h : HoareOn fork callee S P Q) :
    HoareUnder fork callee P Q := fun bound runChild meets evm hp within =>
  let ⟨after, hreach, hq⟩ := h bound runChild meets.meetsOk evm hp within
  ⟨after, hreach, hq.imp_right AbortsOn.abortsBy⟩

end HoareOn

namespace SpecOn

/-- A triple to a frame from which the specification holds. -/
theorem seq [LawfulGasMeter Meter] {P Q R : Evm fork Meter → Prop}
    (first : HoareOn fork callee S P Q) (second : SpecOn fork callee S Q R) :
    SpecOn fork callee S P R := HoareOn.seq first second

/-- Consequence for a specification. -/
theorem consequence {P P' Q Q' : Evm fork Meter → Prop} (h : SpecOn fork callee S P Q)
    (pre : ∀ evm, P' evm → P evm) (post : ∀ evm, Q evm → Q' evm) : SpecOn fork callee S P' Q' :=
  HoareOn.consequence h pre fun evm ⟨hs, hq⟩ => ⟨hs, post evm hq⟩

/-- Such a specification is a specification under the same assumption. -/
theorem toUnder {P Q : Evm fork Meter → Prop} (h : SpecOn fork callee S P Q) :
    SpecUnder fork callee P Q := HoareOn.toUnder h

/-- From a frame of the precondition, the loop gives a stopped frame of the postcondition.

Or it fails.

It holds for every runner whose frames meet the assumption.

The bound on the gas of messages is any bound that holds the gas of the frame.

The loop fails only when a frame that it reaches sends a message of `S`.

The runner then fails on that message, and the loop fails with the same error. -/
theorem runFrame [LawfulGasMeter Meter] {bound : Nat} {runChild : MessageRunner fork Meter bound}
    {P Q : Evm fork Meter → Prop} (h : SpecOn fork callee S P Q) (meets : MeetsOk callee runChild)
    {evm : Evm fork Meter} (hp : P evm) (within : GasMeter.gasHeld evm.gas ≤ bound) :
    (∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ Q stopped) ∨
    ∃ caller message lt e, S caller message ∧ runChild caller message lt = .error e ∧
      runFrame (step fork) (step_decreases fork) bound runChild evm within = .error e := by
  obtain ⟨after, hreach, ⟨halted, hq⟩ | aborted⟩ := h bound runChild meets evm hp within
  · rw [runFrame_eq_of_reaches StepBy.gasHeld_le StepBy.runFrame_eq hreach within,
      runFrame_of_running_eq_false halted]
    exact .inl ⟨after, rfl, hq⟩
  · obtain ⟨running, caller, message, resume, sent, hS, lt, e, failed⟩ := aborted
    rw [runFrame_eq_of_reaches StepBy.gasHeld_le StepBy.runFrame_eq hreach within]
    exact .inr ⟨caller, message, lt, e, hS, failed,
      runFrame_of_runChild_eq_error running sent lt failed⟩

end SpecOn

end EthLib.Execution.Evm.Logic
