module

public import EthLib.Execution.Proofs.Evm.Logic.Loop
public import EthLib.Execution.Proofs.Evm.Call.MessageCall

/-!
# Proofs: the frames that a frame reaches through its messages

A step of a frame can ask for a message, a call or a creation, before the frame goes on.

The loop of the interpreter hands each such message to a runner of messages.

The runner ends the message with a frame, and the frame of the caller goes on from it.

The runner can also fail, and then the whole run fails with its error.

So the frames that a frame reaches depend on that runner, and on its bound on the gas of messages.

A step under a runner is a step that sends no message, or a message that the runner ends.

The steps under one runner are deterministic, as the loop is.

A frame that reaches a stopped frame under a runner is the result of the loop with that runner.

The code that a message runs is arbitrary, and a triple does not reason about it.

It takes an assumption instead, on each frame that ends a message.

A runner meets the assumption when each frame that it gives meets the assumption.

The runner must also fail only with an error that aborts the run.

The runner of the messages of a frame of a message meets the assumption that always holds.

That runner can fail, but only with an error that aborts, such as an error of the state.

A triple under an assumption holds for every runner that meets it, and for every bound.

From each frame of its precondition, the frame reaches a frame of its postcondition.

Or it reaches a frame whose runner fails on its message, and then the run aborts.

The message may change the state, and may even call the caller again.

So a triple says about the state after a message only what the assumption says.

With the assumption that always holds, a triple says nothing of the frame that ends a message.

This file has no rule for an opcode that sends a message, only the rule for a step that sends one.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## Steps under a runner of messages -/

/-- One step of a running frame under a runner of messages.

The step sends no message, or the runner runs its message, and the frame goes on or halts. -/
inductive StepBy (fork : Fork) (bound : Nat) (runChild : MessageRunner fork Meter bound) :
    Evm fork Meter → Evm fork Meter → Prop where
  /-- A step that sends no message. -/
  | step {evm after : Evm fork Meter} : Step fork evm after → StepBy fork bound runChild evm after
  /-- The runner ends the message with `child`, and the frame goes on from the resumed frame. -/
  | child {evm caller after : Evm fork Meter} {message : Message fork}
      {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
      {child : { child : Evm fork Meter // GasMeter.gasHeld child.gas ≤ message.gas }} :
      evm.running = true → step fork evm = .ok (.child caller message resume) →
      ∀ lt : message.gas < bound, runChild caller message lt = .ok child →
      resume child.1 = .ok after → StepBy fork bound runChild evm after
  /-- The runner ends the message, and the resume fails with an error that does not abort. -/
  | childHalt {evm caller : Evm fork Meter} {message : Message fork}
      {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
      {child : { child : Evm fork Meter // GasMeter.gasHeld child.gas ≤ message.gas }}
      {e : EvmError} :
      evm.running = true → step fork evm = .ok (.child caller message resume) →
      ∀ lt : message.gas < bound, runChild caller message lt = .ok child →
      resume child.1 = .error e → e.aborts = false →
      StepBy fork bound runChild evm (exceptionalHalt evm e)

variable {bound : Nat} {runChild : MessageRunner fork Meter bound}

/-- A stopped frame takes no step. -/
theorem StepBy.running {a b : Evm fork Meter} (h : StepBy fork bound runChild a b) :
    a.running = true := by
  cases h with
  | step hs => exact hs.running
  | child running => exact running
  | childHalt running => exact running

/-- A step under a runner holds at most the gas of the frame it starts from. -/
theorem StepBy.gasHeld_le [LawfulGasMeter Meter] {a b : Evm fork Meter}
    (h : StepBy fork bound runChild a b) : GasMeter.gasHeld b.gas ≤ GasMeter.gasHeld a.gas := by
  cases h with
  | step hs => exact hs.gasHeld_le
  | child running sent lt ran resumed =>
    rename_i child
    exact gasHeld_le_of_measure_lt
      ((step_decreases fork running sent).2 child.1 _ child.2 resumed)
  | childHalt => rw [gasHeld_exceptionalHalt]; omega

/-- A step that sends no message is not a step that sends one. -/
theorem Step.not_child {a b caller : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)} (h : Step fork a b)
    (sent : step fork a = .ok (.child caller message resume)) : False := by
  cases h with
  | next _ h => rw [sent] at h; cases h
  | halt _ h _ => rw [sent] at h; cases h

/-- A step under a runner gives one frame. -/
theorem StepBy.deterministic {a b c : Evm fork Meter} (hb : StepBy fork bound runChild a b)
    (hc : StepBy fork bound runChild a c) : b = c := by
  cases hb with
  | step hb =>
    cases hc with
    | step hc => exact hb.deterministic hc
    | child _ sent => exact (hb.not_child sent).elim
    | childHalt _ sent => exact (hb.not_child sent).elim
  | child _ sent lt ran resumed =>
    cases hc with
    | step hc => exact (hc.not_child sent).elim
    | child _ sent' lt' ran' resumed' =>
      rw [sent] at sent'
      cases sent'
      rw [ran] at ran'
      cases ran'
      rw [resumed] at resumed'
      cases resumed'
      rfl
    | childHalt _ sent' lt' ran' failed =>
      rw [sent] at sent'
      cases sent'
      rw [ran] at ran'
      cases ran'
      rw [resumed] at failed
      cases failed
  | childHalt _ sent lt ran failed =>
    cases hc with
    | step hc => exact (hc.not_child sent).elim
    | child _ sent' lt' ran' resumed =>
      rw [sent] at sent'
      cases sent'
      rw [ran] at ran'
      cases ran'
      rw [resumed] at failed
      cases failed
    | childHalt _ sent' lt' ran' failed' =>
      rw [sent] at sent'
      cases sent'
      rw [ran] at ran'
      cases ran'
      rw [failed] at failed'
      cases failed'
      rfl

/-- The frame sends a message, and the runner fails to run it. -/
def AbortsBy (fork : Fork) (bound : Nat) (runChild : MessageRunner fork Meter bound)
    (evm : Evm fork Meter) : Prop :=
  evm.running = true ∧ ∃ caller message resume,
    step fork evm = .ok (.child caller message resume) ∧
      ∃ lt e, runChild caller message lt = .error e

/-! ## The loop of the interpreter -/

/-- The loop runs a frame as it runs the frame that its step under the runner gives. -/
theorem StepBy.runFrame_eq [LawfulGasMeter Meter] {a b : Evm fork Meter}
    (h : StepBy fork bound runChild a b) (within : GasMeter.gasHeld a.gas ≤ bound) :
    runFrame (Evm.step fork) (step_decreases fork) bound runChild a within =
      runFrame (Evm.step fork) (step_decreases fork) bound runChild b
        (Nat.le_trans h.gasHeld_le within) := by
  cases h with
  | step hs => exact hs.runFrame_eq within
  | child running sent lt ran resumed => exact runFrame_of_step_eq_child running sent lt ran resumed
  | childHalt running sent lt ran failed halts =>
    rw [runFrame_of_step_eq_child_error running sent lt ran failed halts,
      runFrame_of_running_eq_false rfl]

/-- A frame whose runner fails on its message makes the loop fail with the error of the runner.

The error aborts the run when the runner fails only with such errors. -/
theorem runFrame_of_abortsBy [LawfulGasMeter Meter]
    (aborts : ∀ caller message lt e, runChild caller message lt = .error e → e.aborts = true)
    {evm : Evm fork Meter} (h : AbortsBy fork bound runChild evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ e, runFrame (step fork) (step_decreases fork) bound runChild evm within = .error e ∧
      e.aborts = true := by
  obtain ⟨running, caller, message, resume, sent, lt, e, failed⟩ := h
  exact ⟨e, runFrame_of_runChild_eq_error running sent lt failed,
    aborts caller message lt e failed⟩

/-! ## Triples under an assumption on the frames that end messages -/

/-- The runner meets an assumption on the frames that end its messages.

Each frame that it gives meets the assumption, and it fails only with an error that aborts. -/
structure Meets (callee : Evm fork Meter → Message fork → Evm fork Meter → Prop)
    (runChild : MessageRunner fork Meter bound) : Prop where
  /-- The frame that ends a message, from a caller, meets the assumption. -/
  ok : ∀ caller message lt child, runChild caller message lt = .ok child →
    callee caller message child.1
  /-- The runner fails only with an error that aborts the run. -/
  aborts : ∀ caller message lt e, runChild caller message lt = .error e → e.aborts = true

/-- The runner of the messages of a frame of a message meets the assumption that always holds.

It runs a call or a creation, as the code of a message runs them, for every bound on their gas. -/
theorem meets_process [LawfulGasMeter Meter] (fork : Fork) (bound : Nat) :
    Meets (bound := bound) (fun _ _ _ => True) fun (caller : Evm fork Meter) message _ =>
      match message.target with
      | some _ => processMessage fork message caller.state caller.substate.child
      | none => processCreateMessage fork message caller.state caller.substate.child := by
  refine ⟨fun _ _ _ _ _ => trivial, fun caller message _ e h => ?_⟩
  split at h
  · exact (aborts_of_process_eq_error message.gas message rfl).1 _ _ _ _ _ h
  · exact (aborts_of_process_eq_error message.gas message rfl).2 _ _ _ _ _ h

/-- Under every runner that meets the assumption, each frame of `P` reaches a frame of `Q`.

Or it reaches a frame whose runner fails on its message, so that the run aborts.

That holds for every bound on the gas of messages, at least the gas of the frame. -/
def HoareUnder (fork : Fork) (callee : Evm fork Meter → Message fork → Evm fork Meter → Prop)
    (P Q : Evm fork Meter → Prop) : Prop :=
  ∀ bound (runChild : MessageRunner fork Meter bound), Meets callee runChild →
    ∀ evm, P evm → GasMeter.gasHeld evm.gas ≤ bound →
      ∃ after, Reaches (StepBy fork bound runChild) evm after ∧
        (Q after ∨ AbortsBy fork bound runChild after)

/-- A triple under an assumption whose postcondition is a stopped frame. -/
def SpecUnder (fork : Fork) (callee : Evm fork Meter → Message fork → Evm fork Meter → Prop)
    (P Q : Evm fork Meter → Prop) : Prop :=
  HoareUnder fork callee P fun evm => evm.running = false ∧ Q evm

/-- The frame meets `P` and its gas is within the bound, or its runner fails on its message. -/
def OrAborts (fork : Fork) (bound : Nat) (runChild : MessageRunner fork Meter bound)
    (P : Evm fork Meter → Prop) (evm : Evm fork Meter) : Prop :=
  (P evm ∧ GasMeter.gasHeld evm.gas ≤ bound) ∨ AbortsBy fork bound runChild evm

variable {callee : Evm fork Meter → Message fork → Evm fork Meter → Prop}

/-- A triple under an assumption is a triple over the steps under each runner that meets it.

Its conditions also hold of a frame whose runner fails, and ask for the gas within the bound. -/
theorem hoareUnder_iff_triple [LawfulGasMeter Meter] {P Q : Evm fork Meter → Prop} :
    HoareUnder fork callee P Q ↔ ∀ bound (runChild : MessageRunner fork Meter bound),
      Meets callee runChild →
        Triple (StepBy fork bound runChild) (OrAborts fork bound runChild P)
          (OrAborts fork bound runChild Q) := by
  constructor
  · intro h bound runChild meets evm hp
    rcases hp with ⟨hp, within⟩ | aborted
    · obtain ⟨after, hreach, hq⟩ := h bound runChild meets evm hp within
      refine ⟨after, hreach, hq.imp_left fun hq => ⟨hq, ?_⟩⟩
      exact Nat.le_trans (hreach.gasHeld_le StepBy.gasHeld_le) within
    · exact ⟨evm, .refl evm, .inr aborted⟩
  · intro h bound runChild meets evm hp within
    obtain ⟨after, hreach, hq⟩ := h bound runChild meets evm (.inl ⟨hp, within⟩)
    exact ⟨after, hreach, hq.imp_left And.left⟩

namespace HoareUnder

/-- A triple with no message holds under every assumption. -/
theorem of_hoare {P Q : Evm fork Meter → Prop} (h : Hoare fork P Q) :
    HoareUnder fork callee P Q := fun _ _ _ evm hp _ =>
  let ⟨after, hreach, hq⟩ := h evm hp
  ⟨after, hreach.mono fun hs => .step hs, .inl hq⟩

/-- A step that sends a message, to a frame of `Q` from every frame that ends it.

From each frame of `P`, the step asks for a message.

Each frame that ends the message with at most its gas, and that meets the assumption, resumes.

The resume gives a frame of `Q`, or fails with an error that does not abort.

Then the frame halts exceptionally with that error, and the halted frame is in `Q`. -/
theorem of_child [LawfulGasMeter Meter] {P Q : Evm fork Meter → Prop}
    (h : ∀ evm, P evm → evm.running = true ∧ ∃ caller message resume,
      step fork evm = .ok (.child caller message resume) ∧
      ∀ child, GasMeter.gasHeld child.gas ≤ message.gas → callee caller message child →
        (∃ after, resume child = .ok after ∧ Q after) ∨
          ∃ e, resume child = .error e ∧ e.aborts = false ∧ Q (exceptionalHalt evm e)) :
    HoareUnder fork callee P Q := by
  intro bound runChild meets evm hp within
  obtain ⟨running, caller, message, resume, sent, hresume⟩ := h evm hp
  have lt : message.gas < bound := by
    have := (step_decreases fork running sent).1
    omega
  cases ran : runChild caller message lt with
  | error e => exact ⟨evm, .refl evm, .inr ⟨running, caller, message, resume, sent, lt, e, ran⟩⟩
  | ok child =>
    rcases hresume child.1 child.2 (meets.ok caller message lt child ran) with
      ⟨after, resumed, hq⟩ | ⟨e, failed, halts, hq⟩
    · exact ⟨after, .single (.child running sent lt ran resumed), .inl hq⟩
    · exact ⟨_, .single (.childHalt running sent lt ran failed halts), .inl hq⟩

/-- A stronger assumption on the frames that end messages keeps a triple. -/
theorem assumption {callee' : Evm fork Meter → Message fork → Evm fork Meter → Prop}
    {P Q : Evm fork Meter → Prop} (h : HoareUnder fork callee P Q)
    (stronger : ∀ caller message child, callee' caller message child →
      callee caller message child) :
    HoareUnder fork callee' P Q := fun bound runChild meets =>
  h bound runChild
    ⟨fun caller message lt child ran => stronger _ _ _ (meets.ok caller message lt child ran),
      meets.aborts⟩

variable [LawfulGasMeter Meter]

/-- Sequence: reach the middle condition, then the postcondition from it. -/
theorem seq {P Q R : Evm fork Meter → Prop} (first : HoareUnder fork callee P Q)
    (second : HoareUnder fork callee Q R) : HoareUnder fork callee P R :=
  hoareUnder_iff_triple.mpr fun bound runChild meets =>
    (hoareUnder_iff_triple.mp first bound runChild meets).seq
      (hoareUnder_iff_triple.mp second bound runChild meets)

/-- Consequence: a stronger precondition and a weaker postcondition. -/
theorem consequence {P P' Q Q' : Evm fork Meter → Prop} (h : HoareUnder fork callee P Q)
    (pre : ∀ evm, P' evm → P evm) (post : ∀ evm, Q evm → Q' evm) :
    HoareUnder fork callee P' Q' :=
  hoareUnder_iff_triple.mpr fun bound runChild meets =>
    (hoareUnder_iff_triple.mp h bound runChild meets).consequence
      (fun evm => Or.imp_left (And.imp_left (pre evm)))
      (fun evm => Or.imp_left (And.imp_left (post evm)))

/-- Each case of the precondition with its own triple. -/
theorem cases {P₁ P₂ Q : Evm fork Meter → Prop} (h₁ : HoareUnder fork callee P₁ Q)
    (h₂ : HoareUnder fork callee P₂ Q) :
    HoareUnder fork callee (fun evm => P₁ evm ∨ P₂ evm) Q :=
  hoareUnder_iff_triple.mpr fun bound runChild meets =>
    ((hoareUnder_iff_triple.mp h₁ bound runChild meets).cases
      (hoareUnder_iff_triple.mp h₂ bound runChild meets)).consequence
      (fun _ hp => match hp with
        | .inl ⟨.inl hp, within⟩ => .inl (.inl ⟨hp, within⟩)
        | .inl ⟨.inr hp, within⟩ => .inr (.inl ⟨hp, within⟩)
        | .inr aborted => .inl (.inr aborted))
      fun _ hq => hq

/-- A loop whose body may lower the measure by more than one. -/
theorem loop_lt {I : Nat → Evm fork Meter → Prop} {Q : Evm fork Meter → Prop}
    (body : ∀ k, HoareUnder fork callee (I (k + 1)) fun evm => ∃ j < k + 1, I j evm)
    (exit : HoareUnder fork callee (I 0) Q) (n : Nat) : HoareUnder fork callee (I n) Q :=
  hoareUnder_iff_triple.mpr fun bound runChild meets =>
    Triple.loop_lt (I := fun k => OrAborts fork bound runChild (I k))
      (fun k => (hoareUnder_iff_triple.mp (body k) bound runChild meets).consequence
        (fun _ hp => hp)
        fun _ hq => match hq with
          | .inl ⟨⟨j, hj, hi⟩, within⟩ => ⟨j, hj, .inl ⟨hi, within⟩⟩
          | .inr aborted => ⟨0, Nat.succ_pos k, .inr aborted⟩)
      (hoareUnder_iff_triple.mp exit bound runChild meets) n

/-- A loop: each run of the body lowers the measure by one, and the exit ends it at 0. -/
theorem loop {I : Nat → Evm fork Meter → Prop} {Q : Evm fork Meter → Prop}
    (body : ∀ k, HoareUnder fork callee (I (k + 1)) (I k))
    (exit : HoareUnder fork callee (I 0) Q) (n : Nat) : HoareUnder fork callee (I n) Q :=
  hoareUnder_iff_triple.mpr fun bound runChild meets =>
    Triple.loop (I := fun k => OrAborts fork bound runChild (I k))
      (fun k => hoareUnder_iff_triple.mp (body k) bound runChild meets)
      (hoareUnder_iff_triple.mp exit bound runChild meets) n

end HoareUnder

namespace SpecUnder

/-- A triple to a frame from which the specification holds. -/
theorem seq [LawfulGasMeter Meter] {P Q R : Evm fork Meter → Prop}
    (first : HoareUnder fork callee P Q) (second : SpecUnder fork callee Q R) :
    SpecUnder fork callee P R := HoareUnder.seq first second

/-- Consequence for a specification. -/
theorem consequence [LawfulGasMeter Meter] {P P' Q Q' : Evm fork Meter → Prop}
    (h : SpecUnder fork callee P Q) (pre : ∀ evm, P' evm → P evm)
    (post : ∀ evm, Q evm → Q' evm) : SpecUnder fork callee P' Q' :=
  HoareUnder.consequence h pre fun evm ⟨hs, hq⟩ => ⟨hs, post evm hq⟩

/-- A specification with no message holds under every assumption. -/
theorem of_spec {P Q : Evm fork Meter → Prop} (h : Spec fork P Q) : SpecUnder fork callee P Q :=
  HoareUnder.of_hoare h

/-- From a frame of the precondition, the loop gives a frame of the postcondition, or aborts.

It holds for every runner that meets the assumption.

The loop aborts only when the runner fails, with an error that aborts the run.

The bound on the gas of messages is any bound that holds the gas of the frame. -/
theorem runFrame [LawfulGasMeter Meter] {P Q : Evm fork Meter → Prop}
    (h : SpecUnder fork callee P Q) (meets : Meets callee runChild) {evm : Evm fork Meter}
    (hp : P evm) (within : GasMeter.gasHeld evm.gas ≤ bound) :
    (∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ Q stopped) ∨
    ∃ e, runFrame (step fork) (step_decreases fork) bound runChild evm within = .error e ∧
      e.aborts = true := by
  obtain ⟨after, hreach, ⟨halted, hq⟩ | aborted⟩ := h bound runChild meets evm hp within
  · rw [runFrame_eq_of_reaches StepBy.gasHeld_le StepBy.runFrame_eq hreach within,
      runFrame_of_running_eq_false halted]
    exact .inl ⟨after, rfl, hq⟩
  · rw [runFrame_eq_of_reaches StepBy.gasHeld_le StepBy.runFrame_eq hreach within]
    exact .inr (runFrame_of_abortsBy meets.aborts aborted _)

end SpecUnder

end EthLib.Execution.Evm.Logic
