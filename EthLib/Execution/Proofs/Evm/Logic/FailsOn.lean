module

public import EthLib.Execution.Proofs.Evm.Logic.Message

/-!
# Proofs: triples whose runner may fail, on a named set of messages

A triple under an assumption asks the runner of messages to fail only with an error that aborts.

Its run may then end at a frame whose runner fails on the message that the frame sends.

The triples here ask nothing of the errors of the runner.

They name instead the messages on which the runner may fail.

That set is a condition on the frame that sends the message and on the message.

That frame is the one that the step hands to the runner, after it pays for the message.

A runner meets an assumption in the weak sense when each frame that it gives meets the assumption.

It may fail on every message, with an error of any kind.

Take a runner that meets the assumption in this sense, and a bound that holds the gas of the frame.

Then each frame of the precondition reaches a frame of the postcondition.

Or it reaches a frame that sends a message of the named set, and the runner fails on that message.

The run of such a frame fails with the error of the runner.

A runner that meets the assumption, as a triple under it asks, also meets it in the weak sense.

So each triple here is also a triple under the same assumption.

When the set holds every message, the two kinds of triple are the same.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The running frame sends a message of `S`, and the runner fails on that message.

`S` is a condition on the frame that the step hands to the runner, and on the message. -/
def FailsOn (S : Evm fork Meter → Message fork → Prop) (bound : Nat)
    (runChild : MessageRunner fork Meter bound) (evm : Evm fork Meter) : Prop :=
  evm.running = true ∧ ∃ caller message resume,
    step fork evm = .ok (.child caller message resume) ∧ S caller message ∧
      ∃ lt e, runChild caller message lt = .error e

/-- Each frame that the runner gives meets the assumption `callee`.

The runner may fail on every message, with an error of any kind. -/
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
        (Q after ∨ FailsOn S bound runChild after)

/-- A triple whose runner may fail on the messages of `S`, to a stopped frame of `Q`. -/
def SpecOn (fork : Fork) (callee : Evm fork Meter → Message fork → Evm fork Meter → Prop)
    (S : Evm fork Meter → Message fork → Prop) (P Q : Evm fork Meter → Prop) : Prop :=
  HoareOn fork callee S P fun evm => evm.running = false ∧ Q evm

/-- The frame meets `P` and its gas is within the bound.

Or the runner fails on the message of `S` that the frame sends. -/
def OrFailsOn (S : Evm fork Meter → Message fork → Prop) (bound : Nat)
    (runChild : MessageRunner fork Meter bound) (P : Evm fork Meter → Prop)
    (evm : Evm fork Meter) : Prop :=
  (P evm ∧ GasMeter.gasHeld evm.gas ≤ bound) ∨ FailsOn S bound runChild evm

variable {callee : Evm fork Meter → Message fork → Evm fork Meter → Prop}
  {S : Evm fork Meter → Message fork → Prop}

/-- A runner that meets an assumption also gives only frames that meet it. -/
theorem Meets.meetsOk {bound : Nat} {runChild : MessageRunner fork Meter bound}
    (h : Meets callee runChild) : MeetsOk callee runChild :=
  h.ok

/-- A frame whose runner fails on a message of `S` is a frame whose runner fails on its message. -/
theorem FailsOn.abortsBy {bound : Nat} {runChild : MessageRunner fork Meter bound}
    {evm : Evm fork Meter} (h : FailsOn S bound runChild evm) : AbortsBy fork bound runChild evm :=
  let ⟨running, caller, message, resume, sent, _, lt, e, failed⟩ := h
  ⟨running, caller, message, resume, sent, lt, e, failed⟩

/-- A frame whose runner fails on its message fails on a message of the set of every message. -/
theorem AbortsBy.failsOn {bound : Nat} {runChild : MessageRunner fork Meter bound}
    {evm : Evm fork Meter} (h : AbortsBy fork bound runChild evm) :
    FailsOn (fun _ _ => True) bound runChild evm :=
  let ⟨running, caller, message, resume, sent, lt, e, failed⟩ := h
  ⟨running, caller, message, resume, sent, trivial, lt, e, failed⟩

/-- A triple whose runner may fail is a triple over the steps under each runner.

The runner is one whose frames meet the assumption.

Its conditions also hold of a frame whose runner fails on a message of `S`.

They ask for the gas within the bound. -/
theorem hoareOn_iff_triple [LawfulGasMeter Meter] {P Q : Evm fork Meter → Prop} :
    HoareOn fork callee S P Q ↔ ∀ bound (runChild : MessageRunner fork Meter bound),
      MeetsOk callee runChild →
        Triple (StepBy fork bound runChild) (OrFailsOn S bound runChild P)
          (OrFailsOn S bound runChild Q) := by
  constructor
  · intro h bound runChild meets evm hp
    rcases hp with ⟨hp, within⟩ | failed
    · obtain ⟨after, hreach, hq⟩ := h bound runChild meets evm hp within
      refine ⟨after, hreach, hq.imp_left fun hq => ⟨hq, ?_⟩⟩
      exact Nat.le_trans (hreach.gasHeld_le StepBy.gasHeld_le) within
    · exact ⟨evm, .refl evm, .inr failed⟩
  · intro h bound runChild meets evm hp within
    obtain ⟨after, hreach, hq⟩ := h bound runChild meets evm (.inl ⟨hp, within⟩)
    exact ⟨after, hreach, hq.imp_left And.left⟩

namespace HoareOn

/-- A triple with no message holds under every assumption and for every set of messages. -/
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

/-- A stronger assumption on the frames that end messages keeps a triple. -/
theorem assumption {callee' : Evm fork Meter → Message fork → Evm fork Meter → Prop}
    {P Q : Evm fork Meter → Prop} (h : HoareOn fork callee S P Q)
    (stronger : ∀ caller message child, callee' caller message child →
      callee caller message child) :
    HoareOn fork callee' S P Q := fun bound runChild meets =>
  h bound runChild fun caller message lt child ran =>
    stronger _ _ _ (meets caller message lt child ran)

/-- A larger set of messages keeps a triple. -/
theorem mono {S' : Evm fork Meter → Message fork → Prop} {P Q : Evm fork Meter → Prop}
    (h : HoareOn fork callee S P Q)
    (larger : ∀ caller message, S caller message → S' caller message) :
    HoareOn fork callee S' P Q := fun bound runChild meets evm hp within =>
  let ⟨after, hreach, hq⟩ := h bound runChild meets evm hp within
  ⟨after, hreach, hq.imp_right fun ⟨running, caller, message, resume, sent, hS, rest⟩ =>
    ⟨running, caller, message, resume, sent, larger caller message hS, rest⟩⟩

/-- A precondition that gives a witness, with a triple from the condition of each witness. -/
theorem of_exists {α : Type} {P Q : Evm fork Meter → Prop} {R : α → Evm fork Meter → Prop}
    (h : ∀ evm, P evm → ∃ x, R x evm) (each : ∀ x, HoareOn fork callee S (R x) Q) :
    HoareOn fork callee S P Q := fun bound runChild meets evm hp within =>
  let ⟨x, hx⟩ := h evm hp
  each x bound runChild meets evm hx within

/-- Consequence: a stronger precondition and a weaker postcondition. -/
theorem consequence {P P' Q Q' : Evm fork Meter → Prop} (h : HoareOn fork callee S P Q)
    (pre : ∀ evm, P' evm → P evm) (post : ∀ evm, Q evm → Q' evm) :
    HoareOn fork callee S P' Q' := fun bound runChild meets evm hp within =>
  let ⟨after, hreach, hq⟩ := h bound runChild meets evm (pre evm hp) within
  ⟨after, hreach, hq.imp_left (post after)⟩

/-- Such a triple is a triple under the same assumption.

A runner that meets the assumption meets it in the weak sense.

A frame whose runner fails on a message of `S` is a frame whose runner fails on its message. -/
theorem toUnder {P Q : Evm fork Meter → Prop} (h : HoareOn fork callee S P Q) :
    HoareUnder fork callee P Q := fun bound runChild meets evm hp within =>
  let ⟨after, hreach, hq⟩ := h bound runChild meets.meetsOk evm hp within
  ⟨after, hreach, hq.imp_right FailsOn.abortsBy⟩

variable [LawfulGasMeter Meter]

/-- Sequence: reach the middle condition, then the postcondition from it. -/
theorem seq {P Q R : Evm fork Meter → Prop}
    (first : HoareOn fork callee S P Q) (second : HoareOn fork callee S Q R) :
    HoareOn fork callee S P R :=
  hoareOn_iff_triple.mpr fun bound runChild meets =>
    (hoareOn_iff_triple.mp first bound runChild meets).seq
      (hoareOn_iff_triple.mp second bound runChild meets)

/-- Each case of the precondition with its own triple. -/
theorem cases {P₁ P₂ Q : Evm fork Meter → Prop} (h₁ : HoareOn fork callee S P₁ Q)
    (h₂ : HoareOn fork callee S P₂ Q) :
    HoareOn fork callee S (fun evm => P₁ evm ∨ P₂ evm) Q :=
  hoareOn_iff_triple.mpr fun bound runChild meets =>
    ((hoareOn_iff_triple.mp h₁ bound runChild meets).cases
      (hoareOn_iff_triple.mp h₂ bound runChild meets)).consequence
      (fun _ hp => match hp with
        | .inl ⟨.inl hp, within⟩ => .inl (.inl ⟨hp, within⟩)
        | .inl ⟨.inr hp, within⟩ => .inr (.inl ⟨hp, within⟩)
        | .inr failed => .inl (.inr failed))
      fun _ hq => hq

/-- A loop whose body may lower the measure by more than one. -/
theorem loop_lt {I : Nat → Evm fork Meter → Prop} {Q : Evm fork Meter → Prop}
    (body : ∀ k, HoareOn fork callee S (I (k + 1)) fun evm => ∃ j < k + 1, I j evm)
    (exit : HoareOn fork callee S (I 0) Q) (n : Nat) : HoareOn fork callee S (I n) Q :=
  hoareOn_iff_triple.mpr fun bound runChild meets =>
    Triple.loop_lt (I := fun k => OrFailsOn S bound runChild (I k))
      (fun k => (hoareOn_iff_triple.mp (body k) bound runChild meets).consequence
        (fun _ hp => hp)
        fun _ hq => match hq with
          | .inl ⟨⟨j, hj, hi⟩, within⟩ => ⟨j, hj, .inl ⟨hi, within⟩⟩
          | .inr failed => ⟨0, Nat.succ_pos k, .inr failed⟩)
      (hoareOn_iff_triple.mp exit bound runChild meets) n

/-- A loop: each run of the body lowers the measure by one, and the exit ends it at 0. -/
theorem loop {I : Nat → Evm fork Meter → Prop} {Q : Evm fork Meter → Prop}
    (body : ∀ k, HoareOn fork callee S (I (k + 1)) (I k))
    (exit : HoareOn fork callee S (I 0) Q) (n : Nat) : HoareOn fork callee S (I n) Q :=
  hoareOn_iff_triple.mpr fun bound runChild meets =>
    Triple.loop (I := fun k => OrFailsOn S bound runChild (I k))
      (fun k => hoareOn_iff_triple.mp (body k) bound runChild meets)
      (hoareOn_iff_triple.mp exit bound runChild meets) n

end HoareOn

/-- A triple under an assumption is a triple whose runner may fail on every message.

A runner whose frames meet the assumption becomes one that meets it, when its errors abort.

That change keeps its steps, and the frames on which it fails. -/
theorem HoareUnder.toOn {P Q : Evm fork Meter → Prop} (h : HoareUnder fork callee P Q) :
    HoareOn fork callee (fun _ _ => True) P Q := by
  intro bound runChild meets evm hp within
  let aborting : MessageRunner fork Meter bound := fun caller message lt =>
    match runChild caller message lt with
    | .ok child => .ok child
    | .error _ => .error (.forkNotYetSpecified fork)
  have same : ∀ caller message lt child,
      aborting caller message lt = .ok child → runChild caller message lt = .ok child := by
    intro caller message lt child ran
    simp only [aborting] at ran
    split at ran <;> simp_all
  have meets' : Meets callee aborting := by
    refine ⟨fun caller message lt child ran => meets caller message lt child
      (same caller message lt child ran), fun caller message lt e ran => ?_⟩
    simp only [aborting] at ran
    split at ran
    · cases ran
    · cases ran
      rfl
  have steps : ∀ {a b : Evm fork Meter}, StepBy fork bound aborting a b →
      StepBy fork bound runChild a b := by
    intro a b hs
    cases hs with
    | step hs => exact .step hs
    | child running sent lt ran resumed =>
      exact .child running sent lt (same _ _ lt _ ran) resumed
    | childHalt running sent lt ran failed halts =>
      exact .childHalt running sent lt (same _ _ lt _ ran) failed halts
  obtain ⟨after, hreach, hq | ⟨running, caller, message, resume, sent, lt, e, failed⟩⟩ :=
    h bound aborting meets' evm hp within
  · exact ⟨after, hreach.mono steps, .inl hq⟩
  · refine ⟨after, hreach.mono steps,
      .inr ⟨running, caller, message, resume, sent, trivial, lt, ?_⟩⟩
    simp only [aborting] at failed
    split at failed
    · cases failed
    · exact ⟨_, by assumption⟩

/-- A triple whose runner may fail on every message is a triple under the same assumption.

So a triple under an assumption is the case of the set of every message. -/
theorem hoareOn_true_iff {P Q : Evm fork Meter → Prop} :
    HoareOn fork callee (fun _ _ => True) P Q ↔ HoareUnder fork callee P Q :=
  ⟨HoareOn.toUnder, HoareUnder.toOn⟩

namespace SpecOn

/-- Sequence: reach the middle condition, then a stopped frame of the postcondition from it. -/
theorem seq [LawfulGasMeter Meter] {P Q R : Evm fork Meter → Prop}
    (first : HoareOn fork callee S P Q) (second : SpecOn fork callee S Q R) :
    SpecOn fork callee S P R := HoareOn.seq first second

/-- Consequence for a specification. -/
theorem consequence {P P' Q Q' : Evm fork Meter → Prop} (h : SpecOn fork callee S P Q)
    (pre : ∀ evm, P' evm → P evm) (post : ∀ evm, Q evm → Q' evm) : SpecOn fork callee S P' Q' :=
  HoareOn.consequence h pre fun evm ⟨hs, hq⟩ => ⟨hs, post evm hq⟩

/-- A specification with no message holds under every assumption and for every set of messages. -/
theorem of_spec {P Q : Evm fork Meter → Prop} (h : Spec fork P Q) : SpecOn fork callee S P Q :=
  HoareOn.of_hoare h

/-- A larger set of messages keeps a specification. -/
theorem mono {S' : Evm fork Meter → Message fork → Prop} {P Q : Evm fork Meter → Prop}
    (h : SpecOn fork callee S P Q)
    (larger : ∀ caller message, S caller message → S' caller message) :
    SpecOn fork callee S' P Q := HoareOn.mono h larger

/-- Such a specification is a specification under the same assumption. -/
theorem toUnder {P Q : Evm fork Meter → Prop} (h : SpecOn fork callee S P Q) :
    SpecUnder fork callee P Q := HoareOn.toUnder h

/-- From a frame of the precondition, the loop gives a stopped frame of the postcondition.

Or it fails.

The theorem holds for every runner whose frames meet the assumption.

The bound on the gas of messages is any bound that holds the gas of the frame.

When the loop fails, a frame that it reaches sends a message of `S`.

The runner fails on that message, and the loop fails with the same error. -/
theorem runFrame [LawfulGasMeter Meter] {bound : Nat} {runChild : MessageRunner fork Meter bound}
    {P Q : Evm fork Meter → Prop} (h : SpecOn fork callee S P Q) (meets : MeetsOk callee runChild)
    {evm : Evm fork Meter} (hp : P evm) (within : GasMeter.gasHeld evm.gas ≤ bound) :
    (∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ Q stopped) ∨
    ∃ after caller message resume lt e, Reaches (StepBy fork bound runChild) evm after ∧
      after.running = true ∧ step fork after = .ok (.child caller message resume) ∧
      S caller message ∧ runChild caller message lt = .error e ∧
      runFrame (step fork) (step_decreases fork) bound runChild evm within = .error e := by
  obtain ⟨after, hreach, ⟨halted, hq⟩ | failed⟩ := h bound runChild meets evm hp within
  · rw [runFrame_eq_of_reaches StepBy.gasHeld_le StepBy.runFrame_eq hreach within,
      runFrame_of_running_eq_false halted]
    exact .inl ⟨after, rfl, hq⟩
  · obtain ⟨running, caller, message, resume, sent, hS, lt, e, ran⟩ := failed
    rw [runFrame_eq_of_reaches StepBy.gasHeld_le StepBy.runFrame_eq hreach within]
    exact .inr ⟨after, caller, message, resume, lt, e, hreach, running, sent, hS, ran,
      runFrame_of_runChild_eq_error running sent lt ran⟩

end SpecOn

end EthLib.Execution.Evm.Logic
