module

public import EthLib.Execution.Proofs.Evm.Logic.Loop

/-!
# Proofs: the frames that a frame reaches through its messages

A step of a frame can ask for a message, a call or a creation, before the frame goes on.

The loop of the interpreter hands each such message to a runner of messages.

The frame then goes on with the frame that ends the message.

So the frames that a frame reaches depend on that runner, and on its bound on the gas of messages.

A step under a runner is a step that sends no message, or a message that the runner runs.

The steps under one runner are deterministic, as the loop is.

A frame that reaches a stopped frame under a runner is the result of the loop with that runner.

The code of the callee is arbitrary, and a triple does not reason about it.

It takes an assumption instead, on the frame that ends each message, the callee.

A runner meets the assumption when it ends each message, and its frame meets the assumption.

A triple under an assumption holds for every runner that meets it, and for every bound.

A callee may change the state, and may even call the caller again.

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

/-- The frames that a frame reaches by steps under a runner of messages, itself included. -/
inductive ReachesBy (fork : Fork) (bound : Nat) (runChild : MessageRunner fork Meter bound) :
    Evm fork Meter → Evm fork Meter → Prop where
  /-- A frame reaches itself. -/
  | refl (evm : Evm fork Meter) : ReachesBy fork bound runChild evm evm
  /-- A step, then the frames that its result reaches. -/
  | step {a b c : Evm fork Meter} : StepBy fork bound runChild a b →
      ReachesBy fork bound runChild b c → ReachesBy fork bound runChild a c

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
  | step hs =>
    cases hs with
    | next running next =>
      exact gasHeld_le_of_measure_lt (show measure _ < measure _ from
        step_decreases fork running next)
    | halt => rw [gasHeld_exceptionalHalt]; omega
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

namespace ReachesBy

/-- A single step reaches its result. -/
theorem single {a b : Evm fork Meter} (h : StepBy fork bound runChild a b) :
    ReachesBy fork bound runChild a b :=
  .step h (.refl b)

/-- The frames reached from a reached frame are reached. -/
theorem trans {a b c : Evm fork Meter} (hab : ReachesBy fork bound runChild a b)
    (hbc : ReachesBy fork bound runChild b c) : ReachesBy fork bound runChild a c := by
  induction hab with
  | refl => exact hbc
  | step h _ ih => exact .step h (ih hbc)

/-- A frame reached with no message is reached under every runner. -/
theorem of_reaches {a b : Evm fork Meter} (h : Reaches fork a b) :
    ReachesBy fork bound runChild a b := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.step hs) ih

/-- A predicate that every step keeps holds at every reached frame. -/
theorem invariant {R : Evm fork Meter → Prop}
    (keeps : ∀ {a b}, StepBy fork bound runChild a b → R a → R b) {a b : Evm fork Meter}
    (h : ReachesBy fork bound runChild a b) (start : R a) : R b := by
  induction h with
  | refl => exact start
  | step hs _ ih => exact ih (keeps hs start)

/-- A reached frame holds at most the gas of the frame it starts from. -/
theorem gasHeld_le [LawfulGasMeter Meter] {a b : Evm fork Meter}
    (h : ReachesBy fork bound runChild a b) : GasMeter.gasHeld b.gas ≤ GasMeter.gasHeld a.gas := by
  induction h with
  | refl => exact Nat.le_refl _
  | step hs _ ih => exact Nat.le_trans ih hs.gasHeld_le

/-- A stopped frame reaches only itself. -/
theorem eq_of_stopped {a b : Evm fork Meter} (h : ReachesBy fork bound runChild a b)
    (stopped : a.running = false) : b = a := by
  cases h with
  | refl => rfl
  | step hs _ => rw [hs.running] at stopped; cases stopped

/-- Two stopped frames that one frame reaches are one frame. -/
theorem stopped_unique {a b c : Evm fork Meter} (hb : ReachesBy fork bound runChild a b)
    (hc : ReachesBy fork bound runChild a c) (sb : b.running = false)
    (sc : c.running = false) : b = c := by
  induction hb generalizing c with
  | refl => exact (hc.eq_of_stopped sb).symm
  | step hs _ ih =>
    cases hc with
    | refl => rw [hs.running] at sc; cases sc
    | step hs' hc' =>
      rw [StepBy.deterministic hs hs'] at *
      exact ih hc' sb sc

end ReachesBy

/-! ## The loop of the interpreter -/

/-- A frame that reaches a stopped frame under a runner runs to it in the loop with that runner. -/
theorem runFrame_of_reachesBy [LawfulGasMeter Meter] {evm stopped : Evm fork Meter}
    (h : ReachesBy fork bound runChild evm stopped) (halted : stopped.running = false)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok stopped := by
  induction h with
  | refl => exact runFrame_of_running_eq_false halted
  | step hs _ ih =>
    cases hs with
    | step hs =>
      cases hs with
      | next running next =>
        rw [runFrame_of_step_eq_next running next]
        exact ih halted _
      | halt running failed halts =>
        rename_i rest
        rw [runFrame_of_step_eq_error running failed halts]
        -- The halted frame is stopped, so the rest of the reach is that frame itself.
        exact congrArg Except.ok (rest.eq_of_stopped rfl).symm
    | child running sent lt ran resumed =>
      rw [runFrame_of_step_eq_child running sent lt ran resumed]
      exact ih halted _
    | childHalt running sent lt ran failed halts =>
      rename_i rest
      rw [runFrame_of_step_eq_child_error running sent lt ran failed halts]
      -- The halted frame is stopped, so the rest of the reach is that frame itself.
      exact congrArg Except.ok (rest.eq_of_stopped rfl).symm

/-! ## Triples under an assumption on the callee -/

/-- The runner ends each message, from a caller, with a frame that the assumption holds of. -/
def Meets (callee : Evm fork Meter → Message fork → Evm fork Meter → Prop)
    (runChild : MessageRunner fork Meter bound) : Prop :=
  ∀ caller message lt, ∃ child, runChild caller message lt = .ok child ∧
    callee caller message child.1

/-- Under every runner that meets the assumption, each frame of `P` reaches a frame of `Q`.

That holds for every bound on the gas of messages, at least the gas of the frame. -/
def HoareUnder (fork : Fork) (callee : Evm fork Meter → Message fork → Evm fork Meter → Prop)
    (P Q : Evm fork Meter → Prop) : Prop :=
  ∀ bound (runChild : MessageRunner fork Meter bound), Meets callee runChild →
    ∀ evm, P evm → GasMeter.gasHeld evm.gas ≤ bound →
      ∃ after, ReachesBy fork bound runChild evm after ∧ Q after

/-- A triple under an assumption whose postcondition is a stopped frame. -/
def SpecUnder (fork : Fork) (callee : Evm fork Meter → Message fork → Evm fork Meter → Prop)
    (P Q : Evm fork Meter → Prop) : Prop :=
  HoareUnder fork callee P fun evm => evm.running = false ∧ Q evm

variable {callee : Evm fork Meter → Message fork → Evm fork Meter → Prop}

namespace HoareUnder

/-- A triple with no message holds under every assumption. -/
theorem of_hoare {P Q : Evm fork Meter → Prop} (h : Hoare fork P Q) :
    HoareUnder fork callee P Q := fun _ _ _ evm hp _ =>
  let ⟨after, hreach, hq⟩ := h evm hp
  ⟨after, .of_reaches hreach, hq⟩

/-- A step that sends a message, to a frame of `Q` from every frame that ends it.

From each frame of `P`, the step asks for a message.

Each frame that ends the message with at most its gas, and that meets the assumption, resumes.

The resume gives a frame of `Q`. -/
theorem of_child [LawfulGasMeter Meter] {P Q : Evm fork Meter → Prop}
    (h : ∀ evm, P evm → evm.running = true ∧ ∃ caller message resume,
      step fork evm = .ok (.child caller message resume) ∧
      ∀ child, GasMeter.gasHeld child.gas ≤ message.gas → callee caller message child →
        ∃ after, resume child = .ok after ∧ Q after) :
    HoareUnder fork callee P Q := by
  intro bound runChild meets evm hp within
  obtain ⟨running, caller, message, resume, sent, hresume⟩ := h evm hp
  have lt : message.gas < bound := by
    have := (step_decreases fork running sent).1
    omega
  obtain ⟨child, ran, hcallee⟩ := meets caller message lt
  obtain ⟨after, resumed, hq⟩ := hresume child.1 child.2 hcallee
  exact ⟨after, .single (.child running sent lt ran resumed), hq⟩

/-- Sequence: reach the middle condition, then the postcondition from it. -/
theorem seq [LawfulGasMeter Meter] {P Q R : Evm fork Meter → Prop}
    (first : HoareUnder fork callee P Q) (second : HoareUnder fork callee Q R) :
    HoareUnder fork callee P R := fun bound runChild meets evm hp within =>
  let ⟨mid, h₁, hq⟩ := first bound runChild meets evm hp within
  let ⟨after, h₂, hr⟩ := second bound runChild meets mid hq (Nat.le_trans h₁.gasHeld_le within)
  ⟨after, h₁.trans h₂, hr⟩

/-- Consequence: a stronger precondition and a weaker postcondition. -/
theorem consequence {P P' Q Q' : Evm fork Meter → Prop} (h : HoareUnder fork callee P Q)
    (pre : ∀ evm, P' evm → P evm) (post : ∀ evm, Q evm → Q' evm) :
    HoareUnder fork callee P' Q' := fun bound runChild meets evm hp within =>
  let ⟨after, hr, hq⟩ := h bound runChild meets evm (pre evm hp) within
  ⟨after, hr, post after hq⟩

/-- A stronger assumption on the callee keeps a triple. -/
theorem assumption {callee' : Evm fork Meter → Message fork → Evm fork Meter → Prop}
    {P Q : Evm fork Meter → Prop} (h : HoareUnder fork callee P Q)
    (stronger : ∀ caller message child, callee' caller message child →
      callee caller message child) :
    HoareUnder fork callee' P Q := fun bound runChild meets =>
  h bound runChild fun caller message lt =>
    let ⟨child, ran, hc⟩ := meets caller message lt
    ⟨child, ran, stronger _ _ _ hc⟩

/-- Each case of the precondition with its own triple. -/
theorem cases {P₁ P₂ Q : Evm fork Meter → Prop} (h₁ : HoareUnder fork callee P₁ Q)
    (h₂ : HoareUnder fork callee P₂ Q) :
    HoareUnder fork callee (fun evm => P₁ evm ∨ P₂ evm) Q :=
  fun bound runChild meets evm hp within =>
    hp.elim (h₁ bound runChild meets evm · within) (h₂ bound runChild meets evm · within)

/-- A loop whose body may lower the measure by more than one. -/
theorem loop_lt [LawfulGasMeter Meter] {I : Nat → Evm fork Meter → Prop}
    {Q : Evm fork Meter → Prop}
    (body : ∀ k, HoareUnder fork callee (I (k + 1)) fun evm => ∃ j < k + 1, I j evm)
    (exit : HoareUnder fork callee (I 0) Q) (n : Nat) : HoareUnder fork callee (I n) Q := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    cases n with
    | zero => exact exit
    | succ k =>
      intro bound runChild meets evm hp within
      obtain ⟨mid, hreach, j, hj, hi⟩ := body k bound runChild meets evm hp within
      obtain ⟨after, hreach', hq⟩ :=
        ih j hj bound runChild meets mid hi (Nat.le_trans hreach.gasHeld_le within)
      exact ⟨after, hreach.trans hreach', hq⟩

/-- A loop: each run of the body lowers the measure by one, and the exit ends it at 0. -/
theorem loop [LawfulGasMeter Meter] {I : Nat → Evm fork Meter → Prop}
    {Q : Evm fork Meter → Prop} (body : ∀ k, HoareUnder fork callee (I (k + 1)) (I k))
    (exit : HoareUnder fork callee (I 0) Q) (n : Nat) : HoareUnder fork callee (I n) Q :=
  loop_lt (fun k => (body k).consequence (fun _ h => h) fun _ h => ⟨k, Nat.lt_succ_self k, h⟩)
    exit n

end HoareUnder

namespace SpecUnder

/-- A triple to a frame from which the specification holds. -/
theorem seq [LawfulGasMeter Meter] {P Q R : Evm fork Meter → Prop}
    (first : HoareUnder fork callee P Q) (second : SpecUnder fork callee Q R) :
    SpecUnder fork callee P R := HoareUnder.seq first second

/-- Consequence for a specification. -/
theorem consequence {P P' Q Q' : Evm fork Meter → Prop} (h : SpecUnder fork callee P Q)
    (pre : ∀ evm, P' evm → P evm) (post : ∀ evm, Q evm → Q' evm) :
    SpecUnder fork callee P' Q' :=
  HoareUnder.consequence h pre fun evm ⟨hs, hq⟩ => ⟨hs, post evm hq⟩

/-- A specification with no message holds under every assumption. -/
theorem of_spec {P Q : Evm fork Meter → Prop} (h : Spec fork P Q) : SpecUnder fork callee P Q :=
  HoareUnder.of_hoare h

/-- From a frame of the precondition, the loop gives a frame of the postcondition.

It holds for every runner that meets the assumption.

The bound on the gas of messages is any bound that holds the gas of the frame. -/
theorem runFrame [LawfulGasMeter Meter] {P Q : Evm fork Meter → Prop}
    (h : SpecUnder fork callee P Q) (meets : Meets callee runChild) {evm : Evm fork Meter}
    (hp : P evm) (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild evm within =
      .ok stopped ∧ Q stopped :=
  let ⟨stopped, hreach, halted, hq⟩ := h bound runChild meets evm hp within
  ⟨stopped, runFrame_of_reachesBy hreach halted within, hq⟩

end SpecUnder

end EthLib.Execution.Evm.Logic
