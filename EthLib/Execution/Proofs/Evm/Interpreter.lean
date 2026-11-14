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

So the step never fails with an unspecified opcode. -/
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
  [LawfulGasMeter Meter]

/-- The loop with no observer unfolds to one step of the loop in the monad of errors.

A stopped frame stays as it is.

A step that fails halts the frame or aborts the run.

A step that succeeds lets the loop go on, after the message that it sends, if any. -/
theorem runFrame_unfold (evm : Evm fork Meter) (within : GasMeter.gasHeld evm.gas ≤ bound) :
    runFrame step decreases bound runChild evm within =
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
      else .ok evm := by
  unfold runFrame
  rw [runFrameWith]
  by_cases running : evm.running
  · simp only [running, dite_true]
    symm
    split <;> rename_i hs <;> symm <;> split <;> rename_i h <;> rw [hs] at h <;> cases h
    · simp only [bind, Except.bind, pure, Except.pure]
      rename_i e
      by_cases aborts : e.aborts <;>
        simp [aborts, throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map]
    · simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
    · generalize runChild _ _ _ = c
      rcases c with e | ⟨child, used⟩
      · rfl
      dsimp only [bind, Except.bind, pure, Except.pure]
      split <;> rename_i hr <;> symm <;> split <;> rename_i h <;> rw [hr] at h <;> cases h
      · rename_i e
        by_cases aborts : e.aborts <;>
          simp [aborts, throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map]
      · simp only [Functor.map, Except.map]
  · simp [running, Functor.map, Except.map, pure, Except.pure]

/-- The loop leaves a stopped frame as it is. -/
theorem runFrame_of_running_eq_false {evm : Evm fork Meter}
    {within : GasMeter.gasHeld evm.gas ≤ bound} (stopped : evm.running = false) :
    runFrame step decreases bound runChild evm within = .ok evm := by
  rw [runFrame_unfold]
  simp [stopped]

/-- A step that fails with an error that aborts makes the whole run fail with that error. -/
theorem runFrame_of_step_eq_abort {evm : Evm fork Meter}
    {within : GasMeter.gasHeld evm.gas ≤ bound} {e : EvmError}
    (running : evm.running = true) (failed : step evm = .error e) (aborts : e.aborts = true) :
    runFrame step decreases bound runChild evm within = .error e := by
  rw [runFrame_unfold]
  simp only [running, dite_true]
  split <;> simp_all

/-- A step that fails with any other error halts the frame exceptionally. -/
theorem runFrame_of_step_eq_error {evm : Evm fork Meter}
    {within : GasMeter.gasHeld evm.gas ≤ bound} {e : EvmError} (running : evm.running = true)
    (failed : step evm = .error e) (halts : e.aborts = false) :
    runFrame step decreases bound runChild evm within = .ok (exceptionalHalt evm e) := by
  rw [runFrame_unfold]
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
  rw [runFrame_unfold]
  simp only [running, dite_true]
  split <;> rename_i heq <;> rw [next] at heq <;> cases heq
  rfl

/-- A step that sends a message, whose resume gives a frame, lets the loop go on from that frame.

The runner runs the message to the frame `child`. -/
theorem runFrame_of_step_eq_child {evm caller after : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {child : { child : Evm fork Meter // GasMeter.gasHeld child.gas ≤ message.gas }}
    {within : GasMeter.gasHeld evm.gas ≤ bound} (running : evm.running = true)
    (sent : step evm = .ok (.child caller message resume)) (lt : message.gas < bound)
    (ran : runChild caller message lt = .ok child) (resumed : resume child.1 = .ok after) :
    runFrame step decreases bound runChild evm within =
      runFrame step decreases bound runChild after
        (Nat.le_trans (gasHeld_le_of_measure_lt
          ((decreases running sent).2 child.1 after child.2 resumed)) within) := by
  rw [runFrame_unfold]
  simp only [running, dite_true]
  split <;> rename_i heq <;> rw [sent] at heq <;> cases heq
  split <;> rename_i hchild
  · rw [ran] at hchild
    cases hchild
  · rw [ran] at hchild
    cases hchild
    split <;> rename_i hresume <;> rw [resumed] at hresume <;> cases hresume
    rfl

/-- A step that sends a message, whose resume fails with an error that does not abort, halts.

The frame halts exceptionally with that error. -/
theorem runFrame_of_step_eq_child_error {evm caller : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {child : { child : Evm fork Meter // GasMeter.gasHeld child.gas ≤ message.gas }}
    {within : GasMeter.gasHeld evm.gas ≤ bound} {e : EvmError} (running : evm.running = true)
    (sent : step evm = .ok (.child caller message resume)) (lt : message.gas < bound)
    (ran : runChild caller message lt = .ok child) (failed : resume child.1 = .error e)
    (halts : e.aborts = false) :
    runFrame step decreases bound runChild evm within = .ok (exceptionalHalt evm e) := by
  rw [runFrame_unfold]
  simp only [running, dite_true]
  split <;> rename_i heq <;> rw [sent] at heq <;> cases heq
  split <;> rename_i hchild
  · rw [ran] at hchild
    cases hchild
  · rw [ran] at hchild
    cases hchild
    split <;> rename_i hresume <;> rw [failed] at hresume <;> cases hresume
    simp [halts]

/-- A step that sends a message, whose resume fails with an error that aborts, makes the run fail.

The run fails with that error. -/
theorem runFrame_of_step_eq_child_abort {evm caller : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {child : { child : Evm fork Meter // GasMeter.gasHeld child.gas ≤ message.gas }}
    {within : GasMeter.gasHeld evm.gas ≤ bound} {e : EvmError} (running : evm.running = true)
    (sent : step evm = .ok (.child caller message resume)) (lt : message.gas < bound)
    (ran : runChild caller message lt = .ok child) (failed : resume child.1 = .error e)
    (aborts : e.aborts = true) :
    runFrame step decreases bound runChild evm within = .error e := by
  rw [runFrame_unfold]
  simp only [running, dite_true]
  split <;> rename_i heq <;> rw [sent] at heq <;> cases heq
  split <;> rename_i hchild
  · rw [ran] at hchild
    cases hchild
  · rw [ran] at hchild
    cases hchild
    split <;> rename_i hresume <;> rw [failed] at hresume <;> cases hresume
    simp [aborts]

/-- A step that sends a message, which the runner fails to run, makes the run fail.

The run fails with the error of the runner. -/
theorem runFrame_of_runChild_eq_error {evm caller : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {within : GasMeter.gasHeld evm.gas ≤ bound} {e : EvmError} (running : evm.running = true)
    (sent : step evm = .ok (.child caller message resume)) (lt : message.gas < bound)
    (failed : runChild caller message lt = .error e) :
    runFrame step decreases bound runChild evm within = .error e := by
  rw [runFrame_unfold]
  simp only [running, dite_true]
  split <;> rename_i heq <;> rw [sent] at heq <;> cases heq
  split <;> rename_i hchild <;> rw [failed] at hchild <;> cases hchild
  rfl

/-- Induction on the loop with no observer, with each case given the value of the run.

It has the cases of the loop, in its order.

A step aborts, halts or goes on.

Or it sends a message, which fails, or whose resume aborts, halts or goes on.

Or the frame is stopped. -/
theorem runFrame_induct
    (motive : (evm : Evm fork Meter) → GasMeter.gasHeld evm.gas ≤ bound →
      Except EvmError (Evm fork Meter) → Prop)
    (case1 : ∀ evm within, evm.running = true → ∀ e, step evm = .error e → e.aborts = true →
      motive evm within (.error e))
    (case2 : ∀ evm within, evm.running = true → ∀ e, step evm = .error e → ¬e.aborts = true →
      motive evm within (.ok (exceptionalHalt evm e)))
    (case3 : ∀ evm within, evm.running = true → ∀ after, step evm = .ok (.next after) →
      ∀ (lower : measure after < measure evm),
        motive after (Nat.le_trans (gasHeld_le_of_measure_lt lower) within)
          (runFrame step decreases bound runChild after
            (Nat.le_trans (gasHeld_le_of_measure_lt lower) within)) →
        motive evm within
          (runFrame step decreases bound runChild after
            (Nat.le_trans (gasHeld_le_of_measure_lt lower) within)))
    (case4 : ∀ evm within, evm.running = true → ∀ caller message resume,
      step evm = .ok (.child caller message resume) →
      ∀ (lower : StepResult.Decreases evm (.child caller message resume)) e,
        runChild caller message (Nat.lt_of_lt_of_le lower.1 within) = .error e →
        motive evm within (.error e))
    (case5 : ∀ evm within, evm.running = true → ∀ caller message resume,
      step evm = .ok (.child caller message resume) →
      ∀ (lower : StepResult.Decreases evm (.child caller message resume)) child
        (used : GasMeter.gasHeld child.gas ≤ message.gas),
        runChild caller message (Nat.lt_of_lt_of_le lower.1 within) = .ok ⟨child, used⟩ →
        ∀ e, resume child = .error e → e.aborts = true → motive evm within (.error e))
    (case6 : ∀ evm within, evm.running = true → ∀ caller message resume,
      step evm = .ok (.child caller message resume) →
      ∀ (lower : StepResult.Decreases evm (.child caller message resume)) child
        (used : GasMeter.gasHeld child.gas ≤ message.gas),
        runChild caller message (Nat.lt_of_lt_of_le lower.1 within) = .ok ⟨child, used⟩ →
        ∀ e, resume child = .error e → ¬e.aborts = true →
          motive evm within (.ok (exceptionalHalt evm e)))
    (case7 : ∀ evm within, evm.running = true → ∀ caller message resume,
      step evm = .ok (.child caller message resume) →
      ∀ (lower : StepResult.Decreases evm (.child caller message resume)) child
        (used : GasMeter.gasHeld child.gas ≤ message.gas),
        runChild caller message (Nat.lt_of_lt_of_le lower.1 within) = .ok ⟨child, used⟩ →
        ∀ after, resume child = .ok after →
        ∀ (lower : measure after < measure evm),
          motive after (Nat.le_trans (gasHeld_le_of_measure_lt lower) within)
            (runFrame step decreases bound runChild after
              (Nat.le_trans (gasHeld_le_of_measure_lt lower) within)) →
          motive evm within
            (runFrame step decreases bound runChild after
              (Nat.le_trans (gasHeld_le_of_measure_lt lower) within)))
    (case8 : ∀ evm within, ¬evm.running = true → motive evm within (.ok evm))
    (evm : Evm fork Meter) (within : GasMeter.gasHeld evm.gas ≤ bound) :
    motive evm within (runFrame step decreases bound runChild evm within) := by
  induction h : measure evm using Nat.strongRecOn generalizing evm with
  | _ n ih =>
  rw [runFrame_unfold]
  split
  · rename_i running
    split
    · rename_i e hs
      split
      · exact case1 evm within running e hs ‹_›
      · exact case2 evm within running e hs ‹_›
    · rename_i after hs
      have lower : measure after < measure evm := decreases running hs
      exact case3 evm within running after hs lower (ih _ (h ▸ lower) _ _ rfl)
    · rename_i caller message resume hs
      have d := decreases running hs
      dsimp only
      split
      · rename_i e hc
        exact case4 evm within running caller message resume hs d e hc
      · rename_i child used hc
        split
        · rename_i e hr
          split
          · exact case5 evm within running caller message resume hs d child used hc e hr ‹_›
          · exact case6 evm within running caller message resume hs d child used hc e hr ‹_›
        · rename_i after hr
          have lower : measure after < measure evm := d.2 child after used hr
          exact case7 evm within running caller message resume hs d child used hc after hr lower
            (ih _ (h ▸ lower) _ _ rfl)
  · exact case8 evm within ‹_›

/-- A run ends with no more gas than the frame it starts from.

The recursion of messages needs this bound, so that a message gives back at most its own gas. -/
theorem gasHeld_runFrame_le {evm after : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound}
    (h : runFrame step decreases bound runChild evm within = .ok after) :
    GasMeter.gasHeld after.gas ≤ GasMeter.gasHeld evm.gas := by
  revert h
  refine runFrame_induct
    (motive := fun evm _ r => r = .ok after → GasMeter.gasHeld after.gas ≤ GasMeter.gasHeld evm.gas)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ evm within <;> intros <;> rename_i h
  all_goals first
    | (cases h; done)
    | (cases h; simp only [exceptionalHalt, LawfulGasMeter.gasHeld_exhaust]; omega)
    | (cases h; exact Nat.le_refl _)
    | (rename_i lower ih; exact Nat.le_trans (ih h) (gasHeld_le_of_measure_lt lower))

/-- A run fails only with an error that aborts, when its runner of messages fails only so. -/
theorem aborts_of_runFrame_eq_error
    (aborts : ∀ caller message lt e, runChild caller message lt = .error e → e.aborts = true)
    {evm : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound} {e : EvmError}
    (h : runFrame step decreases bound runChild evm within = .error e) : e.aborts = true := by
  revert h
  refine runFrame_induct (motive := fun _ _ r => r = .error e → e.aborts = true)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ evm within <;> intros <;> rename_i h
  all_goals first
    | (cases h; done)
    | (rename_i ih; exact ih h)
    | (cases h; assumption)
    | (cases h; exact aborts _ _ _ _ (by assumption))

/-- Every run that succeeds ends with a stopped frame. -/
theorem running_runFrame {evm after : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound}
    (h : runFrame step decreases bound runChild evm within = .ok after) :
    after.running = false := by
  revert h
  refine runFrame_induct (motive := fun _ _ r => r = .ok after → after.running = false)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ evm within <;> intros <;> rename_i h
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
  revert hmod h
  refine runFrame_induct (motive := fun evm _ r => evm.memory.size % 32 = 0 → r = .ok after →
    after.memory.size % 32 = 0) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ evm within <;> intros <;> rename_i hmod h
  all_goals first
    | (cases h; done)
    | (cases h; exact hmod)
    | (rename_i result _ ih; exact ih (next hmod result) h)
    | (rename_i resumed _ ih; exact ih (resumes hmod (by assumption) resumed) h)

end Loop

/-- An exceptional halt drops the output and records the error. -/
theorem exceptionalHalt_output (evm : Evm fork Meter) (e : EvmError) :
    (exceptionalHalt evm e).output = .empty ∧ (exceptionalHalt evm e).error = some e :=
  ⟨rfl, rfl⟩

end EthLib.Execution.Evm
