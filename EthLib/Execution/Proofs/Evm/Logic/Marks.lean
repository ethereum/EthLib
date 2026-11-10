module

public import EthLib.Execution.Proofs.Evm.Call.Marks
public import EthLib.Execution.Proofs.Evm.Logic.Message

/-!
# Proofs: a frame that no revert undoes passes its accounts to delete up to the top

A run of a frame keeps its marks for deletion, under the runner of the messages of code.

This runner runs each message that a step sends, by its call or creation.

So the frames that a run goes through, inside messages that end without an error, lose no mark.

Such a frame is one that no revert undoes.

Each account it marks is marked by the frame that ends the run, when that frame has no error.

The frames that a run goes through are those of a chain of steps under the runner of messages.

They are also those that the code of a message sent on the way goes through.

That message must end without an error, so that no revert undoes them.

These facts hold at every fork.

The proofs about transactions use this for the deletions at the end of a transaction.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)
open EthLib.Execution.State (TransactionState)
open Logic (Reaches StepBy processRunner)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## A run of a frame -/

/-- A run of a frame that returns a frame keeps its marks.

Its messages run under the runner of the messages of code.

That holds whether or not the frame it returns has an error. -/
theorem toDeleteLe_runFrame [LawfulGasMeter Meter] {bound : Nat} {evm after : Evm fork Meter}
    {within : GasMeter.gasHeld evm.gas ≤ bound}
    (h : runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm within =
      .ok after) :
    ToDeleteLe evm after := by
  refine stepRules_toDeleteLe.runFrame (fun caller message _ ended ran => ?_) h
  unfold processRunner at ran
  split at ran
  · exact fun x hx => (toDeleteLe_processMessage_induction message.gas).1 message caller.state
      caller.substate.child _ _ rfl ended ran x hx
  · exact fun x hx => (toDeleteLe_processMessage_induction message.gas).2 message caller.state
      caller.substate.child _ _ rfl ended ran x hx

/-! ## The frames that a run goes through -/

/-- The frames that a run of `evm` goes through, unless a revert of a message inside it undoes them.

It says nothing of whether the run ends with an error; the theorems that use it ask for that.

Its messages run under the runner of the messages of code, with gas below `bound`.

A frame reaches each frame of its chain of steps under that runner.

It also reaches the frames that the code of a message sent on the way goes through.

That message must end without an error, so that the frames of its code count.

The code of the message starts from the state and the child substate of the sender.

It starts with a new meter. -/
inductive Visits [LawfulGasMeter Meter] (fork : Fork) :
    Nat → Evm fork Meter → Evm fork Meter → Prop where
  /-- A frame reached by steps under the runner, the frame itself included. -/
  | frame {bound : Nat} {evm inner : Evm fork Meter} :
      Reaches (StepBy fork bound (processRunner fork bound)) evm inner → Visits fork bound evm inner
  /-- A frame that the code of a message goes through, when the message ends without an error. -/
  | child {bound : Nat} {evm mid caller start inner : Evm fork Meter} {message : Message fork}
      {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
      {ended : { child : Evm fork Meter // GasMeter.gasHeld child.gas ≤ message.gas }} :
      Reaches (StepBy fork bound (processRunner fork bound)) evm mid → mid.running = true →
      step fork mid = .ok (.child caller message resume) →
      ∀ lt : message.gas < bound, processRunner fork bound caller message lt = .ok ended →
      ended.val.error = none →
      CodeStarts fork message caller.state caller.substate.child
        (GasMeter.start message.gas message.reservoir) start →
      Visits fork message.gas start inner → Visits fork bound evm inner

/-! ## Messages -/

/-- A message to code that ends without an error runs its frame to an end without an error.

The message ends with the substate of that end, so with its marks too.

The run starts from the frame of its code, under the runner of the messages of that code. -/
theorem runFrame_of_processMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended} {start : Evm fork Meter}
    (h : processMessage fork message state substate meter held = .ok ended)
    (starts : FrameStarts fork message state substate meter start)
    (ok : ended.val.error = none) :
    ∃ (within : GasMeter.gasHeld start.gas ≤ message.gas) (last : Evm fork Meter),
      runFrame (step fork) (step_decreases fork) message.gas (processRunner fork message.gas)
          start within = .ok last ∧
        last.error = none ∧ ended.val.substate = last.substate := by
  obtain ⟨hpa, entry, entrySubstate, hentry, rfl⟩ := starts
  rw [processMessage] at h
  obtain ⟨ended0, hdo, rolled⟩ := Base.map_ok_iff.mp h
  have hval := congrArg Subtype.val rolled
  simp only at hval
  dsimp only at hdo
  split at hdo
  all_goals obtain ⟨state1, hm, hdo⟩ := Base.bind_ok_iff.mp hdo
  all_goals simp only [hpa] at hdo
  all_goals split at hdo
  · cases hdo
  · rename_i transfers _ after hrun
    cases hdo
    rcases hentry with ⟨hn, -⟩ | ⟨-, hmove, rfl⟩
    · exact absurd transfers hn
    rw [Base.mapError_ok_iff.mp hm] at hmove
    cases hmove
    simp only [transfers, ne_eq, not_false_eq_true, and_self, ↓reduceIte] at hrun
    exact ⟨held, after, hrun, error_rollbackOnError (hval ▸ ok),
      by rw [← hval, (createdAccounts_rollbackOnError _ _).2]⟩
  · cases hdo
  · rename_i transfers _ after hrun
    cases hdo
    obtain ⟨rfl, rfl⟩ := hentry.of_not_transfers transfers
    cases hm
    simp only [transfers, ↓reduceIte] at hrun
    exact ⟨held, after, hrun, error_rollbackOnError (hval ▸ ok),
      by rw [← hval, (createdAccounts_rollbackOnError _ _).2]⟩

/-- A message to code that ends without an error runs its frame to an end without an error.

The message ends with the substate of that end, so with its marks too.

A call or a creation runs its code from the frame where its code starts. -/
theorem runFrame_of_codeStarts [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended} {start : Evm fork Meter}
    (h : (match message.target with
      | some _ => processMessage fork message state substate meter held
      | none => processCreateMessage fork message state substate meter held) = .ok ended)
    (starts : CodeStarts fork message state substate meter start)
    (ok : ended.val.error = none) :
    ∃ (within : GasMeter.gasHeld start.gas ≤ message.gas) (last : Evm fork Meter),
      runFrame (step fork) (step_decreases fork) message.gas (processRunner fork message.gas)
          start within = .ok last ∧
        last.error = none ∧ ended.val.substate = last.substate := by
  unfold CodeStarts at starts
  cases ht : message.target with
  | some _ =>
    simp only [ht] at h starts
    exact runFrame_of_processMessage h starts ok
  | none =>
    simp only [ht] at h starts
    obtain ⟨prepared, hp, starts⟩ := starts
    rw [processCreateMessage] at h
    obtain ⟨prepared', hp', h⟩ := Base.bind_ok_iff.mp h
    rw [hp] at hp'
    cases hp'
    obtain ⟨⟨evm, used⟩, hrun, h⟩ := Base.bind_ok_iff.mp h
    dsimp only at h
    split at h
    · cases h
    · rename_i after hd
      cases h
      obtain ⟨within, last, hlast, err, sub⟩ :=
        runFrame_of_processMessage (ended := ⟨evm, used⟩) hrun starts (error_depositCode hd ok)
      exact ⟨within, last, hlast, err, ((createdAccounts_depositCode hd).2.trans sub)⟩

/-! ## The end of a run -/

/-- A frame that a run goes through, unless a revert undoes it, passes its marks to the end.

The run must end in a frame without an error.

Each account that the frame marks for deletion is then marked by that end. -/
theorem toDeleteLe_of_visits [LawfulGasMeter Meter] {bound : Nat}
    {evm inner after : Evm fork Meter} (visits : Visits fork bound evm inner)
    {within : GasMeter.gasHeld evm.gas ≤ bound}
    (h : runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm within =
      .ok after)
    (ok : after.error = none) :
    ToDeleteLe inner after := by
  induction visits generalizing after with
  | frame hreach =>
    rw [Logic.runFrame_eq_of_reaches StepBy.gasHeld_le StepBy.runFrame_eq hreach within] at h
    exact toDeleteLe_runFrame h
  | @child bound evm mid caller start inner message resume ended hreach running sent lt ran eok
      starts _ ih =>
    rw [Logic.runFrame_eq_of_reaches StepBy.gasHeld_le StepBy.runFrame_eq hreach within] at h
    cases resumed : resume ended.val with
    | error e =>
      cases halts : e.aborts with
      | false =>
        rw [runFrame_of_step_eq_child_error running sent lt ran resumed halts] at h
        cases h
        cases ok
      | true =>
        rw [runFrame_of_step_eq_child_abort running sent lt ran resumed halts] at h
        cases h
    | ok r =>
      rw [runFrame_of_step_eq_child running sent lt ran resumed] at h
      obtain ⟨within', last, hlast, err, sub⟩ := runFrame_of_codeStarts ran starts eok
      have inner_last := ih (within := within') hlast err
      have last_r : ToDeleteLe ended.val r := toDeleteLe_resume sent resumed eok
      intro x hx
      exact toDeleteLe_runFrame h x (last_r x (sub ▸ inner_last x hx))

/-- A message to code that ends without an error passes the marks of the frames it goes through.

Those are the frames that the run of its code goes through, unless a revert undoes them.

Each account that such a frame marks for deletion is marked by the frame that ends the message. -/
theorem toDeleteLe_of_codeStarts [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended} {start inner : Evm fork Meter}
    (h : (match message.target with
      | some _ => processMessage fork message state substate meter held
      | none => processCreateMessage fork message state substate meter held) = .ok ended)
    (starts : CodeStarts fork message state substate meter start)
    (visits : Visits fork message.gas start inner) (ok : ended.val.error = none) :
    ToDeleteLe inner ended.val := by
  obtain ⟨within, last, hlast, err, sub⟩ := runFrame_of_codeStarts h starts ok
  intro x hx
  rw [sub]
  exact toDeleteLe_of_visits visits hlast err x hx

end EthLib.Execution.Evm
