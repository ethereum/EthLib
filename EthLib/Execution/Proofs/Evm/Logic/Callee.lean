module

public import EthLib.Execution.Proofs.Evm.Logic.Message
public import EthLib.Execution.Proofs.Evm.Logic.Symbolic

/-!
# Proofs: the runner of the interpreter meets the specification of a callee

A triple under an assumption on the frames that end messages holds under each runner that meets it.

The runner of the interpreter runs each message of a call with the code that the message names.

When that code has a specification with no message, the runner meets the assumption it gives.

The assumption covers a message with that code and a target, with no value and no precompile.

Its frame starts from the state of the caller, which before Paris has its target touched.

The frame that ends the message is a stopped frame of the specification, rolled back on a failure.

The callee sends no message itself, since its specification is one with no message.

The code is the one that the message names, and a rule for a call ties it to the address.

The runner touches the target before Paris, moves no value, runs the code, and rolls back a failure.

A message with value moves it from the caller to the target first, and its frame starts from there.

A message that ends with a frame has moved its value.

The runner meets one assumption on such messages.

A message with value to no code ends with no error, in the state that the move gives.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork}

/-- A message with no value and no precompile ends as the run of its code from its frame ends.

The frame that ends the message is the stopped frame of that run, rolled back on a failure.

The frame starts with any lawful meter `meter` that holds at most the gas of the message.

A run that fails makes the message fail with the same error. -/
theorem processMessage_map_val {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {result : Except EvmError (Evm fork Meter)}
    (noValue : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0))
    (noPrecompile : precompileAddress fork message = none)
    (ran : runFrame (step fork) (step_decreases fork) message.gas (processRunner fork message.gas)
      (startFrame message (startState fork message state) substate meter) held = result) :
    (processMessage fork message state substate meter held).map Subtype.val =
      result.map (rollbackOnError state) := by
  have ran' : ∀ within, runFrame (step fork) (step_decreases fork) message.gas
      (processRunner fork message.gas)
      (startFrame message (startState fork message state)
        (if message.shouldTransferValue = true ∧ message.value ≠ 0 then
          { substate with
            logs := pushTransferLog fork substate.logs message.caller message.currentTarget
              message.value } else substate)
        meter) within = result := by
    intro within
    simp only [noValue, ite_false]
    exact ran
  rw [processMessage]
  simp only [Except.map, noPrecompile, noValue, ite_false, bind, pure, Except.bind, Except.pure]
  split <;> rename_i heq
  · split at heq <;> rename_i heq'
    · split at heq' <;> rename_i h3
      · cases heq'
        cases heq
        have hr := (ran' _).symm.trans h3
        subst hr
        rfl
      · cases heq'
    · cases heq
  · split at heq <;> rename_i heq'
    · cases heq
    · split at heq' <;> rename_i h3
      · cases heq'
      · cases heq'
        cases heq
        have hr := (ran' _).symm.trans h3
        subst hr
        rfl

/-- A message with value and no precompile ends as the run of its code from its frame ends.

The value moves from the caller to the target first, and the frame starts from that state.

The frame starts with any lawful meter `meter` that holds at most the gas of the message. -/
theorem processMessage_map_val_value {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]
    {message : Message fork} {state movedState : TransactionState} {substate : Substate}
    {meter : Meter} {held : GasMeter.gasHeld meter ≤ message.gas}
    {result : Except EvmError (Evm fork Meter)}
    (transfers : message.shouldTransferValue = true ∧ message.value ≠ 0)
    (moved : (startState fork message state).moveEther fork message.caller message.currentTarget
      message.value = .ok movedState)
    (noPrecompile : precompileAddress fork message = none)
    (ran : runFrame (step fork) (step_decreases fork) message.gas (processRunner fork message.gas)
      (startFrame message movedState
        { substate with
          logs := pushTransferLog fork substate.logs message.caller message.currentTarget
            message.value }
        meter) held = result) :
    (processMessage fork message state substate meter held).map Subtype.val =
      result.map (rollbackOnError state) := by
  have ran' : ∀ within, runFrame (step fork) (step_decreases fork) message.gas
      (processRunner fork message.gas)
      (startFrame message movedState
        (if message.shouldTransferValue = true ∧ message.value ≠ 0 then
          { substate with
            logs := pushTransferLog fork substate.logs message.caller message.currentTarget
              message.value } else substate)
        meter) within = result := by
    intro within
    simp only [transfers, ne_eq, not_false_eq_true, and_self, ite_true]
    exact ran
  rw [processMessage]
  simp only [Except.map, noPrecompile, transfers, ne_eq, not_false_eq_true, and_self, ite_true,
    bind, pure, Except.bind, Except.pure, Except.mapError, moved]
  split <;> rename_i heq
  · split at heq <;> rename_i heq'
    · split at heq' <;> rename_i h3
      · cases heq'
        cases heq
        have hr := (ran' _).symm.trans h3
        subst hr
        rfl
      · cases heq'
    · cases heq
  · split at heq <;> rename_i heq'
    · cases heq
    · split at heq' <;> rename_i h3
      · cases heq'
      · cases heq'
        cases heq
        have hr := (ran' _).symm.trans h3
        subst hr
        rfl

/-- A message with value that ends with a frame has moved its value. -/
theorem moveEther_of_processMessage_eq_ok {message : Message fork} {state : TransactionState}
    {substate : Substate} {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (transfers : message.shouldTransferValue = true ∧ message.value ≠ 0)
    (h : processMessage fork message state substate = .ok ended) :
    ∃ movedState, (startState fork message state).moveEther fork message.caller
      message.currentTarget message.value = .ok movedState := by
  cases hmove : (startState fork message state).moveEther fork message.caller
      message.currentTarget message.value with
  | ok movedState => exact ⟨movedState, rfl⟩
  | error e =>
    have hv : ¬message.value = 0#256 := transfers.2
    rw [processMessage] at h
    simp [Except.map, transfers, hv, bind, Except.bind, Except.mapError, hmove] at h

/-- A message with no value and no precompile runs its code to a stopped frame of a specification.

The specification holds from the frame that the message starts, and sends no message.

The frame that ends the message is that stopped frame, rolled back on a failure. -/
theorem processMessage_of_spec {message : Message fork} {state : TransactionState}
    {substate : Substate} {P Q : Evm fork Nat → Prop} (h : Spec fork P Q)
    (noValue : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0))
    (noPrecompile : precompileAddress fork message = none)
    (start : P (startFrame message (startState fork message state) substate
      (GasMeter.start message.gas message.reservoir))) :
    ∃ stopped, Q stopped ∧
      (processMessage fork message state substate).map Subtype.val =
        .ok (rollbackOnError state stopped) := by
  obtain ⟨stopped, ran, hq⟩ := h.runFrame (bound := message.gas)
    (runChild := processRunner fork message.gas) start (Nat.le_refl _)
  exact ⟨stopped, hq, processMessage_map_val noValue noPrecompile ran⟩

/-- A frame that stopped with no error needs no rollback. -/
theorem rollbackOnError_of_error_eq_none {snapshot : TransactionState} {evm : Evm fork Nat}
    (h : evm.error = none) : rollbackOnError snapshot evm = evm := by
  simp [rollbackOnError, h]

/-- A frame of no code stops at once, with any gas meter.

The frame it ends with is its start frame, advanced and stopped. -/
theorem runFrame_startFrame_of_code_empty {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Meter}
    (hcode : message.code = .empty) {bound : Nat} {runChild : MessageRunner fork Meter bound}
    {within} :
    runFrame (step fork) (step_decreases fork) bound runChild
        (startFrame message state substate meter) within =
      .ok (advance { startFrame message state substate meter with running := false }) := by
  have hs : step fork (startFrame message state substate meter) =
      .ok (.next (advance { startFrame message state substate meter with running := false })) :=
    step_of_size_le (by simp [startFrame, hcode])
  rw [runFrame_of_step_eq_next rfl hs, runFrame_of_running_eq_false rfl]

/-- A frame of no code stops at once, with no error and with the state it starts from. -/
theorem runFrame_startFrame_empty {message : Message fork} {state : TransactionState}
    {substate : Substate} (hcode : message.code = .empty) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {within} :
    ∃ stopped, runFrame (step fork) (step_decreases fork) bound runChild
        (startFrame (Meter := Nat) message state substate
          (GasMeter.start message.gas message.reservoir)) within =
        .ok stopped ∧ stopped.error = none ∧ stopped.state = state :=
  ⟨_, runFrame_startFrame_of_code_empty hcode, rfl, rfl⟩

/-- A message with value to no code ends with no error, in the state that the move gives. -/
theorem processMessage_empty_value {message : Message fork} {state movedState : TransactionState}
    {substate : Substate} {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hcode : message.code = .empty)
    (transfers : message.shouldTransferValue = true ∧ message.value ≠ 0)
    (moved : (startState fork message state).moveEther fork message.caller message.currentTarget
      message.value = .ok movedState)
    (noPrecompile : precompileAddress fork message = none)
    (h : processMessage fork message state substate = .ok ended) :
    ended.val.error = none ∧ ended.val.state = movedState := by
  obtain ⟨stopped, ran, herr, hst⟩ := runFrame_startFrame_empty (fork := fork) (state := movedState)
    (substate := { substate with
      logs := pushTransferLog fork substate.logs message.caller message.currentTarget
        message.value })
    (runChild := processRunner fork message.gas) (within := Nat.le_refl _) hcode
  have hmap := processMessage_map_val_value transfers moved noPrecompile ran
  rw [h] at hmap
  have he : ended.val = rollbackOnError state stopped := Except.ok.inj hmap
  rw [he, rollbackOnError_of_error_eq_none herr]
  exact ⟨herr, hst⟩

/-- The frame that a message starts is a running frame of its code, at 0, with nothing on it.

It has no return data. -/
theorem at_startFrame {code : ByteArray} {message : Message fork} (hcode : message.code = code)
    (state : TransactionState) (substate : Substate) :
    At code message 0 [] .empty message.gas state substate .empty
      (startFrame message state substate (GasMeter.start message.gas message.reservoir)) := by
  subst hcode
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The assumption that a call with code `code` runs as a specification of that code says.

The message runs that code, has a target, sends no value, and runs no precompile.

`G` holds of the message, and of the state and the substate that it starts from.

Then the frame that ends it is a stopped frame of `Q`.

That frame is the one that the callee stopped in, after the rollback of a failure. -/
def RunsAs (code : ByteArray) (G : Message fork → TransactionState → Substate → Prop)
    (Q : Message fork → TransactionState → Substate → Evm fork Nat → Prop)
    (caller : Evm fork Nat) (message : Message fork) (child : Evm fork Nat) : Prop :=
  message.code = code → message.target.isSome →
    ¬(message.shouldTransferValue = true ∧ message.value ≠ 0) →
    precompileAddress fork message = none → G message caller.state caller.substate.child →
    ∃ stopped, Q message caller.state caller.substate.child stopped ∧
      child = rollbackOnError caller.state stopped

/-- The runner of the interpreter meets the assumption of a specification of the code of a callee.

The specification holds of every message with that code and `G`, from the frame it starts.

The callee may send messages: its specification is a triple under an assumption `A`.

The runner of the interpreter must meet `A` for every bound on the gas of messages.

A run of the callee that aborts makes the runner fail, and the assumption asks nothing of it. -/
theorem meets_of_specUnder {code : ByteArray}
    {G : Message fork → TransactionState → Substate → Prop}
    {Q : Message fork → TransactionState → Substate → Evm fork Nat → Prop}
    {A : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    (hspec : ∀ message state substate, message.code = code → G message state substate →
      SpecUnder fork A
        (At code message 0 [] .empty message.gas (startState fork message state) substate
          .empty)
        (Q message state substate))
    (meets : ∀ bound, Meets A (processRunner fork bound)) (bound : Nat) :
    Meets (RunsAs code G Q) (processRunner fork bound) := by
  refine ⟨fun caller message _ child ran hcode htarget noValue noPrecompile hg => ?_,
    (meets_process fork bound).aborts⟩
  obtain ⟨target, ht⟩ := Option.isSome_iff_exists.mp htarget
  simp only [processRunner, ht] at ran
  rcases (hspec message caller.state caller.substate.child hcode hg).runFrame
      (meets message.gas) (at_startFrame hcode _ _) (Nat.le_refl _) with
    ⟨stopped, hrun, hq⟩ | ⟨e, hrun, -⟩
  · have h := processMessage_map_val (state := caller.state) noValue noPrecompile hrun
    rw [ran] at h
    exact ⟨stopped, hq, Except.ok.inj h⟩
  · have h := processMessage_map_val (state := caller.state) noValue noPrecompile hrun
    rw [ran] at h
    cases h

/-- The runner of the interpreter meets the assumption of a specification with no message.

The callee then sends no message itself. -/
theorem meets_of_spec {code : ByteArray} {G : Message fork → TransactionState → Substate → Prop}
    {Q : Message fork → TransactionState → Substate → Evm fork Nat → Prop}
    (hspec : ∀ message state substate, message.code = code → G message state substate →
      Spec fork
        (At code message 0 [] .empty message.gas (startState fork message state) substate .empty)
        (Q message state substate))
    (bound : Nat) :
    Meets (RunsAs code G Q) (processRunner fork bound) :=
  meets_of_specUnder (A := fun _ _ _ => True)
    (fun message state substate hcode hg =>
      SpecUnder.of_spec (hspec message state substate hcode hg))
    (meets_process fork) bound

/-- The assumption that a call with value to no code moves the value and ends with no error.

The message has no code, a target and no precompile, and moves a value that is not 0.

The frame that ends it has the state that the move of the value gives, from the start state. -/
def PaidNoCode (caller : Evm fork Nat) (message : Message fork) (child : Evm fork Nat) : Prop :=
  message.code = .empty → message.target.isSome → precompileAddress fork message = none →
    message.shouldTransferValue = true ∧ message.value ≠ 0 →
    ∃ movedState, (startState fork message caller.state).moveEther fork message.caller
        message.currentTarget message.value = .ok movedState ∧
      child.error = none ∧ child.state = movedState

/-- The runner of the interpreter meets the assumption on calls with value to no code.

That holds for every bound. -/
theorem meets_paidNoCode (bound : Nat) :
    Meets (PaidNoCode (fork := fork)) (processRunner fork bound) := by
  refine ⟨fun caller message _ child ran hcode htarget noPrecompile transfers => ?_,
    (meets_process fork bound).aborts⟩
  obtain ⟨target, ht⟩ := Option.isSome_iff_exists.mp htarget
  simp only [processRunner, ht] at ran
  obtain ⟨movedState, moved⟩ := moveEther_of_processMessage_eq_ok transfers ran
  exact ⟨movedState, moved, processMessage_empty_value hcode transfers moved noPrecompile ran⟩

end EthLib.Execution.Evm.Logic
