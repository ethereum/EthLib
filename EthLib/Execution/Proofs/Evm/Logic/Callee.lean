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

It touches the target before Paris, moves no value, runs the code, and rolls back a failure.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork U256)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork}

/-- The state that a message starts its frame from: before Paris, its target is touched. -/
def startState (fork : Fork) (message : Message fork) (state : TransactionState) :
    TransactionState :=
  if fork < .paris then state.touchAccount message.currentTarget else state

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
    (runChild := fun caller child _ =>
      match child.target with
      | some _ => processMessage fork child caller.state caller.substate.child
      | none => processCreateMessage fork child caller.state caller.substate.child)
    start (Nat.le_refl _)
  refine ⟨stopped, hq, ?_⟩
  have ran' : ∀ within, runFrame (step fork) (step_decreases fork) message.gas
      (fun caller child _ =>
        match child.target with
        | some _ => processMessage fork child caller.state caller.substate.child
        | none => processCreateMessage fork child caller.state caller.substate.child)
      (startFrame message
        (if fork < .paris then state.touchAccount message.currentTarget else state)
        (if message.shouldTransferValue = true ∧ message.value ≠ 0 then
          { substate with
            logs := pushTransferLog fork substate.logs message.caller message.currentTarget
              message.value } else substate)
        (GasMeter.start message.gas message.reservoir)) within = .ok stopped := by
    intro within
    simp only [noValue, ite_false]
    exact ran
  rw [processMessage]
  simp only [Except.map, noPrecompile, noValue, ite_false, bind, pure, Except.bind, Except.pure]
  split <;> rename_i heq
  · split at heq <;> rename_i heq'
    · split at heq' <;> rename_i h3 <;> first | (cases heq'; done) | cases h3.symm.trans (ran' _)
    · cases heq
  · split at heq <;> rename_i heq'
    · cases heq
    · split at heq' <;> rename_i h3
      · cases heq'
      · cases h3.symm.trans (ran' _)
        cases heq'
        cases heq
        rfl

/-- A frame that stopped with no error needs no rollback. -/
theorem rollbackOnError_of_error_eq_none {snapshot : TransactionState} {evm : Evm fork Nat}
    (h : evm.error = none) : rollbackOnError snapshot evm = evm := by
  simp [rollbackOnError, h]

/-- The frame that a message starts is a running frame of its code, at 0, with nothing on it. -/
theorem at_startFrame {code : ByteArray} {message : Message fork} (hcode : message.code = code)
    (state : TransactionState) (substate : Substate) :
    At code message 0 [] .empty message.gas state substate
      (startFrame message state substate (GasMeter.start message.gas message.reservoir)) := by
  subst hcode
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The assumption that a call with code `code` runs as a specification of that code says.

The message runs that code, has a target, sends no value, and runs no precompile.

When `G` holds of the message, the frame that ends it is a stopped frame of `Q`.

That frame is the one that the callee stopped in, after the rollback of a failure. -/
def RunsAs (code : ByteArray) (G : Message fork → Prop)
    (Q : Message fork → TransactionState → Substate → Evm fork Nat → Prop)
    (caller : Evm fork Nat) (message : Message fork) (child : Evm fork Nat) : Prop :=
  message.code = code → message.target.isSome →
    ¬(message.shouldTransferValue = true ∧ message.value ≠ 0) →
    precompileAddress fork message = none → G message →
    ∃ stopped, Q message caller.state caller.substate.child stopped ∧
      child = rollbackOnError caller.state stopped

/-- The runner of the interpreter meets the assumption of a specification of the code of a callee.

The specification holds of every message with that code and `G`, from the frame it starts.

The callee sends no message itself, since the specification is one with no message. -/
theorem meets_of_spec {code : ByteArray} {G : Message fork → Prop}
    {Q : Message fork → TransactionState → Substate → Evm fork Nat → Prop}
    (hspec : ∀ message state substate, message.code = code → G message →
      Spec fork (At code message 0 [] .empty message.gas (startState fork message state) substate)
        (Q message state substate))
    (bound : Nat) :
    Meets (bound := bound) (RunsAs code G Q) fun (caller : Evm fork Nat) message _ =>
      match message.target with
      | some _ => processMessage fork message caller.state caller.substate.child
      | none => processCreateMessage fork message caller.state caller.substate.child := by
  refine ⟨fun caller message _ child ran hcode htarget noValue noPrecompile hg => ?_,
    (meets_process fork bound).aborts⟩
  obtain ⟨target, ht⟩ := Option.isSome_iff_exists.mp htarget
  simp only [ht] at ran
  obtain ⟨stopped, hq, hrun⟩ := processMessage_of_spec (state := caller.state)
    (substate := caller.substate.child) (hspec message caller.state caller.substate.child hcode hg)
    noValue noPrecompile (at_startFrame hcode _ _)
  refine ⟨stopped, hq, ?_⟩
  rw [ran] at hrun
  exact Except.ok.inj hrun

end EthLib.Execution.Evm.Logic
