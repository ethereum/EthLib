module

public import EthLib.Execution.Proofs.Evm.Logic.Callee
public import EthLib.Execution.Proofs.Evm.Logic.Examples.Return42
public import EthLib.Execution.Proofs.Evm.Logic.Examples.CallFlag

/-!
# Proofs: a contract that calls the contract that returns 42

This example composes two specifications through the runner of messages of the interpreter.

The caller is the contract that calls the address in its call data and returns whether it succeeded.

The callee is the contract that returns 42, at that address.

The specification of the callee holds of every message, with at least 18 gas.

So the runner of the interpreter meets the assumption that the callee stops with no error.

The caller then returns the word 1, or the run aborts.

The address must hold no precompile, and the call sends no value.

The rules are those of one counter of gas, from Berlin to the fork before Glamsterdam.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic.CallReturn42

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution.State (TransactionState)
open GasCosts

variable {fork : Fork} {message : Message fork} {state : TransactionState} {substate : Substate}

/-- The assumption that the callee runs the code that returns 42, as its specification says. -/
abbrev Callee : Evm fork Nat → Message fork → Evm fork Nat → Prop :=
  RunsAs Return42.CODE (fun message => 18 ≤ message.gas) fun message state substate =>
    Return42.Returned (message.gas - 18) (startState fork message state) substate

/-- The runner of the interpreter meets the assumption, for every bound. -/
theorem meets (bound : Nat) :
    Meets (bound := bound) (Callee (fork := fork)) fun (caller : Evm fork Nat) message _ =>
      match message.target with
      | some _ => processMessage fork message caller.state caller.substate.child
      | none => processCreateMessage fork message caller.state caller.substate.child :=
  meets_of_spec (fun _ _ _ _ hg => Return42.spec hg) bound

/-- The caller returns the word 1 when the address holds the code that returns 42.

Or the run aborts, when a runner fails with an error that aborts the run. -/
theorem runFrame_process (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {cold : Bool}
    (hcode : state.getCode
      (state.getAccount (toAddressMasked (CallFlag.target message.data))).codeHash =
      .ok Return42.CODE)
    (hprecompile : ¬Precompiles.isPrecompile fork
      (toAddressMasked (CallFlag.target message.data)).toU256.toNat)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked (CallFlag.target message.data) ∉
      substate.accessedAddresses) = cold)
    {gas : Nat} (hgas : 24 + CallFlag.accessCost cold + 960 ≤ gas) {bound : Nat}
    {evm : Evm fork Nat} (start : At CallFlag.CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    (∃ stopped, runFrame (step fork) (step_decreases fork) bound
        (fun caller message _ => match message.target with
          | some _ => processMessage fork message caller.state caller.substate.child
          | none => processCreateMessage fork message caller.state caller.substate.child)
        evm within = .ok stopped ∧
      stopped.running = false ∧ stopped.error = none ∧ stopped.output = wordBytes 1) ∨
    ∃ e, runFrame (step fork) (step_decreases fork) bound
        (fun caller message _ => match message.target with
          | some _ => processMessage fork message caller.state caller.substate.child
          | none => processCreateMessage fork message caller.state caller.substate.child)
        evm within = .error e ∧ e.aborts = true := by
  rcases CallFlag.runFrame_spec hfork hglam hcode (fun _ => by decide) hdepth hcold hgas
    (meets bound) start within with ⟨stopped, ran, hr⟩ | aborted
  · obtain ⟨caller, msg, child, hcallee, -, -, hmg, -, hmtg, hmca, hmcode, hmv, -, -, hhalt⟩ := hr
    have hpre : precompileAddress fork msg = none := by
      simp [precompileAddress, hmca, hprecompile]
    have hg : 18 ≤ msg.gas := by
      rw [hmg]
      unfold callGas maxMessageCallGas
      rw [show (65535 : U256).toNat = 65535 from rfl]
      cases cold <;> simp only [CallFlag.accessCost, ite_true, Bool.false_eq_true, ite_false]
        at hgas ⊢ <;> omega
    obtain ⟨ended, hret, hchild⟩ := hcallee hmcode (by simp [hmtg]) (by simp [hmv]) hpre hg
    have hnone : child.error = none := by
      rw [hchild, rollbackOnError_of_error_eq_none hret.2.1]
      exact hret.2.1
    have hflag : CallFlag.flag child = 1 := by simp [CallFlag.flag, hnone]
    exact .inl ⟨stopped, ran, hhalt.1, hhalt.2.1, by rw [hhalt.2.2.1, hflag]⟩
  · exact .inr aborted

end EthLib.Execution.Evm.Logic.CallReturn42
