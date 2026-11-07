module

public import EthLib.Execution.Proofs.Evm.Logic.Callee
public import EthLib.Execution.Proofs.Evm.Logic.Examples.CallFlag
public import EthLib.Execution.Proofs.State.Frame

/-!
# Proofs: a chain of three frames through the runner of the interpreter

This example composes a callee that itself calls, through the runner of messages of the interpreter.

The outer frame runs the contract that calls the address in its call data and returns the result.

That address, `B`, holds the same code, so the middle frame runs it again, with no call data.

So the middle frame calls the address of the word 0, which holds no code and is no precompile.

That call ends with no error, so the middle frame returns 1, and so does the outer frame.

The logic does not reason about a callee that calls back into its caller and depends on its state.

Before Paris, the call to the address of the word 0 may create its empty account.

No frame writes the account of `B` or of the outer address.

So the chain needs no such reasoning, and the result holds even when `B` is the outer address.

The rules are those of one counter of gas, from Berlin to the fork before Glamsterdam.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic.CallChain

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution.State (TransactionState)
open GasCosts

variable {fork : Fork}

/-- The address of the word 0, which the middle frame calls, since it has no call data. -/
def ZERO : Base.Address := toAddressMasked (CallFlag.target .empty)

/-- The assumption on the middle frame: it runs with no call data, the depth and the gas it needs.

The address of the word 0 holds no code in the state it starts from. -/
def Middle (message : Message fork) (state : TransactionState) (_substate : Substate) : Prop :=
  message.data = .empty ∧ message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧ 3584 ≤ message.gas ∧
    (startState fork message state).getCode
      ((startState fork message state).getAccount ZERO).codeHash = .ok .empty

/-- What the middle frame ends with: no error, and the word 1. -/
def Ended (_message : Message fork) (_state : TransactionState) (_substate : Substate)
    (evm : Evm fork Nat) : Prop :=
  evm.error = none ∧ evm.output = wordBytes 1

/-- The address of the word 0 is no precompile. -/
theorem isPrecompile_zero : Precompiles.isPrecompile fork ZERO.toU256.toNat = false := by
  have h : ZERO.toU256.toNat = 0 := by decide
  rw [h]
  rfl

/-- The middle frame runs its code to the word 1.

That holds under the assumption that a call to no code succeeds. -/
theorem middle (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (message : Message fork) (state : TransactionState) (substate : Substate)
    (h : Middle message state substate) :
    SpecUnder fork NoCodeSucceeds
      (At CallFlag.CODE message 0 [] .empty message.gas (startState fork message state) substate)
      (Ended message state substate) := by
  obtain ⟨hdata, hdepth, hgas, hzero⟩ := h
  have hzero' : (startState fork message state).getCode ((startState fork message state).getAccount
      (toAddressMasked (CallFlag.target message.data))).codeHash = .ok .empty := by
    rw [hdata]
    exact hzero
  have hpre : Precompiles.isPrecompile fork
      (toAddressMasked (CallFlag.target message.data)).toU256.toNat = false := by
    rw [hdata]
    exact isPrecompile_zero
  apply (CallFlag.spec_noCode hfork hglam hzero' hpre hdepth rfl
    (by unfold CallFlag.accessCost; split <;> omega)).consequence (fun _ hp => hp)
  rintro evm ⟨hr, hout⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hhalt⟩ := hr
  exact ⟨hhalt.2.1, hout⟩

/-- The assumption that the address of the outer call runs the middle frame to the word 1. -/
abbrev Callee : Evm fork Nat → Message fork → Evm fork Nat → Prop :=
  RunsAs CallFlag.CODE Middle Ended

/-- The runner of the interpreter meets the assumption, for every bound. -/
theorem meets (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) (bound : Nat) :
    Meets (Callee (fork := fork)) (processRunner fork bound) :=
  meets_of_specUnder (fun message state substate _ h => middle hfork hglam message state substate h)
    (meets_process_noCode fork) bound

variable {message : Message fork} {state : TransactionState} {substate : Substate}

/-- The outer frame returns the word 1, with the runner of messages of the interpreter.

The address in its call data, `B`, holds the code of the contract, and is no precompile.

The address of the word 0 holds no code, so it differs from `B`.

The depth leaves room for two more frames, and the frame holds the gas of both calls.

Or the run aborts, when a runner fails with an error that aborts the run. -/
theorem runFrame_process (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {cold : Bool}
    (hcode : state.getCode
      (state.getAccount (toAddressMasked (CallFlag.target message.data))).codeHash =
      .ok CallFlag.CODE)
    (hprecompile : Precompiles.isPrecompile fork
      (toAddressMasked (CallFlag.target message.data)).toU256.toNat = false)
    (hzero : state.getCode (state.getAccount ZERO).codeHash = .ok .empty)
    (hdepth : message.depth + 2 ≤ STACK_DEPTH_LIMIT)
    (hcold : decide (toAddressMasked (CallFlag.target message.data) ∉
      substate.accessedAddresses) = cold)
    {gas : Nat} (hgas : 24 + CallFlag.accessCost cold + 3700 ≤ gas) {bound : Nat}
    {evm : Evm fork Nat} (start : At CallFlag.CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    (∃ stopped, runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .ok stopped ∧
      stopped.running = false ∧ stopped.error = none ∧ stopped.output = wordBytes 1) ∨
    ∃ e, runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .error e ∧ e.aborts = true := by
  rcases CallFlag.runFrame_spec hfork hglam hcode (fun _ => by decide) (by omega) hcold
    (by omega) (meets hfork hglam bound) start within with ⟨stopped, ran, hr⟩ | aborted
  · -- The address of the word 0 holds no code, and `B` holds the code, so they differ.
    have hne : ZERO ≠ toAddressMasked (CallFlag.target message.data) := by
      intro heq
      rw [← heq, hzero] at hcode
      cases hcode
    obtain ⟨caller, msg, child, hcallee, -, hst, hmg, hmt, hmtg, hmca, hmcode, hmv, hmd, hmdep,
      hhalt⟩ := hr
    have hpre : precompileAddress fork msg = none := by
      simp [precompileAddress, hmca, hprecompile]
    have hg : 3584 ≤ msg.gas := by
      have htw : fork ≥ .tangerineWhistle := Nat.le_trans (by decide) hfork
      rw [hmg, show (65535 : U256).toNat = 65535 from rfl]
      cases cold <;> simp only [CallFlag.accessCost, ite_true, Bool.false_eq_true, ite_false]
        at hgas ⊢ <;> rw [messageCallGas_of_le htw (by omega)] <;>
        simp only [maxMessageCallGas] <;> omega
    have hzero' : (startState fork msg caller.state).getCode
        ((startState fork msg caller.state).getAccount ZERO).codeHash = .ok .empty := by
      have hread : caller.state.getCode (caller.state.getAccount ZERO).codeHash = .ok .empty := by
        rw [hst]
        exact hzero
      unfold startState
      split
      · rw [TransactionState.getCode_touchAccount, hmt,
          TransactionState.getAccount_touchAccount hne]
        exact hread
      · exact hread
    obtain ⟨ended, ⟨hnone, -⟩, hchild⟩ := hcallee hmcode (by simp [hmtg]) (by simp [hmv]) hpre
      ⟨hmd, by rw [hmdep]; omega, hg, hzero'⟩
    have hchild_none : child.error = none := by
      rw [hchild, rollbackOnError_of_error_eq_none hnone]
      exact hnone
    have hflag : CallFlag.flag child = 1 := by simp [CallFlag.flag, hchild_none]
    exact .inl ⟨stopped, ran, hhalt.1, hhalt.2.1, by rw [hhalt.2.2.1, hflag]⟩
  · exact .inr aborted

end EthLib.Execution.Evm.Logic.CallChain
