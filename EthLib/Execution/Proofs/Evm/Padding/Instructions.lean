module

public import EthLib.Execution.Proofs.Evm.Padding.Stack
public import EthLib.Execution.Proofs.Evm.Padding.Frame
public import EthLib.Execution.Proofs.Evm.Padding.State
public import EthLib.Execution.Proofs.Evm.Padding.Messages

/-!
# Proofs: every instruction but CODESIZE runs the same on code with the same bytes

An instruction that gives the next frame keeps the code, so its frame has the other code.

A call or a creation does so for the caller and for each frame that resumes from it.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- Each instruction that gives the next frame, but CODESIZE, runs the same on the same bytes. -/
theorem instruction_swapsCode {op : Op} {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hrun : instruction fork op = some run) (hsize : op ≠ .codesize) : SwapsCode run := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact stackOnlyStep_swapsCode hf
  rcases orElse_eq_some hrun with hf | hrun
  · exact controlFlowStep_swapsCode hf
  rcases orElse_eq_some hrun with hf | hrun
  · exact memoryDataStep_swapsCode hf hsize
  rcases orElse_eq_some hrun with hf | hrun
  · exact returnOpStep_swapsCode hf
  rcases orElse_eq_some hrun with hf | hrun
  · exact environmentStep_swapsCode hf
  rcases orElse_eq_some hrun with hf | hrun
  · exact accountStep_swapsCode hf
  rcases orElse_eq_some hrun with hf | hrun
  · exact storageStep_swapsCode hf
  rcases orElse_eq_some hrun with hf | hrun
  · exact transientStorageStep_swapsCode hf
  rcases orElse_eq_some hrun with hf | hf
  · exact logOpStep_swapsCode hf
  · exact selfdestructOpStep_swapsCode hf

omit [GasMeter Meter] in
/-- A run that swaps the code, run on its own code, keeps the code of each frame it gives. -/
theorem SwapsCode.code_eq {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : SwapsCode run) {evm after : Evm fork Meter} (hr : run evm = .ok after) :
    after.code = evm.code ∧ after.validJumpDestinations = evm.validJumpDestinations := by
  have := h evm evm.code evm.validJumpDestinations (fun _ => rfl) (fun _ => rfl)
  rw [hr] at this
  have := congrArg (fun r => (Except.map Evm.code r, Except.map Evm.validJumpDestinations r)) this
  simp only [Functor.map, Except.map, Prod.mk.injEq, Except.ok.injEq] at this
  exact this

omit [GasMeter Meter] in
/-- A run that swaps the code, run on its own code, gives each frame with that code again. -/
theorem SwapsCodeChild.withCode_self
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} (h : SwapsCodeChild run)
    {evm : Evm fork Meter} {result : StepResult fork Meter} (hr : run evm = .ok result) :
    StepResult.withCode evm.code evm.validJumpDestinations result = result := by
  have := h evm evm.code evm.validJumpDestinations (fun _ => rfl) (fun _ => rfl)
  rw [hr] at this
  exact (Except.ok.inj this).symm

end EthLib.Execution.Evm
