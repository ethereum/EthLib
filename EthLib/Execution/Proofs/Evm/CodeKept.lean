module

public import EthLib.Execution.Proofs.Evm.OpTables

/-!
# Proofs: every step keeps the code and its jump destinations

A step keeps them in the frame it gives, in a caller, and in each frame that resumes from it.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The frame holds the valid jump destinations of its code. -/
def HasDestinations (evm : Evm fork Meter) : Prop :=
  evm.validJumpDestinations = validJumpDestinations evm.code

omit [GasMeter Meter] in
/-- A message starts with the valid jump destinations of its code. -/
theorem hasDestinations_startFrame (message : Message fork) (state : State.TransactionState)
    (substate : Substate) (meter : Meter) :
    HasDestinations (startFrame message state substate meter) :=
  rfl

/-- A result of a step from `before` keeps its code and its valid jump destinations.

A frame that waits for a message keeps them, and so does each frame that resumes from it. -/
def StepResult.KeepsCode (before : Evm fork Meter) : StepResult fork Meter → Prop
  | .next after =>
    after.code = before.code ∧ after.validJumpDestinations = before.validJumpDestinations
  | .child caller _ resume =>
    caller.code = before.code ∧ caller.validJumpDestinations = before.validJumpDestinations ∧
      ∀ child after, resume child = .ok after →
        after.code = before.code ∧ after.validJumpDestinations = before.validJumpDestinations

/-- Every step keeps the code and its valid jump destinations, at every fork. -/
theorem step_keepsCode [LawfulGasMeter Meter] {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : step fork evm = .ok result) : result.KeepsCode evm := by
  by_cases hlt : evm.pc < evm.code.size
  · cases hop : Op.ofByte fork evm.code[evm.pc] with
    | none =>
      -- A byte that is no opcode fails the step.
      unfold step at h
      simp only [hlt, ↓reduceDIte, hop] at h
      cases h
    | some op =>
      cases hw : op.stackWords (immediateByte evm.code evm.pc) with
      | none =>
        -- An immediate byte that encodes no words fails the step.
        obtain ⟨e, -, he⟩ := step_eq_error_of_stackWords_eq_none hlt hop hw
        rw [he] at h
        cases h
      | some words =>
        have hf := step_followsTables hlt hop hw h
        cases result with
        | next after => exact ⟨hf.code, hf.jumps⟩
        | child caller _ resume =>
          refine ⟨hf.code, hf.jumps, fun child after hr => ?_⟩
          obtain ⟨code, jumps, -⟩ := hf.resume child after hr
          exact ⟨code.trans hf.code, jumps.trans hf.jumps⟩
  · -- Past the end of its code, the frame stops as STOP does.
    unfold step at h
    simp only [hlt, ↓reduceDIte, stopStep, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩

end EthLib.Execution.Evm
