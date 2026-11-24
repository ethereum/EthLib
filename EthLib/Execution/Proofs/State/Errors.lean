module

public import EthLib.Execution.State.Errors
import EthLib.Base.Proofs.CodeInjective

/-!
# Proofs: the codes of the state root errors

Two errors with one code come from one constructor, so a code names its constructor.
-/

@[expose] public section

namespace EthLib.Execution.State

/-- Two errors with one code come from one constructor. -/
theorem StateInputError.code_injective (e₁ e₂ : StateInputError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  code_injective StateInputError.code

end EthLib.Execution.State
