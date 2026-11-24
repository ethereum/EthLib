module

public import EthLib.Execution.Evm.Precompiles.Modexp.Errors
import EthLib.Base.Proofs.CodeInjective

/-!
# Proofs: the codes of the MODEXP errors

Two errors with one code come from one constructor, so a code names its constructor.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Modexp

/-- Two errors with one code come from one constructor. -/
theorem ModexpError.code_injective (e₁ e₂ : ModexpError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  code_injective ModexpError.code

end EthLib.Execution.Evm.Precompiles.Modexp
