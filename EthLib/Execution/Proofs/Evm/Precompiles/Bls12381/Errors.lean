module

public import EthLib.Execution.Evm.Precompiles.Bls12381.Errors
import EthLib.Base.Proofs.CodeInjective

/-!
# Proofs: `Evm.Precompiles.Bls12381.Errors`

Two errors with one code come from one constructor, so a code names its constructor.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

/-- Two errors with one code come from one constructor. -/
theorem Bls12381Error.code_injective (e₁ e₂ : Bls12381Error) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  code_injective Bls12381Error.code

end EthLib.Execution.Evm.Precompiles.Bls12381
