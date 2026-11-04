module

public import EthLib.Execution.Evm.Precompiles.Ecrecover.Errors

/-!
# Proofs: the codes of the ECRECOVER errors

Two errors with one code come from one constructor, so a code names its constructor.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Ecrecover

/-- Two errors with one code come from one constructor. -/
theorem EcrecoverError.code_injective (e₁ e₂ : EcrecoverError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [EcrecoverError.code] at h; exact absurd h (by decide))

end EthLib.Execution.Evm.Precompiles.Ecrecover
