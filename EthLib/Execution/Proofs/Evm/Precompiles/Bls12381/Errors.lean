module

public import EthLib.Execution.Evm.Precompiles.Bls12381.Errors

/-!
# Proofs: `Evm.Precompiles.Bls12381.Errors`

Two errors with one code come from one constructor, so a code names its constructor.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

/-- Two errors with one code come from one constructor. -/
theorem Bls12381Error.code_injective (e₁ e₂ : Bls12381Error) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [Bls12381Error.code] at h; exact absurd h (by decide))

end EthLib.Execution.Evm.Precompiles.Bls12381
