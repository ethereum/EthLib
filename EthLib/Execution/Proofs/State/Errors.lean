module

public import EthLib.Execution.State.Errors

/-!
# Proofs: the codes of the state root errors

Two errors with one code come from one constructor, so a code names its constructor.
-/

@[expose] public section

namespace EthLib.Execution.State

/-- Two errors with one code come from one constructor. -/
theorem StateInputError.code_injective (e₁ e₂ : StateInputError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [StateInputError.code] at h; exact absurd h (by decide))

end EthLib.Execution.State
