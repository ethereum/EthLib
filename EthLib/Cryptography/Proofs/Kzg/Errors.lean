module

public import EthLib.Cryptography.Kzg.Errors

/-!
# Proofs: the codes of the KZG errors

Two errors with one code come from one constructor, so a code names its constructor.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

/-- Two errors with one code come from one constructor. -/
theorem KzgError.code_injective (e₁ e₂ : KzgError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [KzgError.code] at h; exact absurd h (by decide))

end EthLib.Cryptography.Kzg
