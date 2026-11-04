module

public import EthLib.Cryptography.Secp256r1.Errors

/-!
# Proofs: the codes of the secp256r1 errors

Two errors with one code come from one constructor, so a code names its constructor.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256r1

/-- Two errors with one code come from one constructor. -/
theorem Secp256r1Error.code_injective (e₁ e₂ : Secp256r1Error) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [Secp256r1Error.code] at h; exact absurd h (by decide))

end EthLib.Cryptography.Secp256r1
