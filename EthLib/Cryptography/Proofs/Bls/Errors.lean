module

public import EthLib.Cryptography.Bls.Errors

/-!
# Proofs: the codes of the BLS errors

Two errors with one code come from one constructor, so a code names its constructor.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

/-- Two errors with one code come from one constructor. -/
theorem BlsError.code_injective (e₁ e₂ : BlsError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [BlsError.code] at h; exact absurd h (by decide))

end EthLib.Cryptography.Bls
