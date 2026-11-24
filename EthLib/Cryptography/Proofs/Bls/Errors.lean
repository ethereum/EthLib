module

public import EthLib.Cryptography.Bls.Errors
import EthLib.Base.Proofs.CodeInjective

/-!
# Proofs: the codes of the BLS errors

Two errors with one code come from one constructor, so a code names its constructor.

Every code lies below 101, the first code of a path error.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

/-- Two errors with one code come from one constructor. -/
theorem BlsError.code_injective (e₁ e₂ : BlsError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  code_injective BlsError.code

/-- BLS error codes lie below 101, the first code of a path error. -/
theorem BlsError.code_lt (e : BlsError) : e.code < 101 := by
  cases e <;> simp [BlsError.code]

end EthLib.Cryptography.Bls
