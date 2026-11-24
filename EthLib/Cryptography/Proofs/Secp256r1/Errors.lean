module

public import EthLib.Cryptography.Secp256r1.Errors
import EthLib.Base.Proofs.CodeInjective

/-!
# Proofs: the codes of the secp256r1 errors

Two errors with one code come from one constructor, so a code names its constructor.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256r1

/-- Two errors with one code come from one constructor. -/
theorem Secp256r1Error.code_injective (e₁ e₂ : Secp256r1Error) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  code_injective Secp256r1Error.code

end EthLib.Cryptography.Secp256r1
