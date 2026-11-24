module

public import EthLib.Cryptography.Kzg.Errors
import EthLib.Base.Proofs.CodeInjective

/-!
# Proofs: the codes of the KZG errors

Two errors with one code come from one constructor, so a code names its constructor.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

/-- Two errors with one code come from one constructor. -/
theorem KzgError.code_injective (e₁ e₂ : KzgError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  code_injective KzgError.code

end EthLib.Cryptography.Kzg
