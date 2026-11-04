module

-- The laws unfold the bodies of `EST.pure` and `EST.bind`, which `Init.System.ST` does not expose.
import all Init.System.ST

/-!
# Proofs: monad laws for `IO`

The KZG operations run in `ExceptT KzgError IO`.

Lean core derives the laws of `ExceptT ε m` from those of `m`, but states none for `IO`.

This module proves them, so the core `ExceptT` lemmas apply to KZG.
-/

public section

namespace EthLib.Cryptography.Kzg

/-- `EST ε σ` satisfies the monad laws. -/
instance instLawfulMonadEST {ε σ : Type} : LawfulMonad (EST ε σ) := .mk' _
  (id_map := fun x => funext fun s => by
    dsimp only [Functor.map, EST.bind]
    cases x s <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x _ _ => funext fun s => by
    dsimp only [Bind.bind, EST.bind]
    cases x s <;> rfl)

/-- `IO` satisfies the monad laws. -/
instance instLawfulMonadIO : LawfulMonad IO :=
  inferInstanceAs (LawfulMonad (EST IO.Error IO.RealWorld))

end EthLib.Cryptography.Kzg
