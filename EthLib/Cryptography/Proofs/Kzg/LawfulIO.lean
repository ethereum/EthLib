module

-- The laws unfold the bodies of `EST.pure` and `EST.bind`, which `Init.System.ST` does not expose.
import all Init.System.ST

/-!
# Proofs: monad laws for `IO`

The KZG entry points run in `KzgM`, which is `ExceptT KzgError IO`.
Lean core proves the laws of `ExceptT ε m` from the laws of `m`, but it states no laws for `IO`.
This module proves them, so the core lemmas about `ExceptT` apply to `KzgM`.

`IO` is `EST IO.Error IO.RealWorld`, a state-passing function that returns either a value or an error.
The law for `pure` followed by `bind` holds by definition.
The other two laws hold after a case split on the result of the first action.
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
