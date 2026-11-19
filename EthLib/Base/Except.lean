module

/-!
# `Base.Except`

An assertion in `Except`, with the success condition of two steps in sequence.

It sits outside the property modules, so a specification module may import it.

The remaining success and failure properties live in `EthLib/Base/Proofs/Except.lean`.
-/

@[expose] public section

namespace EthLib.Base

/-- An assertion: success when the condition holds, and the error otherwise. -/
def ensure {ε : Type} (condition : Prop) [Decidable condition] (error : ε) : Except ε Unit :=
  if condition then .ok () else .error error

/-- Two steps in sequence succeed exactly when the first succeeds with some value.

The second step must then succeed on that value. -/
theorem bind_ok_iff {ε α β : Type} {x : Except ε α} {g : α → Except ε β} {y : β} :
    x >>= g = .ok y ↔ ∃ a, x = .ok a ∧ g a = .ok y := by
  cases x <;> simp [bind, Except.bind]

end EthLib.Base
