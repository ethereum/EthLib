module

/-!
# `Base.Except`

When a sequence of two steps in `Except` succeeds.

It sits outside the property modules, so a specification module may import it.

Lean core states no such fact for `Except`.
-/

@[expose] public section

namespace EthLib.Base

/-- Two steps in sequence succeed exactly when the first succeeds with some value.

The second step must then succeed on that value. -/
theorem bind_ok_iff {ε α β : Type} {x : Except ε α} {g : α → Except ε β} {y : β} :
    x >>= g = .ok y ↔ ∃ a, x = .ok a ∧ g a = .ok y := by
  cases x <;> simp [bind, Except.bind]

end EthLib.Base
