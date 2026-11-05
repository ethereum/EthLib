module

/-!
# `Base.Except`

When a map or a sequence of two steps in `Except` succeeds.

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

/-- A check followed by a step succeeds exactly when the check passes and the step succeeds. -/
theorem bind_unit_ok_iff {ε β : Type} {x : Except ε Unit} {g : Unit → Except ε β} {y : β} :
    x >>= g = .ok y ↔ x = .ok () ∧ g () = .ok y := by
  cases x <;> simp [bind, Except.bind]

/-- A map succeeds exactly when the step under it succeeds with some value.

The map then sends that value to the result. -/
theorem map_ok_iff {ε α β : Type} {f : α → β} {x : Except ε α} {y : β} :
    f <$> x = .ok y ↔ ∃ a, x = .ok a ∧ f a = y := by
  cases x <;> simp [Functor.map, Except.map]

end EthLib.Base
