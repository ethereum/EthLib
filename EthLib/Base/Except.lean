module

/-!
# `Base.Except`

An assertion in `Except`, and when an assertion, a map or a sequence of two steps succeeds or fails.

It sits outside the property modules, so a specification module may import it.

Lean core states no such fact for `Except`.
-/

@[expose] public section

namespace EthLib.Base

/-- An assertion: success when the condition holds, and the error otherwise. -/
def ensure {ε : Type} (condition : Prop) [Decidable condition] (error : ε) : Except ε Unit :=
  if condition then .ok () else .error error

/-- An assertion succeeds exactly when its condition holds. -/
theorem ensure_ok_iff {ε : Type} {condition : Prop} [Decidable condition] {error : ε}
    {u : Unit} : ensure condition error = .ok u ↔ condition := by
  unfold ensure
  split <;> simp_all

/-- A failed assertion fails with its own error. -/
theorem eq_of_ensure_eq_error {ε : Type} {condition : Prop} [Decidable condition]
    {error other : ε} (failed : ensure condition error = .error other) : other = error := by
  unfold ensure at failed
  split at failed <;> simp_all

/-- Two steps in sequence fail when the first fails, or when the second fails on its value. -/
theorem bind_eq_error {ε α β : Type} {x : Except ε α} {g : α → Except ε β} {e : ε}
    (h : x >>= g = .error e) : x = .error e ∨ ∃ a, x = .ok a ∧ g a = .error e := by
  cases x <;> simp_all [bind, Except.bind]

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
