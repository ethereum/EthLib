module

public import EthLib.Base.Except

/-!
# Proofs: assertions, maps and sequences in `Except`

The properties characterize the success and failure of steps that return `Except`.
-/

@[expose] public section

namespace EthLib.Base

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
