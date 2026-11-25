module

public import EthLib.Base.Proofs.Except

/-!
# `Base.Proofs.ErrorsMeet`

Whether every failure of a computation that can fail meets a property.

A sequence, a map and a change of error keep it, so a proof follows the steps of a definition.
-/

@[expose] public section

namespace EthLib.Base

/-- Whether every failure of a result meets a property. -/
def ErrorsMeet {ε α : Type} (P : ε → Prop) (r : Except ε α) : Prop :=
  ∀ e, r = .error e → P e

namespace ErrorsMeet

variable {ε α β : Type} {P : ε → Prop}

/-- A success has no failure. -/
theorem ok (a : α) : ErrorsMeet P (.ok a : Except ε α) :=
  fun _ h => by cases h

/-- A pure result has no failure. -/
theorem pure (a : α) : ErrorsMeet P (Pure.pure a : Except ε α) :=
  fun _ h => by cases h

/-- A failure with an error that meets the property meets it. -/
theorem error {e : ε} (h : P e) : ErrorsMeet P (.error e : Except ε α) :=
  fun _ he => by cases he; exact h

/-- A throw of an error that meets the property meets it. -/
theorem throw {e : ε} (h : P e) : ErrorsMeet P (MonadExcept.throw e : Except ε α) :=
  fun _ he => by cases he; exact h

/-- A sequence meets the property when its first part does, and its rest after it. -/
theorem bind {x : Except ε α} {f : α → Except ε β} (hx : ErrorsMeet P x)
    (hf : ∀ a, x = .ok a → ErrorsMeet P (f a)) : ErrorsMeet P (x >>= f) := by
  intro e h
  rcases bind_eq_error h with h | ⟨a, ha, h⟩
  · exact hx e h
  · exact hf a ha e h

/-- A map of a result that meets the property meets it. -/
theorem map {x : Except ε α} (f : α → β) (hx : ErrorsMeet P x) : ErrorsMeet P (f <$> x) := by
  intro e h
  cases hx' : x with
  | error e' => rw [hx'] at h; cases h; exact hx e hx'
  | ok a => rw [hx'] at h; cases h

/-- A change of error meets the property when each changed failure does. -/
theorem mapError {δ : Type} {x : Except δ α} {f : δ → ε} (hf : ∀ e, x = .error e → P (f e)) :
    ErrorsMeet P (x.mapError f) := by
  intro e h
  cases hx : x with
  | error e' => rw [hx] at h; cases h; exact hf e' hx
  | ok a => rw [hx] at h; cases h

end ErrorsMeet

end EthLib.Base
