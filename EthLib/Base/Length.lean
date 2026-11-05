module

/-!
# `Base.Length`

A bound on the length of a list, checked in as many steps as the bound.

A decoder checks each length it reads against the rest of its input.

Reading the whole rest each time would make a long input cost time quadratic in its length.

A decoder that opens these instances locally pays only the bound at each check.
-/

@[expose] public section

namespace EthLib.Base.Length

/-- Whether a list has at least `n` elements, read in at most `n` steps. -/
def hasAtLeast {α : Type} : Nat → List α → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | n + 1, _ :: rest => hasAtLeast n rest

/-- The check reads the length of the list against the bound. -/
theorem hasAtLeast_iff {α : Type} (n : Nat) (l : List α) :
    hasAtLeast n l = true ↔ n ≤ l.length := by
  induction n generalizing l with
  | zero => simp [hasAtLeast]
  | succ n ih => cases l <;> simp [hasAtLeast, ih]

/-- A list at least as long as a bound, decided in as many steps as the bound. -/
@[instance_reducible] def decideLeLength {α : Type} (n : Nat) (l : List α) :
    Decidable (n ≤ l.length) :=
  decidable_of_iff _ (hasAtLeast_iff n l)

/-- A list shorter than a bound, decided in as many steps as the bound. -/
@[instance_reducible] def decideLengthLt {α : Type} (l : List α) (n : Nat) :
    Decidable (l.length < n) :=
  decidable_of_iff (¬ hasAtLeast n l = true) (by rw [hasAtLeast_iff]; omega)

end EthLib.Base.Length
