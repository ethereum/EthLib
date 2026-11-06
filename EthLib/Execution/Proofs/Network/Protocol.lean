module

public import EthLib.Execution.Network.Protocol

/-!
# Proofs: the versions of the eth capability

A version and its number determine each other.

So the number that a node announces in Hello or in Status names at most one version.

The order of the versions is the order of their numbers.
-/

@[expose] public section

namespace EthLib.Execution.Network.EthVersion

/-- The number of a version reads back to that version. -/
theorem ofNumber?_number (v : EthVersion) : ofNumber? v.number = some v := by
  cases v <;> rfl

/-- A number reads to a version exactly when it is the number of that version. -/
theorem ofNumber?_eq_some_iff {n : Nat} {v : EthVersion} : ofNumber? n = some v ↔ v.number = n := by
  constructor
  · intro h
    unfold ofNumber? at h
    split at h <;> cases h <;> rfl
  · rintro rfl
    exact ofNumber?_number v

/-- Two versions with one number are one version. -/
theorem number_injective : Function.Injective number := fun a b h => by
  have := ofNumber?_number a
  rwa [h, ofNumber?_number, Option.some.injEq, eq_comm] at this

/-- A version is at or before another exactly when its number is at most the other's. -/
theorem le_iff_number_le {a b : EthVersion} : a ≤ b ↔ a.number ≤ b.number := by
  cases a <;> cases b <;> decide

/-- A version is before another exactly when its number is below the other's. -/
theorem lt_iff_number_lt {a b : EthVersion} : a < b ↔ a.number < b.number := by
  cases a <;> cases b <;> decide

end EthLib.Execution.Network.EthVersion
