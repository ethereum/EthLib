module

public import EthLib.Serialization.Ssz.Typed.Class

/-!
# Typed SSZ values: a value that keeps its root

A rooted value holds a value of an SSZ type together with its root, computed once.

A field that the state roots often and writes rarely then gives its root without hashing again.

The proofs show that the kept root is the root of the value.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- A value of an SSZ type, with its root. -/
structure Rooted (α : Type) [SszType α] where
  /-- The value. -/
  value : α
  /-- The root of the value, or why it has none. -/
  cached : Except Err Bytes
  /-- The kept root is the root of the value. -/
  built : cached = SszType.root value

namespace Rooted

variable {α : Type} [SszType α]

/-- A value with its root, computed here. -/
def of (value : α) : Rooted α :=
  ⟨value, SszType.root value, rfl⟩

/-- Two rooted values with the same value are the same, since the value fixes the root. -/
theorem ext {r s : Rooted α} (same : r.value = s.value) : r = s := by
  cases r
  cases s
  subst same
  simp_all

instance [Repr α] : Repr (Rooted α) where
  reprPrec r := reprPrec r.value

instance [DecidableEq α] : DecidableEq (Rooted α) := fun r s =>
  if same : r.value = s.value then isTrue (ext same)
  else isFalse fun equal => same (equal ▸ rfl)

end Rooted

open SszType in
/-- The SSZ type of the value, which reads its root from the value's kept root. -/
instance {α : Type} [SszType α] : SszType (Rooted α) where
  desc := desc α
  toValue r := toValue r.value
  ofValue value := Rooted.of <$> ofValue value
  root r := r.cached

end EthLib.Serialization.Ssz
