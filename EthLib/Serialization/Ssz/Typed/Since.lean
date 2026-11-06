module

public import EthLib.Base.Fork
public import EthLib.Serialization.Ssz.Typed.Container

/-!
# Typed SSZ values: fields that a fork adds or removes

A container that every fork shares can hold a field that a later fork adds or removes.

Where the field is absent, it holds nothing, and the codec does not see it.

Where it is present, it is one more SSZ field, at its place in the order.

Both cases are one field that is present when a proposition holds, a function from its proofs.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open Base SszType

/-- The names of fields that appear at a fork: all of them from that fork on, none before. -/
def sinceNames (first fork : Fork) (names : List String) : List String :=
  if first ≤ fork then names else []

/-- The names of fields that a fork removes: all of them before that fork, none from it on. -/
def untilNames (last fork : Fork) (names : List String) : List String :=
  if fork < last then names else []

/-- The names of fields that one fork adds and a later fork removes. -/
def duringNames (first last fork : Fork) (names : List String) : List String :=
  if first ≤ fork ∧ fork < last then names else []

/-- A field present when `p` holds, in front of the fields that follow it. -/
abbrev presentFieldsProd (p : Prop) [Decidable p] (α β : Type) [SszType α] [SszFields β] :
    SszFields ((p → α) × β) where
  descs := if p then desc α :: SszFields.descs β else SszFields.descs β
  toValues pair :=
    if present : p then toValue (pair.1 present) :: SszFields.toValues pair.2
    else SszFields.toValues pair.2
  ofValues values :=
    if present : p then
      match values with
      | value :: rest => do
        let field ← ofValue value
        return (fun _ => field, ← SszFields.ofValues rest)
      | [] => .error (.count (SszFields.descs β).length.succ 0)
    else do
      -- An absent field has one value, so it reads nothing.
      return (fun later => absurd later present, ← SszFields.ofValues values)
  roots pair :=
    if present : p then return (← root (pair.1 present)) :: (← SszFields.roots pair.2)
    else SszFields.roots pair.2

/-- A field present when `p` holds, as the last field of a container. -/
abbrev presentFields (p : Prop) [Decidable p] (α : Type) [SszType α] : SszFields (p → α) where
  descs := if p then [desc α] else []
  toValues field := if present : p then [toValue (field present)] else []
  ofValues values :=
    if present : p then
      match values with
      | [value] => (fun field _ => field) <$> ofValue value
      | values => .error (.count 1 values.length)
    else
      match values with
      | [] => .ok fun later => absurd later present
      | values => .error (.count 0 values.length)
  roots field := if present : p then return [← root (field present)] else return []

/-- A field that appears at a fork, in front of the fields that follow it. -/
instance {first fork : Fork} {α β : Type} [SszType α] [SszFields β] :
    SszFields (Since first fork α × β) :=
  presentFieldsProd (first ≤ fork) α β

/-- A field that appears at a fork, as the last field of a container. -/
instance {first fork : Fork} {α : Type} [SszType α] : SszFields (Since first fork α) :=
  presentFields (first ≤ fork) α

/-- A field that a fork removes, in front of the fields that follow it. -/
instance {last fork : Fork} {α β : Type} [SszType α] [SszFields β] :
    SszFields (Until last fork α × β) :=
  presentFieldsProd (fork < last) α β

/-- A field that a fork removes, as the last field of a container. -/
instance {last fork : Fork} {α : Type} [SszType α] : SszFields (Until last fork α) :=
  presentFields (fork < last) α

/-- A field that one fork adds and a later fork removes, in front of the fields that follow it. -/
instance {first last fork : Fork} {α β : Type} [SszType α] [SszFields β] :
    SszFields (During first last fork α × β) :=
  presentFieldsProd (first ≤ fork ∧ fork < last) α β

/-- A field that one fork adds and a later fork removes, as the last field of a container. -/
instance {first last fork : Fork} {α : Type} [SszType α] :
    SszFields (During first last fork α) :=
  presentFields (first ≤ fork ∧ fork < last) α

end EthLib.Serialization.Ssz
