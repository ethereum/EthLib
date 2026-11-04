module

public import EthLib.Base.Fork
public import EthLib.Serialization.Ssz.Typed.Container

/-!
# Typed SSZ values: fields that appear at a fork

A container that every fork shares can hold a field that a later fork adds.

At a fork before that one, the field holds nothing, and the codec does not see it.

From that fork on, the field is one more SSZ field, at its place in the order.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open Base SszType

/-- The names of fields that appear at a fork: all of them from that fork on, none before. -/
def sinceNames (first fork : Fork) (names : List String) : List String :=
  if first ≤ fork then names else []

/-- A field that appears at a fork, in front of the fields that follow it. -/
instance {first fork : Fork} {α β : Type} [SszType α] [SszFields β] :
    SszFields (Since first fork α × β) where
  descs := if first ≤ fork then desc α :: SszFields.descs β else SszFields.descs β
  toValues pair :=
    if present : first ≤ fork then toValue (pair.1 present) :: SszFields.toValues pair.2
    else SszFields.toValues pair.2
  ofValues values :=
    if present : first ≤ fork then
      match values with
      | value :: rest => do
        let field ← ofValue value
        return (fun _ => field, ← SszFields.ofValues rest)
      | [] => .error (.count (SszFields.descs β).length.succ 0)
    else do
      -- Before its fork the field has one value, so it reads nothing.
      return (fun later => absurd later present, ← SszFields.ofValues values)

/-- A field that appears at a fork, as the last field of a container. -/
instance {first fork : Fork} {α : Type} [SszType α] : SszFields (Since first fork α) where
  descs := if first ≤ fork then [desc α] else []
  toValues field := if present : first ≤ fork then [toValue (field present)] else []
  ofValues values :=
    if present : first ≤ fork then
      match values with
      | [value] => (fun field _ => field) <$> ofValue value
      | values => .error (.count 1 values.length)
    else
      match values with
      | [] => .ok fun later => absurd later present
      | values => .error (.count 0 values.length)

end EthLib.Serialization.Ssz
