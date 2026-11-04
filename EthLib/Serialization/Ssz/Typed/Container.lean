module

public import EthLib.Serialization.Ssz.Typed.Class

/-!
# Typed SSZ values: containers

A container is a Lean structure whose fields are SSZ types.

Its fields, in declaration order, form a tuple nested to the right, such as `α × (β × γ)`.

The tuple gives the field types and values, and the structure converts to and from it.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- The fields of a container, as a tuple of SSZ types nested to the right. -/
class SszFields (β : Type) where
  /-- The field types, in order. -/
  descs : List Desc
  /-- The untyped field values, in order. -/
  toValues : β → List Value
  /-- The typed fields that untyped field values stand for, or why they stand for none. -/
  ofValues : List Value → Except Err β

open SszType

/-- The last field of a container. -/
instance (priority := low) {α : Type} [SszType α] : SszFields α where
  descs := [desc α]
  toValues a := [toValue a]
  ofValues
    | [value] => ofValue value
    | values => .error (.count 1 values.length)

/-- One field of a container, in front of the fields that follow it. -/
instance {α β : Type} [SszType α] [SszFields β] : SszFields (α × β) where
  descs := desc α :: SszFields.descs β
  toValues pair := toValue pair.1 :: SszFields.toValues pair.2
  ofValues
    | value :: values => return (← ofValue value, ← SszFields.ofValues values)
    | [] => .error (.count (SszFields.descs β).length.succ 0)

/--
The container with the given field names, over a structure and the tuple of its fields.

The two conversions must undo each other, which the proofs of the instance check.
-/
@[instance_reducible]
def SszType.container {σ β : Type} [SszFields β] (names : List String) (fields : σ → β)
    (build : β → σ) : SszType σ where
  desc := .container names (SszFields.descs β)
  toValue s := .seq (SszFields.toValues (fields s))
  ofValue
    | .seq values => build <$> SszFields.ofValues values
    | _ => .error .typeMismatch

end EthLib.Serialization.Ssz
