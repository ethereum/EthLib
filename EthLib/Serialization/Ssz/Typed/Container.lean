module

public import EthLib.Serialization.Ssz.Typed.Class

/-!
# Typed SSZ values: containers

A container is a Lean structure whose fields are SSZ types, read and written as byte arrays.

The rules are stated in EthLib's own terms, one step per comment.

Source: [EIP-7495][eip7495] for the layout of a progressive container.

[eip7495]: https://github.com/ethereum/EIPs/blob/875fcf6d084c096195fec170310514444f537133/EIPS/eip-7495.md#progressivecontaineractive_fields
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- The fields of a container, as a tuple of SSZ types nested to the right. -/
class SszFields (β : Type) where
  -- The fields, in declaration order, form a tuple such as `α × (β × γ)`.
  --
  -- The tuple gives the field types and values, and the structure converts to and from it.
  /-- The field types, in order. -/
  descs : List Desc
  /-- The untyped field values, in order. -/
  toValues : β → List Value
  /-- The typed fields that untyped field values stand for, or why they stand for none. -/
  ofValues : List Value → Except Err β
  /-- The roots of the fields, in order. -/
  roots : β → Except Err (List Bytes)
  /-- The bytes of the fields, in order. -/
  encodes : β → Except Err (List ByteArray)
  /--
  The fields written in place, decoded from their slots, then a reader of the other fields.

  The reader takes the bodies of the fields behind offsets, in order.
  -/
  decodeSlots : List Slot → Except Err (List ByteArray → Except Err β)

open SszType

/-- The last field of a container. -/
instance (priority := low) {α : Type} [SszType α] : SszFields α where
  descs := [desc α]
  toValues a := [toValue a]
  ofValues
    | [value] => ofValue value
    | values => .error (.count 1 values.length)
  roots a := return [← root a]
  encodes a := return [← encode a]
  decodeSlots
    -- A fixed-size field decodes from its bytes in place, before any offset is trusted.
    | .inline bytes :: _ => do
      let a ← decode bytes
      return fun _ => .ok a
    -- A variable-size field decodes from its body, the only one left.
    | _ => .ok fun
      | [bytes] => decode bytes
      | bodies => .error (.count 1 bodies.length)

/-- One field of a container, in front of the fields that follow it. -/
instance {α β : Type} [SszType α] [SszFields β] : SszFields (α × β) where
  descs := desc α :: SszFields.descs β
  toValues pair := toValue pair.1 :: SszFields.toValues pair.2
  ofValues
    | value :: values => return (← ofValue value, ← SszFields.ofValues values)
    | [] => .error (.count (SszFields.descs β).length.succ 0)
  roots pair := return (← root pair.1) :: (← SszFields.roots pair.2)
  encodes pair := return (← encode pair.1) :: (← SszFields.encodes pair.2)
  decodeSlots
    -- A fixed-size field decodes from its bytes in place, before any offset is trusted.
    | .inline bytes :: slots => do
      let a ← decode bytes
      let rest ← SszFields.decodeSlots slots
      return fun bodies => return (a, ← rest bodies)
    -- A variable-size field decodes from the next body, in declaration order.
    | .body _ :: slots => do
      let rest ← SszFields.decodeSlots slots
      return fun
        | bytes :: bodies => return (← decode bytes, ← rest bodies)
        | [] => .error (.count (SszFields.descs β).length.succ 0)
    | [] => .ok fun _ => .error (.count (SszFields.descs β).length.succ 0)

/--
The root of a container whose fields are the given roots, each held as one 32-byte node.

It is the root of the container itself, since a field and its root give the same leaf.
-/
def summaryRoot (shape : List Desc → Desc) (roots : List Bytes) : Except Err Bytes :=
  -- A container, plain or progressive, merkleizes the roots of its fields, one chunk each.
  --
  -- A ByteVector[32] holding a root packs into that one chunk, so it gives the same leaf.
  Ssz.hashTreeRoot (shape (roots.map fun _ => .byteVector bytesPerChunk)) (.seq (roots.map .bytes))

/--
The bytes of a struct whose fields are the given tuple.

It is compiled once for all containers, since a copy for each one would hold all its fields.
-/
@[noinline, nospecialize]
def encodeStruct {β : Type} [SszFields β] (b : β) : Except Err ByteArray := do
  -- The serializations of the fields, laid out by whether each field is fixed-size.
  assemble ((SszFields.descs β).map Desc.isFixed) (← SszFields.encodes b)

/--
The tuple of fields that the bytes of a struct encode.

It is compiled once for all containers, since a copy for each one would hold all its fields.
-/
@[noinline, nospecialize]
def decodeStruct {β : Type} [SszFields β] (data : ByteArray) : Except Err β := do
  -- The steps run in the order of the untyped codec, so the decoder refuses the same input.
  --
  -- So a refusal names the same rule.
  --
  -- EthLib's step 1, the budget, then step 2, the fixed part, read in place.
  let (slots, leading) ← structSlots (SszFields.descs β) data
  -- With no offsets, step 3 checks that the fixed part is the whole input, then fields decode.
  if (bodyStarts slots).isEmpty then
    let bodies ← offsetBodies data slots leading
    (← SszFields.decodeSlots slots) bodies
  -- With offsets, the fixed fields decode first, then step 3 checks the offsets as a whole.
  --
  -- So the fixed fields are decoded before any offset is trusted.
  --
  -- Step 4 then decodes each body, in declaration order.
  else
    let read ← SszFields.decodeSlots slots
    read (← offsetBodies data slots leading)

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
  -- The root is that of the untyped container, computed from the roots of its fields.
  --
  -- Container: merkleize the roots of the fields, one chunk per field, with no mix-in.
  root s := do summaryRoot (.container names) (← SszFields.roots (fields s))
  -- Container: the fields in declaration order, fixed parts and offsets, then the bodies.
  encode s := encodeStruct (fields s)
  decode data := build <$> decodeStruct data

/--
The progressive container with the given layout and field names.

The two conversions must undo each other, which the proofs of the instance check.
-/
@[instance_reducible]
def SszType.progressiveContainer {σ β : Type} [SszFields β] (active : List Bool)
    (names : List String) (fields : σ → β) (build : β → σ) : SszType σ where
  -- EIP-7495: the layout places the fields on a list of active positions and gaps.
  --
  -- It holds one bit per position: a set bit holds the next field, a clear bit is a gap.
  desc := .progressiveContainer active names (SszFields.descs β)
  toValue s := .seq (SszFields.toValues (fields s))
  ofValue
    | .seq values => build <$> SszFields.ofValues values
    | _ => .error .typeMismatch
  -- The root is that of the untyped container, computed from the roots of its fields.
  --
  -- EIP-7495: `H(r || layout)`, `r` the progressive root of one chunk per layout position.
  --
  -- Here `H` is SHA-256, and the layout is packed as bits into one chunk.
  --
  -- An active position holds the root of the next field, and a gap the zero chunk.
  root s := do summaryRoot (.progressiveContainer active names) (← SszFields.roots (fields s))
  -- EIP-7495: serialization and deserialization are those of a Container of the same fields.
  encode s := encodeStruct (fields s)
  decode data := build <$> decodeStruct data

end EthLib.Serialization.Ssz
