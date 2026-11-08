module

public import EthLib.Serialization.Ssz.Typed.Class

/-!
# Typed SSZ values: containers

A container is a Lean structure whose fields are SSZ types.

Its fields, in declaration order, form a tuple nested to the right, such as `α × (β × γ)`.

The tuple gives the field types and values, and the structure converts to and from it.

A progressive container also places its fields on a layout of active positions and gaps.

That layout follows [EIP-7495](https://eips.ethereum.org/EIPS/eip-7495).

A container reads and writes its bytes as byte arrays, field by field.

Its slicing repeats the steps of the untyped codec in the same order, so it refuses the same input.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- What one slot of a struct's fixed part holds, cut from a byte array. -/
inductive ByteSlot where
  /-- The field itself, written in place. -/
  | inline (bytes : ByteArray)
  /-- Where the field's body begins, the body following the fixed part. -/
  | body (start : Nat)

/-- The slot of the untyped codec at the same place. -/
def ByteSlot.toSlot : ByteSlot → Slot
  | .inline bytes => .inline bytes.data
  | .body start => .body start

/-- Where each field's bytes sit inside a struct's encoding. -/
def readByteSlots : List Desc → ByteArray → Nat → Except Err (List ByteSlot × Nat)
  | [], _, position => .ok ([], position)
  | field :: fields, data, position =>
    match field.fixedSize with
    | some width => do
      if position + width > data.size then throw .truncated
      let (rest, ending) ← readByteSlots fields data (position + width)
      return (.inline (data.extract position (position + width)) :: rest, ending)
    | none => do
      if position + bytesPerOffset > data.size then throw .truncated
      let (rest, ending) ← readByteSlots fields data (position + bytesPerOffset)
      return (.body (readUintBytes data position bytesPerOffset) :: rest, ending)

/--
The slots of a struct's fixed part, and where that part ends.

The budget is settled first, so no slot is read past the input.
-/
def byteStructSlots (fields : List Desc) (data : ByteArray) :
    Except Err (List ByteSlot × Nat) := do
  if data.size ≥ 2 ^ (8 * bytesPerOffset) then throw (.offsetOverflow data.size)
  structBudget fields data.size
  readByteSlots fields data 0

/-- Where each body begins, in the order the table names them. -/
def byteBodyStarts : List ByteSlot → List Nat
  | [] => []
  | .inline _ :: rest => byteBodyStarts rest
  | .body start :: rest => start :: byteBodyStarts rest

/-- The body of each field behind an offset, once the offsets are checked against the input. -/
def byteBodies (data : ByteArray) (slots : List ByteSlot) (leading : Nat) :
    Except Err (List ByteArray) := do
  let offsets := byteBodyStarts slots
  -- With no bodies, the slots just read are the whole encoding.
  if offsets.isEmpty then
    if data.size != leading then throw (.scope leading data.size)
    return []
  -- The first body starts where the slots end; anything else leaves a gap or an overlap.
  if offsets.headD 0 != leading then throw (.firstOffset leading (offsets.headD 0))
  let spans ← offsetSpans offsets data.size
  return List.zipWith (fun start span => data.extract start (start + span)) offsets spans

/-- The width so far, plus the bytes the fixed part of `parts` occupies. -/
def byteHeadWidthFrom : List (Bool × ByteArray) → Nat → Nat
  | [], width => width
  | (isInline, part) :: rest, width =>
      byteHeadWidthFrom rest (width + if isInline then part.size else bytesPerOffset)

/-- The width so far, plus the bytes the bodies of `parts` occupy. -/
def byteBodyWidthFrom : List (Bool × ByteArray) → Nat → Nat
  | [], width => width
  | (true, _) :: rest, width => byteBodyWidthFrom rest width
  | (false, part) :: rest, width => byteBodyWidthFrom rest (width + part.size)

/-- The fixed part so far, then the fixed part of `parts`, whose first body begins at `start`. -/
def byteHeadOfFrom : Nat → List (Bool × ByteArray) → ByteArray → ByteArray
  | _, [], out => out
  | start, (true, part) :: rest, out => byteHeadOfFrom start rest (out ++ part)
  | start, (false, part) :: rest, out =>
      byteHeadOfFrom (start + part.size) rest (out ++ ⟨uintBytes bytesPerOffset start⟩)

/-- The bodies so far, then the bodies of `parts`. -/
def byteBodiesOfFrom : List (Bool × ByteArray) → ByteArray → ByteArray
  | [], out => out
  | (true, _) :: rest, out => byteBodiesOfFrom rest out
  | (false, part) :: rest, out => byteBodiesOfFrom rest (out ++ part)

/--
Parts laid out as a struct encodes them, as one byte array.

Fixed parts sit in place, variable ones leave an offset behind and follow after.
-/
def assembleBytes (inline : List Bool) (parts : List ByteArray) : Except Err ByteArray := do
  let slots := List.zipWith Prod.mk inline parts
  let leading := byteHeadWidthFrom slots 0
  let total := leading + byteBodyWidthFrom slots 0
  -- An offset past what four bytes can name would wrap, so the encoding is refused.
  if total ≥ 2 ^ (8 * bytesPerOffset) then throw (.offsetOverflow total)
  -- The whole encoding is written into one array, sized once.
  return byteBodiesOfFrom slots (byteHeadOfFrom leading slots (ByteArray.emptyWithCapacity total))

/-- The fields of a container, as a tuple of SSZ types nested to the right. -/
class SszFields (β : Type) where
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
  decodeSlots : List ByteSlot → Except Err (List ByteArray → Except Err β)

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
    | .inline bytes :: _ => do
      let a ← decode bytes
      return fun _ => .ok a
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
    | .inline bytes :: slots => do
      let a ← decode bytes
      let rest ← SszFields.decodeSlots slots
      return fun bodies => return (a, ← rest bodies)
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
  Ssz.hashTreeRoot (shape (roots.map fun _ => .byteVector bytesPerChunk)) (.seq (roots.map .bytes))

/--
The bytes of a struct whose fields are the given tuple.

It is compiled once for all containers, since a copy for each one would hold all its fields.
-/
@[noinline, nospecialize]
def encodeStruct {β : Type} [SszFields β] (b : β) : Except Err ByteArray := do
  assembleBytes ((SszFields.descs β).map Desc.isFixed) (← SszFields.encodes b)

/--
The tuple of fields that the bytes of a struct encode.

The steps run in the order of the untyped codec, so a refusal names the same rule.

The fixed fields are decoded before any offset is trusted, if there are offsets at all.

It is compiled once for all containers, since a copy for each one would hold all its fields.
-/
@[noinline, nospecialize]
def decodeStruct {β : Type} [SszFields β] (data : ByteArray) : Except Err β := do
  let (slots, leading) ← byteStructSlots (SszFields.descs β) data
  if (byteBodyStarts slots).isEmpty then
    let bodies ← byteBodies data slots leading
    (← SszFields.decodeSlots slots) bodies
  else
    let read ← SszFields.decodeSlots slots
    read (← byteBodies data slots leading)

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
  root s := do summaryRoot (.container names) (← SszFields.roots (fields s))
  encode s := encodeStruct (fields s)
  decode data := build <$> decodeStruct data

/--
The progressive container with the given layout and field names.

The layout holds one bit per position: a set bit holds the next field, a clear bit is a gap.

The two conversions must undo each other, which the proofs of the instance check.
-/
@[instance_reducible]
def SszType.progressiveContainer {σ β : Type} [SszFields β] (active : List Bool)
    (names : List String) (fields : σ → β) (build : β → σ) : SszType σ where
  desc := .progressiveContainer active names (SszFields.descs β)
  toValue s := .seq (SszFields.toValues (fields s))
  ofValue
    | .seq values => build <$> SszFields.ofValues values
    | _ => .error .typeMismatch
  root s := do summaryRoot (.progressiveContainer active names) (← SszFields.roots (fields s))
  encode s := encodeStruct (fields s)
  decode data := build <$> decodeStruct data

end EthLib.Serialization.Ssz
