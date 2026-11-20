module

public import EthLib.Serialization.Ssz.Packing
public import EthLib.Serialization.Ssz.Type.Value

/-! Turning a value into bytes. -/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- Buffer operations shared by the two byte representations of SSZ encoding. -/
class ByteBuffer (B : Type) extends Append B, EmptyCollection B where
  /-- Read the number of bytes. -/
  size : B → Nat
  /-- Reserve capacity for an empty buffer. -/
  reserve : Nat → B
  /-- Load bytes from an ordinary array. -/
  ofArray : Array UInt8 → B

@[default_instance, reducible]
instance : ByteBuffer (Array UInt8) where
  size := Array.size
  reserve := Array.emptyWithCapacity
  ofArray := id

@[reducible]
instance : ByteBuffer ByteArray where
  size := ByteArray.size
  reserve := ByteArray.emptyWithCapacity
  ofArray := ByteArray.mk

variable {B : Type} [ByteBuffer B]

/--
The first byte count that an SSZ offset cannot name.

Compile the bound once so that each element can reuse it.
-/
@[noinline, reducible] def offsetLimit : Nat := 2 ^ (8 * bytesPerOffset)

/--
Bits packed into bytes, closed by a set bit one past the last of them.

The closing bit is what recovers the count on the way back.

An empty value therefore still takes one byte.
-/
def packBitsDelimited (bits : Array Bool) : B :=
  -- One bit more than the data is carried, so the width follows from the count plus one.
  ByteBuffer.ofArray (packBits (bits.push true) ((bits.size + 8) / 8))

/-- The width so far, plus the bytes the fixed part of `parts` occupies.

The loops below carry what they have built so far, so they run in constant stack. -/
@[specialize] def headWidthFrom : List (Bool × B) → Nat → Nat
  | [], width => width
  | (isInline, part) :: rest, width =>
      headWidthFrom rest (width + if isInline then ByteBuffer.size part else bytesPerOffset)

/-- Bytes the fixed part occupies, before any body follows it. -/
def headWidth (parts : List (Bool × B)) : Nat :=
  headWidthFrom parts 0

/-- The width so far, plus the bytes the bodies of `parts` occupy. -/
@[specialize] def bodyWidthFrom : List (Bool × B) → Nat → Nat
  | [], width => width
  | (true, _) :: rest, width => bodyWidthFrom rest width
  | (false, part) :: rest, width => bodyWidthFrom rest (width + ByteBuffer.size part)

/-- Bytes the bodies occupy, which is every part not written in place. -/
def bodyWidth (parts : List (Bool × B)) : Nat :=
  bodyWidthFrom parts 0

/-- The fixed part so far, then the fixed part of `parts`, whose first body begins at `start`. -/
@[specialize] def headOfFrom : Nat → List (Bool × B) → B → B
  | _, [], out => out
  | start, (true, part) :: rest, out => headOfFrom start rest (out ++ part)
  | start, (false, part) :: rest, out =>
      headOfFrom (start + ByteBuffer.size part) rest
        (out ++ ByteBuffer.ofArray (uintBytes bytesPerOffset start))

/--
The fixed part, given where the first body begins.

An inline part sits here in full.

Anything else leaves the offset of its body, and the next body begins past its end.
-/
def headOf (start : Nat) (parts : List (Bool × B)) : B :=
  headOfFrom start parts ∅

/-- The bodies so far, then the bodies of `parts`. -/
@[specialize] def bodiesOfFrom : List (Bool × B) → B → B
  | [], out => out
  | (true, _) :: rest, out => bodiesOfFrom rest out
  | (false, part) :: rest, out => bodiesOfFrom rest (out ++ part)

/-- The bodies, in the order their offsets name them. -/
def bodiesOf (parts : List (Bool × B)) : B :=
  bodiesOfFrom parts ∅

/-- The encoding of parts already paired with their inline flags. -/
@[specialize] def assembleSlots (slots : List (Bool × B)) : Except Err B := do
  -- The first body starts past the fixed part, so that width is also the first offset.
  let leading := headWidth slots
  -- An offset past what four bytes can name would wrap, so the encoding is refused.
  let total := leading + bodyWidth slots
  if total ≥ offsetLimit then throw (.offsetOverflow total)
  -- Reserve the whole output once and append the bodies to the fixed part in place.
  return bodiesOfFrom slots (headOfFrom leading slots (ByteBuffer.reserve total))

/-- The concatenation of parts that all sit in the fixed section. -/
@[specialize] def assembleFixed (parts : List B) : Except Err B := do
  let total := parts.foldl (fun width part => width + ByteBuffer.size part) 0
  if total ≥ offsetLimit then throw (.offsetOverflow total)
  return parts.foldl (· ++ ·) (ByteBuffer.reserve total)

/--
Parts laid out as a struct or a sequence encodes them.

Fixed parts sit in place, variable ones leave an offset behind and follow after.

For the fields `u64`, a list and `u8`:

```text
    [ u64: 8 bytes | offset of the list: 4 bytes | u8: 1 byte | list body ]
```
-/
@[specialize] def assemble (inline : List Bool) (parts : List B) : Except Err B :=
  -- Each part is paired with its flag; `zipWith` pairs them in a loop of constant stack.
  assembleSlots (List.zipWith Prod.mk inline parts)

/-- The option a selector names, or a refusal when it names none. -/
def lookupOption : List Nat → List Desc → Nat → Except Err Desc
  | [], [], selector => .error (.unknownSelector selector)
  | chosen :: selectors, option :: options, selector =>
    if chosen == selector then .ok option else lookupOption selectors options selector
  -- Selectors and options that do not pair up name no union.
  | _, _, _ => .error .badDeclaration

/-- A union selector held to the range a declaration may use. -/
def checkSelector (selector : Nat) : Except Err Unit :=
  if minSelector ≤ selector ∧ selector ≤ maxSelector then .ok ()
  else .error (.unionSelectorRange selector minSelector maxSelector)

/-- A count held to the capacity its shape declares, where it declares one. -/
def boundCheck : Option Nat → Nat → Except Err Unit
  | none, _ => .ok ()
  | some bound, count => if count ≤ bound then .ok () else .error (.overLimit bound count)

mutual

/-- The SSZ encoding of a value, read against the type it is meant to fit. -/
@[specialize] def serialize : Desc → ValueOf B → Except Err B
  | .bool, .bool b => .ok (ByteBuffer.ofArray #[if b then 1 else 0])
  | .uint width, .uint n =>
    if uintFits width n then .ok (ByteBuffer.ofArray (uintBytes width n)) else .error .typeMismatch
  -- A byte array is a sequence of bytes, so it meets the size bound every sequence meets.
  | .byteVector length, .bytes data => do
    if ByteBuffer.size data != length then throw (.scope length (ByteBuffer.size data))
    if ByteBuffer.size data ≥ offsetLimit then throw (.offsetOverflow (ByteBuffer.size data))
    return data
  | .byteList limit, .bytes data => do
    if ByteBuffer.size data > limit then throw (.overLimit limit (ByteBuffer.size data))
    if ByteBuffer.size data ≥ offsetLimit then throw (.offsetOverflow (ByteBuffer.size data))
    return data
  -- A fixed bit count needs no closing bit, since the width already gives it.
  | .bitVector length, .bits data =>
    if data.size == length then .ok (ByteBuffer.ofArray (packBits data ((length + 7) / 8)))
    else .error (.scope length data.size)
  -- A variable bit count needs a closing bit, so trailing zero bits are not lost.
  | .bitList limit, .bits data =>
    if data.size ≤ limit then .ok (packBitsDelimited data)
    else .error (.overLimit limit data.size)
  | .progressiveBitList limit, .bits data => do
    boundCheck limit data.size
    return packBitsDelimited data
  | .vector element length, .seq elements =>
    if elements.length == length then serializeSequence element elements
    else .error (.scope length elements.length)
  | .list element limit, .seq elements =>
    if elements.length ≤ limit then serializeSequence element elements
    else .error (.overLimit limit elements.length)
  | .progressiveList element limit, .seq elements => do
    boundCheck limit elements.length
    serializeSequence element elements
  | .container _ fields, .seq values => serializeStruct fields values
  -- A gap holds no field, so a struct encodes exactly the fields it declares.
  | .progressiveContainer _ _ fields, .seq values => serializeStruct fields values
  | .compatibleUnion selectors options, .union selector data => do
    let option ← lookupOption selectors options selector
    -- The selector is written as one byte, so one the range does not allow is refused, not cut.
    checkSelector selector
    let body ← serialize option data
    return ByteBuffer.ofArray #[UInt8.ofNat selector] ++ body
  | _, _ => .error .typeMismatch

/-- The encoding of a sequence whose elements all share one type. -/
@[specialize] def serializeSequence (element : Desc) (elements : List (ValueOf B)) :
    Except Err B := do
  -- Check every element before allocating the output.
  let parts ← serializeEach element elements
  if parts.isEmpty then return ∅
  if element.isFixed then assembleFixed parts
  else assembleSlots (parts.map fun part => (false, part))

/-- The encoding of a struct, each field read against its own type. -/
@[specialize] def serializeStruct (fields : List Desc) (values : List (ValueOf B)) :
    Except Err B := do
  let parts ← serializeFields fields values
  assemble (fields.map Desc.isFixed) parts

/-- Each element of a sequence encoded on its own. -/
@[specialize] def serializeEach (element : Desc) : List (ValueOf B) → Except Err (List B)
  | [] => .ok []
  | value :: rest => do
    let head ← serialize element value
    serializeEachFrom element rest [head]

/-- The encodings so far, in reverse order, then each element of `values` encoded on its own. -/
@[specialize] def serializeEachFrom (element : Desc) :
    List (ValueOf B) → List B → Except Err (List B)
  | [], done => .ok done.reverse
  | value :: rest, done => do
    let head ← serialize element value
    serializeEachFrom element rest (head :: done)

/-- Each field of a struct encoded on its own, paired with the type it was declared as. -/
@[specialize] def serializeFields : List Desc → List (ValueOf B) → Except Err (List B)
  | [], [] => .ok []
  | field :: fields, value :: values => do
    let head ← serialize field value
    serializeFieldsFrom fields values [head]
  -- A struct given a different number of values than it has fields fits no type.
  | _, _ => .error .typeMismatch

/-- The encodings so far, in reverse order, then each field encoded on its own. -/
@[specialize] def serializeFieldsFrom : List Desc → List (ValueOf B) → List B → Except Err (List B)
  | [], [], done => .ok done.reverse
  | field :: fields, value :: values, done => do
    let head ← serialize field value
    serializeFieldsFrom fields values (head :: done)
  | _, _, _ => .error .typeMismatch

end

end EthLib.Serialization.Ssz
