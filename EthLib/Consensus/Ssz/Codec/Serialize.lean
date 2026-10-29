import EthLib.Consensus.Ssz.Type.Value
import EthLib.Consensus.Ssz.Codec.Error

/-! Turning a value into bytes. -/

namespace EthLib.Consensus.Ssz

/--
An unsigned integer as little-endian bytes of the given width.

The low byte is written first, so each step drops the byte it just wrote.

A value wider than the given width is truncated.

A caller needing exact recovery has to check the range itself.
-/
def uintBytes : (width : Nat) → (value : Nat) → Bytes
  | 0, _ => #[]
  | width + 1, value => #[UInt8.ofNat (value % 256)] ++ uintBytes width (value / 256)

/-- The eight bits that land in one byte, gathered into it. -/
def packByte (bits : Array Bool) (byteIndex : Nat) : UInt8 :=
  let held (offset : Nat) : UInt8 :=
    -- An absent bit contributes zero, which is also the high padding of the last byte.
    if bits[byteIndex * 8 + offset]?.getD false then (1 : UInt8) <<< UInt8.ofNat offset else 0
  held 0 ||| held 1 ||| held 2 ||| held 3 ||| held 4 ||| held 5 ||| held 6 ||| held 7

/--
Bits packed into bytes, the first bit lowest in the first byte.

    bits [1, 0, 1, 1]  ->  byte 0 = 0b00001101

Each byte is built from the bits that land in it, rather than one bit at a time into a buffer.

A byte then stands on its own, which is what lets a bit be read back where it was put.
-/
def packBits (bits : Array Bool) (byteCount : Nat) : Bytes :=
  Array.ofFn (n := byteCount) fun byteIndex => packByte bits byteIndex.val

/--
Bits packed into bytes, closed by a set bit one past the last of them.

The closing bit is what recovers the count on the way back.

An empty value therefore still takes one byte.
-/
def packBitsDelimited (bits : Array Bool) : Bytes :=
  -- One bit more than the data is carried, so the width follows from the count plus one.
  packBits (bits.push true) ((bits.size + 8) / 8)

/-- Bytes the fixed part occupies, before any body follows it. -/
def headWidth : List (Bool × Bytes) → Nat
  | [] => 0
  | (isInline, part) :: rest =>
      (if isInline then part.size else bytesPerOffset) + headWidth rest

/-- Bytes the bodies occupy, which is every part not written in place. -/
def bodyWidth : List (Bool × Bytes) → Nat
  | [] => 0
  | (true, _) :: rest => bodyWidth rest
  | (false, part) :: rest => part.size + bodyWidth rest

/--
The fixed part, given where the first body begins.

An inline part sits here in full.

Anything else leaves the offset of its body, and the next body begins past its end.
-/
def headOf (start : Nat) : List (Bool × Bytes) → Bytes
  | [] => #[]
  | (true, part) :: rest => part ++ headOf start rest
  | (false, part) :: rest =>
      uintBytes bytesPerOffset start ++ headOf (start + part.size) rest

/-- The bodies, in the order their offsets name them. -/
def bodiesOf : List (Bool × Bytes) → Bytes
  | [] => #[]
  | (true, _) :: rest => bodiesOf rest
  | (false, part) :: rest => part ++ bodiesOf rest

/--
Parts laid out as a struct or a sequence encodes them.

Fixed parts sit in place, variable ones leave an offset behind and follow after.

    fields    u64      list     u8
    encoding  [8 bytes][offset ][1 byte][list body]
-/
def assemble (inline : List Bool) (parts : List Bytes) : Except Err Bytes := do
  let slots := inline.zip parts
  -- The first body starts past the fixed part, so that width is also the first offset.
  let leading := headWidth slots
  -- An offset past what four bytes can name would wrap, so the encoding is refused.
  let total := leading + bodyWidth slots
  if total ≥ 2 ^ (8 * bytesPerOffset) then throw (.offsetOverflow total)
  return headOf leading slots ++ bodiesOf slots

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
def serialize : Desc → Value → Except Err Bytes
  | .bool, .bool b => .ok #[if b then 1 else 0]
  | .uint width, .uint n =>
    if n < 2 ^ (8 * width) then .ok (uintBytes width n) else .error .typeMismatch
  -- A byte array is a sequence of bytes, so it meets the size bound every sequence meets.
  | .byteVector length, .bytes data => do
    if data.size != length then throw (.scope length data.size)
    if data.size ≥ 2 ^ (8 * bytesPerOffset) then throw (.offsetOverflow data.size)
    return data
  | .byteList limit, .bytes data => do
    if data.size > limit then throw (.overLimit limit data.size)
    if data.size ≥ 2 ^ (8 * bytesPerOffset) then throw (.offsetOverflow data.size)
    return data
  -- A fixed bit count needs no closing bit, since the width already gives it.
  | .bitVector length, .bits data =>
    if data.size == length then .ok (packBits data ((length + 7) / 8))
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
    return #[UInt8.ofNat selector] ++ body
  | _, _ => .error .typeMismatch

/-- The encoding of a sequence whose elements all share one type. -/
def serializeSequence (element : Desc) (elements : List Value) : Except Err Bytes := do
  let parts ← serializeEach element elements
  -- Fixed elements need no offset table, since the count follows from the width.
  assemble (parts.map fun _ => element.isFixed) parts

/-- The encoding of a struct, each field read against its own type. -/
def serializeStruct (fields : List Desc) (values : List Value) : Except Err Bytes := do
  let parts ← serializeFields fields values
  assemble (fields.map Desc.isFixed) parts

/-- Each element of a sequence encoded on its own. -/
def serializeEach (element : Desc) : List Value → Except Err (List Bytes)
  | [] => .ok []
  | value :: rest => do
    let head ← serialize element value
    let tail ← serializeEach element rest
    return head :: tail

/-- Each field of a struct encoded on its own, paired with the type it was declared as. -/
def serializeFields : List Desc → List Value → Except Err (List Bytes)
  | [], [] => .ok []
  | field :: fields, value :: values => do
    let head ← serialize field value
    let tail ← serializeFields fields values
    return head :: tail
  -- A struct given a different number of values than it has fields fits no type.
  | _, _ => .error .typeMismatch

end

end EthLib.Consensus.Ssz
