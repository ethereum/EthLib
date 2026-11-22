module

public import EthLib.Serialization.Ssz.Packing
public import EthLib.Serialization.Ssz.Type.Value

/-!
Turning a value into bytes, by the rules of SSZ serialization.

The core rules are stated in EthLib's own terms, one step per comment.

[EIP-7495][eip7495] and [EIP-7916][eip7916] serialize the progressive types as the core ones.

[EIP-8016][eip8016] adds the compatible union.

[eip7495]: https://github.com/ethereum/EIPs/blob/875fcf6d084c096195fec170310514444f537133/EIPS/eip-7495.md#serialization
[eip7916]: https://github.com/ethereum/EIPs/blob/875fcf6d084c096195fec170310514444f537133/EIPS/eip-7916.md#serialization
[eip8016]: https://github.com/ethereum/EIPs/blob/875fcf6d084c096195fec170310514444f537133/EIPS/eip-8016.md#serialization
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/--
Bits packed into bytes, closed by a set bit one past the last of them.

The closing bit is what recovers the count on the way back.

An empty value therefore still takes one byte.
-/
def packBitsDelimited (bits : Array Bool) : Bytes :=
  -- Bitlist: bit `i` is bit `i mod 8` of byte `floor(i / 8)`, and bit `e = |bits|` is set.
  --
  -- That closing bit takes the width to `floor(e / 8) + 1` bytes.
  packBits (bits.push true) ((bits.size + 8) / 8)

/-- The width so far, plus the bytes the fixed part of `parts` occupies.

The loops below carry what they have built so far, so they run in constant stack. -/
def headWidthFrom : List (Bool × Bytes) → Nat → Nat
  | [], width => width
  | (isInline, part) :: rest, width =>
      headWidthFrom rest (width + if isInline then part.size else bytesPerOffset)

/-- Bytes the fixed part occupies, before any body follows it. -/
def headWidth (parts : List (Bool × Bytes)) : Nat :=
  headWidthFrom parts 0

/-- The width so far, plus the bytes the bodies of `parts` occupy. -/
def bodyWidthFrom : List (Bool × Bytes) → Nat → Nat
  | [], width => width
  | (true, _) :: rest, width => bodyWidthFrom rest width
  | (false, part) :: rest, width => bodyWidthFrom rest (width + part.size)

/-- Bytes the bodies occupy, which is every part not written in place. -/
def bodyWidth (parts : List (Bool × Bytes)) : Nat :=
  bodyWidthFrom parts 0

/-- The fixed part so far, then the fixed part of `parts`, whose first body begins at `start`. -/
def headOfFrom : Nat → List (Bool × Bytes) → Bytes → Bytes
  | _, [], out => out
  | start, (true, part) :: rest, out => headOfFrom start rest (out ++ part)
  | start, (false, part) :: rest, out =>
      headOfFrom (start + part.size) rest (out ++ uintBytes bytesPerOffset start)

/--
The fixed part, given where the first body begins.

An inline part sits here in full.

Anything else leaves the offset of its body, and the next body begins past its end.
-/
def headOf (start : Nat) (parts : List (Bool × Bytes)) : Bytes :=
  headOfFrom start parts #[]

/-- The bodies so far, then the bodies of `parts`. -/
def bodiesOfFrom : List (Bool × Bytes) → Bytes → Bytes
  | [], out => out
  | (true, _) :: rest, out => bodiesOfFrom rest out
  | (false, part) :: rest, out => bodiesOfFrom rest (out ++ part)

/-- The bodies, in the order their offsets name them. -/
def bodiesOf (parts : List (Bool × Bytes)) : Bytes :=
  bodiesOfFrom parts #[]

/--
Parts laid out as a struct or a sequence encodes them.

Fixed parts sit in place, variable ones leave an offset behind and follow after.

For the fields uint64, a list and uint8: the uint64 (8 bytes), the offset (4), the uint8 (1).

The body of the list follows them.
-/
def assemble (inline : List Bool) (parts : List Bytes) : Except Err Bytes := do
  -- Each part is paired with its flag, in a loop of constant stack.
  let slots := List.zipWith Prod.mk inline parts
  -- A fixed-size part has its own length, a variable-size one the length of its offset, 4.
  --
  -- The first body starts past the fixed part, so the sum of those lengths is the first offset.
  let leading := headWidth slots
  -- The fixed and the variable lengths sum to less than `2^32`, since an offset has four bytes.
  --
  -- A larger total would wrap an offset, so the encoding is refused.
  let total := leading + bodyWidth slots
  if total ≥ 2 ^ (8 * bytesPerOffset) then throw (.offsetOverflow total)
  -- The offset of the body `i` is the first offset plus the lengths of the bodies before it.
  --
  -- The result is the fixed parts, offsets in place, then the variable parts in order.
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
  -- boolean: the byte `0x01` for true, `0x00` for false.
  | .bool, .bool b => .ok #[if b then 1 else 0]
  -- uintN: `N / 8` bytes, little-endian; the type holds the byte width `N / 8`.
  --
  -- A value of `2^N` or more is refused.
  | .uint width, .uint n =>
    if uintFits width n then .ok (uintBytes width n) else .error .typeMismatch
  -- A byte array is a sequence of bytes, so it meets the size bound every sequence meets.
  --
  -- ByteVector[N]: exactly `N` bytes, written as they are.
  | .byteVector length, .bytes data => do
    if data.size != length then throw (.scope length data.size)
    if data.size ≥ 2 ^ (8 * bytesPerOffset) then throw (.offsetOverflow data.size)
    return data
  -- ByteList[N]: at most `N` bytes, written as they are.
  | .byteList limit, .bytes data => do
    if data.size > limit then throw (.overLimit limit data.size)
    if data.size ≥ 2 ^ (8 * bytesPerOffset) then throw (.offsetOverflow data.size)
    return data
  -- Bitvector[N]: exactly `N` bits, bit `i` in bit `i mod 8` of byte `floor(i / 8)`.
  --
  -- That takes `ceil(N / 8)` bytes, with no closing bit, since the width already gives the count.
  | .bitVector length, .bits data =>
    if data.size == length then .ok (packBits data ((length + 7) / 8))
    else .error (.scope length data.size)
  -- Bitlist[N]: at most `N` bits, then a closing bit, so trailing zero bits are not lost.
  | .bitList limit, .bits data =>
    if data.size ≤ limit then .ok (packBitsDelimited data)
    else .error (.overLimit limit data.size)
  -- EIP-7916: a ProgressiveBitlist serializes as a Bitlist[N].
  --
  -- It has no limit there; the bound is EthLib's, and applies only where a shape declares one.
  | .progressiveBitList limit, .bits data => do
    boundCheck limit data.size
    return packBitsDelimited data
  -- Vector[type, N]: exactly `N` elements, laid out as the parts of a sequence.
  | .vector element length, .seq elements =>
    if elements.length == length then serializeSequence element elements
    else .error (.scope length elements.length)
  -- List[type, N]: at most `N` elements, laid out the same way.
  | .list element limit, .seq elements =>
    if elements.length ≤ limit then serializeSequence element elements
    else .error (.overLimit limit elements.length)
  -- EIP-7916: a ProgressiveList serializes as a List[type, N].
  --
  -- As for the bitlist, its bound is EthLib's, and applies only where a shape declares one.
  | .progressiveList element limit, .seq elements => do
    boundCheck limit elements.length
    serializeSequence element elements
  -- Container: the fields in declaration order, laid out as the parts of a sequence.
  | .container _ fields, .seq values => serializeStruct fields values
  -- EIP-7495: a ProgressiveContainer serializes as a Container.
  --
  -- A gap holds no field, so a struct encodes exactly the fields it declares.
  | .progressiveContainer _ _ fields, .seq values => serializeStruct fields values
  -- EIP-8016: one byte, the selector, then the serialization of the value it selects.
  | .compatibleUnion selectors options, .union selector data => do
    let option ← lookupOption selectors options selector
    -- EIP-8016 makes a union with a selector outside 1 to 127 an illegal type.
    --
    -- The selector is written as one byte, so one the range does not allow is refused, not cut.
    checkSelector selector
    let body ← serialize option data
    return #[UInt8.ofNat selector] ++ body
  | _, _ => .error .typeMismatch

/-- The encoding of a sequence whose elements all share one type. -/
def serializeSequence (element : Desc) (elements : List Value) : Except Err Bytes := do
  -- Each element is serialized on its own, then each is a part of the layout.
  let parts ← serializeEach element elements
  -- Fixed elements need no offset table, since the count follows from the width.
  assemble (parts.map fun _ => element.isFixed) parts

/-- The encoding of a struct, each field read against its own type. -/
def serializeStruct (fields : List Desc) (values : List Value) : Except Err Bytes := do
  -- Each field is serialized against its declared type, which says whether it is fixed-size.
  let parts ← serializeFields fields values
  assemble (fields.map Desc.isFixed) parts

/-- Each element of a sequence encoded on its own. -/
def serializeEach (element : Desc) : List Value → Except Err (List Bytes)
  | [] => .ok []
  | value :: rest => do
    let head ← serialize element value
    serializeEachFrom element rest [head]

/-- The encodings so far, in reverse order, then each element of `values` encoded on its own. -/
def serializeEachFrom (element : Desc) : List Value → List Bytes → Except Err (List Bytes)
  | [], done => .ok done.reverse
  | value :: rest, done => do
    let head ← serialize element value
    serializeEachFrom element rest (head :: done)

/-- Each field of a struct encoded on its own, paired with the type it was declared as. -/
def serializeFields : List Desc → List Value → Except Err (List Bytes)
  | [], [] => .ok []
  | field :: fields, value :: values => do
    let head ← serialize field value
    serializeFieldsFrom fields values [head]
  -- A struct given a different number of values than it has fields fits no type.
  | _, _ => .error .typeMismatch

/-- The encodings so far, in reverse order, then each field encoded on its own. -/
def serializeFieldsFrom : List Desc → List Value → List Bytes → Except Err (List Bytes)
  | [], [], done => .ok done.reverse
  | field :: fields, value :: values, done => do
    let head ← serialize field value
    serializeFieldsFrom fields values (head :: done)
  | _, _, _ => .error .typeMismatch

end

end EthLib.Serialization.Ssz
