import EthLib.Serialization.Ssz.Codec.Serialize

/-! Turning bytes back into a value, refusing anything a value would not have produced. -/

namespace EthLib.Serialization.Ssz

/-- What one slot of a struct's fixed part holds. -/
inductive Slot where
  /-- The field itself, written in place. -/
  | inline (bytes : Bytes)
  /-- Where the field's body begins, the body following the fixed part. -/
  | body (start : Nat)

/-- The bytes a slot holds in place, a body having none of its own here. -/
def Slot.held : Slot → Bytes
  | .inline bytes => bytes
  | .body _ => #[]


/--
Little-endian bytes read back as an unsigned integer.

The low byte comes first, so each later byte is worth a further factor of 256.
-/
def readUint (data : Bytes) (start : Nat) : (width : Nat) → Nat
  | 0 => 0
  -- Combine the low byte with the remaining digits, each shifted by one base-256 position.
  | width + 1 => (data[start]?.getD 0).toNat + 256 * readUint data (start + 1) width

/-- The offset table at the front of an encoding, one entry per variable-size part. -/
def readOffsets (data : Bytes) (count : Nat) : List Nat :=
  -- Read consecutive four-byte entries without interpreting their body spans yet.
  (List.range count).map fun i => readUint data (i * bytesPerOffset) bytesPerOffset

/-- Bits recovered from packed bytes, the first bit lowest in the first byte. -/
def unpackBits (data : Bytes) (count : Nat) : Array Bool :=
  -- Division by eight selects the byte, and the remainder selects its bit from the low end.
  (Array.range count).map fun i => (data[i / 8]! >>> UInt8.ofNat (i % 8)) &&& 1 == 1

/--
Position of the highest set bit of a byte, counted from the low end.

Zero is returned for an all-zero byte.

The bitlist decoder rejects that case before it looks for a delimiter.
-/
def highestBit (byte : UInt8) : Nat :=
  if (byte >>> UInt8.ofNat 7) &&& 1 == 1 then 7
  else if (byte >>> UInt8.ofNat 6) &&& 1 == 1 then 6
  else if (byte >>> UInt8.ofNat 5) &&& 1 == 1 then 5
  else if (byte >>> UInt8.ofNat 4) &&& 1 == 1 then 4
  else if (byte >>> UInt8.ofNat 3) &&& 1 == 1 then 3
  else if (byte >>> UInt8.ofNat 2) &&& 1 == 1 then 2
  else if (byte >>> UInt8.ofNat 1) &&& 1 == 1 then 1
  else 0

/--
Width of each body, from the table and the budget it closes over.

    offsets       12       17       20
    boundaries    12       17       20       27
    spans         12..17   17..20   20..27

The whole table is settled before any body is read.

A corrupt one is then refused as a table, not as whatever a bad span made of it.
-/
def offsetSpans : List Nat → Nat → Except Err (List Nat)
  | [], _ => .ok []
  -- The final body is closed by the budget rather than by another offset.
  | [start], scope =>
      if scope < start then .error .offsetPastScope else .ok [scope - start]
  -- Every other body ends where the next one begins.
  | start :: next :: rest, scope =>
      if next < start then .error .offsetUnordered
      else do return (next - start) :: (← offsetSpans (next :: rest) scope)

/-- Where each field's bytes sit inside a struct's encoding. -/
def readSlots : List Desc → Bytes → Nat → Except Err (List Slot × Nat)
  | [], _, position => .ok ([], position)
  | field :: fields, data, position =>
    match field.fixedSize with
    | some width => do
      if position + width > data.size then throw .truncated
      let (rest, ending) ← readSlots fields data (position + width)
      return (.inline (data.extract position (position + width)) :: rest, ending)
    | none => do
      if position + bytesPerOffset > data.size then throw .truncated
      let (rest, ending) ← readSlots fields data (position + bytesPerOffset)
      return (.body (readUint data position bytesPerOffset) :: rest, ending)

/-- Where each body begins, in the order the table names them. -/
def bodyStarts : List Slot → List Nat
  | [] => []
  -- Inline fields have no body reference, so only variable-field offsets enter the span table.
  | .inline _ :: rest => bodyStarts rest
  | .body start :: rest => start :: bodyStarts rest

/-- The parts in field order, each body taken from the span its offset opened. -/
def takeSlots (data : Bytes) : List Slot → List Nat → Except Err (List Bytes)
  | [], _ => .ok []
  -- An inline field consumes no body span because its payload is already present.
  | .inline bytes :: rest, spans => do return bytes :: (← takeSlots data rest spans)
  -- A variable field consumes exactly one validated span and extracts those payload bytes.
  | .body start :: rest, span :: spans => do
      return data.extract start (start + span) :: (← takeSlots data rest spans)
  -- A body with no span left means a table shorter than the fields that read it.
  | .body _ :: _, [] => .error .badDeclaration

/--
The budget a struct encoding has to give, settled before any of its fields is read.

Checking it here is what makes a refusal name the input rather than whichever field ran out.
-/
def structBudget (fields : List Desc) (scope : Nat) : Except Err Unit :=
  match Desc.fieldsFixedSize fields with
  -- A struct of fixed width encodes to that width exactly, at every value it holds.
  | some width => if scope != width then .error (.scope width scope) else .ok ()
  -- A fixed part wider than the budget would read bytes belonging to something else.
  | none =>
    let front := Desc.leadingWidth fields
    if scope < front then .error (.scopeTooSmall front scope) else .ok ()

/--
The slots of a struct's fixed part, and where that part ends.

The budget is settled first, so no slot is read past the input.
-/
def structSlots (fields : List Desc) (data : Bytes) : Except Err (List Slot × Nat) := do
  -- A composite encoding faces the same four-byte offset bound as serialization.
  if data.size ≥ 2 ^ (8 * bytesPerOffset) then throw (.offsetOverflow data.size)
  structBudget fields data.size
  readSlots fields data 0

/-- Each field's own bytes, once the offsets in the fixed part are checked against the input. -/
def structBodies (data : Bytes) (slots : List Slot) (leading : Nat) : Except Err (List Bytes) := do
  let offsets := bodyStarts slots
  -- With no bodies, the slots just read are the whole encoding.
  if offsets.isEmpty then
    if data.size != leading then throw (.scope leading data.size)
    return slots.map Slot.held
  -- The first body starts where the slots end; anything else leaves a gap or an overlap.
  if offsets[0]! != leading then throw (.firstOffset leading offsets[0]!)
  -- Validate the complete offset order before extracting any variable payload.
  let spans ← offsetSpans offsets data.size
  takeSlots data slots spans

/--
Each field's own bytes, cut out of a struct encoding.

Fixed fields are read in place, and each variable one is reached through its offset.
-/
def structSlices (fields : List Desc) (data : Bytes) : Except Err (List Bytes) := do
  let (slots, leading) ← structSlots fields data
  structBodies data slots leading

/-- Byte ranges of a fixed-count sequence, with offsets only for variable-size elements. -/
def vectorSlices (element : Desc) (length : Nat) (data : Bytes) :
    Except Err (List Bytes) := do
  if data.size ≥ 2 ^ (8 * bytesPerOffset) then throw (.offsetOverflow data.size)
  match element.fixedSize with
  | some width =>
    let expected := width * length
    if data.size != expected then throw (.scope expected data.size)
    return (List.range length).map fun i => data.extract (i * width) ((i + 1) * width)
  | none =>
    -- The count is declared, so the table's own width is known before it is read.
    let expectedFirst := length * bytesPerOffset
    if data.size < expectedFirst then throw (.scopeTooSmall expectedFirst data.size)
    if length == 0 then return []
    let offsets := readOffsets data length
    if offsets[0]! != expectedFirst then throw (.firstOffset expectedFirst offsets[0]!)
    let spans ← offsetSpans offsets data.size
    return (offsets.zip spans).map fun (start, span) => data.extract start (start + span)

/-- Where each element's bytes sit, for a sequence whose count the encoding carries. -/
def listSlices (element : Desc) (limit : Option Nat) (data : Bytes) :
    Except Err (List Bytes) := do
  if data.size ≥ 2 ^ (8 * bytesPerOffset) then throw (.offsetOverflow data.size)
  let scope := data.size
  if scope == 0 then return []
  match element.fixedSize with
  | some width =>
    -- Elements of no width pack to nothing, so no count of them spends a byte.
    if width == 0 then throw .scopeWidthless
    if scope % width != 0 then throw (.scopeUndivided scope width)
    let count := scope / width
    if let some cap := limit then
      if count > cap then throw (.overLimit cap count)
    return (List.range count).map fun i => data.extract (i * width) ((i + 1) * width)
  | none =>
    -- The first offset is the table's own width, so it gives the count as well as the start.
    if scope < bytesPerOffset then throw (.scopeTooSmall bytesPerOffset scope)
    let first := readUint data 0 bytesPerOffset
    if first < bytesPerOffset then throw .offsetBelowTable
    if first % bytesPerOffset != 0 then throw .offsetUnaligned
    if first > scope then throw .offsetPastScope
    let count := first / bytesPerOffset
    if let some cap := limit then
      if count > cap then throw (.overLimit cap count)
    let offsets := readOffsets data count
    let spans ← offsetSpans offsets scope
    return (offsets.zip spans).map fun (start, span) => data.extract start (start + span)

/--
Bits recovered from a delimited encoding.

The highest set bit closes the sequence, and everything below it is data.

    byte 0 : 0 0 0 0 [1] 1 0 1     the closing bit at position 3
    bits   : 1, 0, 1               three bits of data
-/
def unpackDelimited (limit : Option Nat) (data : Bytes) : Except Err (Array Bool) := do
  -- Even an empty value carries its closing bit, so no encoding is empty.
  if data.size == 0 then throw .emptyEncoding
  let final := data[data.size - 1]!
  -- Trailing zero bytes would give one value a second encoding.
  if final == 0 then
    if data.all (· == 0) then throw .noDelimiter else throw .trailingZeros
  -- Inside the final byte, the closing bit is the highest one set.
  let count := 8 * (data.size - 1) + highestBit final
  if let some cap := limit then
    if count > cap then throw (.overLimit cap count)
  return unpackBits data count

mutual

/-- The value an encoding holds, read against the type it is meant to fit. -/
def deserialize : Desc → Bytes → Except Err Value
  | .bool, data => do
    if data.size != 1 then throw (.scope 1 data.size)
    match data[0]! with
    | 0 => return .bool false
    | 1 => return .bool true
    | byte => throw (.notABit byte.toNat)
  | .uint width, data => do
    if data.size != width then throw (.scope width data.size)
    return .uint (readUint data 0 width)
  -- A byte array is read as a sequence of bytes would be, the size bound first.
  | .byteVector length, data => do
    if data.size ≥ 2 ^ (8 * bytesPerOffset) then throw (.offsetOverflow data.size)
    if data.size != length then throw (.scope length data.size)
    return .bytes data
  | .byteList limit, data => do
    if data.size ≥ 2 ^ (8 * bytesPerOffset) then throw (.offsetOverflow data.size)
    if data.size > limit then throw (.overLimit limit data.size)
    return .bytes data
  | .bitVector length, data => do
    let expected := (length + 7) / 8
    if data.size != expected then throw (.scope expected data.size)
    -- Bits above the last declared one are padding, and a set one is not canonical.
    if length % 8 != 0 && data.size > 0 then
      if data[data.size - 1]! >>> UInt8.ofNat (length % 8) != 0 then throw .paddingBits
    return .bits (unpackBits data length)
  | .bitList limit, data => return .bits (← unpackDelimited (some limit) data)
  | .progressiveBitList limit, data => return .bits (← unpackDelimited limit data)
  | .vector element length, data => do
    let slices ← vectorSlices element length data
    return .seq (← deserializeEach element slices)
  | .list element limit, data => do
    let slices ← listSlices element (some limit) data
    return .seq (← deserializeEach element slices)
  | .progressiveList element limit, data => do
    let slices ← listSlices element limit data
    return .seq (← deserializeEach element slices)
  | .container _ fields, data => return .seq (← deserializeStruct fields data)
  | .progressiveContainer _ _ fields, data => return .seq (← deserializeStruct fields data)
  | .compatibleUnion selectors options, data => do
    if data.size < 1 then throw .noSelector
    deserializeOption selectors options (data[0]!).toNat (data.extract 1 data.size)
termination_by d => (sizeOf d, 0)

/-- Each element of a sequence decoded on its own. -/
def deserializeEach (element : Desc) : List Bytes → Except Err (List Value)
  | [] => .ok []
  | slice :: rest => do
    let head ← deserialize element slice
    let tail ← deserializeEach element rest
    return head :: tail
termination_by slices => (sizeOf element, slices.length + 1)

/--
Each field of a struct, decoded in the order the specification reads them.

    budget        the input against the width of the fixed part
    fixed part    each fixed field, read in place
    table         the offsets, as a whole
    bodies        each variable field, in declaration order

An input breaking several rules is refused for the first one met in that order.
-/
def deserializeStruct (fields : List Desc) (data : Bytes) : Except Err (List Value) := do
  let (slots, leading) ← structSlots fields data
  -- Fixed fields are checked before any offset is trusted.
  -- Without offsets, declaration order is already reading order, so nothing is checked ahead.
  if !(bodyStarts slots).isEmpty then checkInline fields slots
  let slices ← structBodies data slots leading
  -- A fixed field checked above decodes the same way here, so only a body can refuse now.
  deserializeFields fields slices
termination_by (sizeOf fields, 1)

/-- Each field written in place decoded on its own, a field behind an offset skipped. -/
def checkInline : List Desc → List Slot → Except Err Unit
  | [], _ | _ :: _, [] => .ok ()
  | field :: fields, .inline bytes :: slots => do
    let _ ← deserialize field bytes
    checkInline fields slots
  | _ :: fields, .body _ :: slots => checkInline fields slots
termination_by fields => (sizeOf fields, 0)

/-- Each field of a struct decoded on its own, against the type it was declared as. -/
def deserializeFields : List Desc → List Bytes → Except Err (List Value)
  | [], [] => .ok []
  | field :: fields, slice :: slices => do
    let head ← deserialize field slice
    let tail ← deserializeFields fields slices
    return head :: tail
  | _, _ => .error .typeMismatch
termination_by fields => (sizeOf fields, 0)

/--
The value of the option a selector names, under that selector.

The option is searched for here rather than looked up and returned.

What is decoded then stays a part of the union's own type.
-/
def deserializeOption : List Nat → List Desc → Nat → Bytes → Except Err Value
  | [], [], selector, _ => .error (.unknownSelector selector)
  | chosen :: selectors, option :: options, selector, data =>
    if chosen == selector then do
      -- A legal declaration names only selectors in range, so an encoding is held to that range.
      checkSelector selector
      return .union selector (← deserialize option data)
    else deserializeOption selectors options selector data
  -- Selectors and options that do not pair up name no union.
  | _, _, _, _ => .error .badDeclaration
termination_by _ options => (sizeOf options, 0)

end

end EthLib.Serialization.Ssz
