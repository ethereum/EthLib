import Lean.Data.Json
import EthLib.Serialization.Ssz.Codec.Deserialize

/-! The JSON document a value is written as, which an SSZ schema defines alongside its bytes. -/

namespace EthLib.Serialization.Ssz

open Lean

/--
Where a declaration spells a one-byte unsigned integer as the byte alias.

SSZ gives the alias and the one-byte integer the same type, and the JSON mapping does not:
the alias is written as hex, and the integer as decimal digits in a string.

A spelling travels beside a declaration and holds one node for each node of it.

    declaration        spelling            document
    Uint8              plain []            "255"
    Byte               byte                "0xff"
    Vector[Uint8, 2]   plain [plain []]    ["1", "2"]
    Vector[Byte, 2]    plain [byte]        "0x0102"
-/
inductive Spelling where
  /-- The byte alias, written as hex where a plain integer is written as digits. -/
  | byte
  /-- Anything else, with one spelling for each declaration the shape holds. -/
  | plain (parts : List Spelling)
  deriving Inhabited

/-- The spelling to use where none was recorded, which marks no alias anywhere. -/
def Spelling.opaque : Spelling := .plain []

/-- The spelling recorded for the declaration at one position. -/
def Spelling.part : Spelling → Nat → Spelling
  | .plain parts, position => parts.getD position .opaque
  | .byte, _ => .opaque

/-- Whether a one-byte integer here is the byte alias. -/
def Spelling.isByte : Spelling → Bool
  | .byte => true
  | .plain _ => false

/-- The sixteen hex digits, in the lowercase the mapping uses. -/
def hexAlphabet : Array Char :=
  #['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']

/-- Bytes as the mapping writes them: lowercase hex behind a two-character marker. -/
def toHex (data : Bytes) : String :=
  data.foldl (init := "0x") fun text byte =>
    (text.push hexAlphabet[byte.toNat >>> 4]!).push hexAlphabet[byte.toNat &&& 0xF]!

/-- The value of one hex digit, in either letter case. -/
def hexDigit (character : Char) : Except Err Nat :=
  if '0' ≤ character && character ≤ '9' then .ok (character.toNat - '0'.toNat)
  else if 'a' ≤ character && character ≤ 'f' then .ok (character.toNat - 'a'.toNat + 10)
  else if 'A' ≤ character && character ≤ 'F' then .ok (character.toNat - 'A'.toNat + 10)
  else .error .hexDigits

/-- Two digits at a time, folded into the byte each pair holds. -/
def hexBytes : List Char → Except Err Bytes
  | [] => .ok #[]
  | [_] => .error .hexDigits
  | high :: low :: rest => do
    let byte := 16 * (← hexDigit high) + (← hexDigit low)
    return #[UInt8.ofNat byte] ++ (← hexBytes rest)

/--
The bytes a hex string holds.

Every hex string the mapping writes carries the marker, so one without it is refused.
-/
def ofHex (text : String) : Except Err Bytes := do
  let characters := text.toList
  if characters.take 2 != ['0', 'x'] then throw .hexPrefix
  hexBytes (characters.drop 2)

/-- The bytes a run of one-byte integer values holds, in order. -/
def byteRun : List Value → Except Err Bytes
  | [] => .ok #[]
  | .uint n :: rest => do
    if n ≥ 256 then throw (.uintRange 256 n)
    return #[UInt8.ofNat n] ++ (← byteRun rest)
  | _ => .error .typeMismatch

/-- One-byte integer values for a run of bytes, which reads a byte-alias sequence back. -/
def byteElements (data : Bytes) : List Value :=
  data.toList.map fun byte => .uint byte.toNat

/-- Digits in a string, which is how the mapping writes an integer. -/
def decimal (n : Nat) : Json := .str (toString n)

/--
The number a document holds.

An integer is digits in a string, so a wide one survives a parser using doubles.

Only the digits the mapping writes are read back, with no sign, padding or separator.
Writing the number again and comparing is what checks that.

A bare number is accepted as well.
-/
def readNat (document : Json) : Except Err Nat :=
  match document with
  | .str text =>
    let n := Nat.ofDigitChars 10 text.toList 0
    if toString n == text then .ok n else .error .typeMismatch
  | .num value =>
    if value.exponent == 0 && value.mantissa ≥ 0 then .ok value.mantissa.toNat
    else .error .typeMismatch
  | _ => .error .typeMismatch

/--
The hex a collection is written as.

A bitfield and a byte sequence are each written as a single hex string.

An array in that place holds elements of the wrong kind for the collection.
-/
def collectionHex (document : Json) : Except Err String :=
  match document with
  | .str text => .ok text
  | .arr _ => .error .elementKind
  | _ => .error .typeMismatch

/-- The bits a bitfield document holds, read out of the encoding it is written as. -/
def readBitfield (shape : Desc) (document : Json) : Except Err Value := do
  let data ← ofHex (← collectionHex document)
  -- A bitfield's hex is its own encoding, so the codec reads it back under the mapping's names.
  match deserialize shape data with
  | .ok value => return value
  | .error .paddingBits => throw .bitfieldPadding
  | .error .noDelimiter => throw .bitfieldDelimiter
  | .error .trailingZeros => throw .bitfieldTrailingZeros
  | .error (.overLimit limit actual) => throw (.documentOverLimit limit actual)
  | .error fault => throw fault

/-- The field names an object carries. -/
def objectNames (document : Json) : List String :=
  match document with
  | .obj fields => fields.toList.map fun (name, _) => name
  | _ => []

mutual

/--
The JSON document a value is written as.

The declaration fixes the shape of the document.

The spelling decides how a byte is written.
-/
def jsonOf (shape : Desc) (spelling : Spelling) (value : Value) : Except Err Json :=
  match shape, value with
  | .bool, .bool b => .ok (.bool b)
  | .uint width, .uint n =>
    if n ≥ 2 ^ (8 * width) then .error (.uintRange (2 ^ (8 * width)) n)
    -- The alias is a one-byte integer, so no wider integer is written as hex.
    else if spelling.isByte && width == 1 then .ok (.str (toHex #[UInt8.ofNat n]))
    else .ok (decimal n)
  -- A value the type does not admit is refused with the fault its encoding draws.
  | .byteVector length, .bytes data =>
    if data.size == length then .ok (.str (toHex data)) else .error (.scope length data.size)
  | .byteList limit, .bytes data =>
    if data.size ≤ limit then .ok (.str (toHex data)) else .error (.overLimit limit data.size)
  | .bitVector _, .bits _ | .bitList _, .bits _ | .progressiveBitList _, .bits _ => do
    return .str (toHex (← serialize shape value))
  | .vector element length, .seq elements =>
    if elements.length == length then jsonOfSequence element (spelling.part 0) elements
    else .error (.scope length elements.length)
  | .list element limit, .seq elements =>
    if elements.length ≤ limit then jsonOfSequence element (spelling.part 0) elements
    else .error (.overLimit limit elements.length)
  | .progressiveList element limit, .seq elements => do
    boundCheck limit elements.length
    jsonOfSequence element (spelling.part 0) elements
  | .container names fields, .seq values | .progressiveContainer _ names fields, .seq values => do
    return .mkObj (names.zip (← jsonOfFields fields spelling 0 values))
  | .compatibleUnion selectors options, .union selector data => do
    let option ← lookupOption selectors options selector
    let position := (selectors.findIdx? (· == selector)).getD 0
    return .mkObj [("selector", decimal selector),
      ("data", ← jsonOf option (spelling.part position) data)]
  | _, _ => .error .typeMismatch
termination_by (sizeOf value, 2)

/-- The document a sequence is written as, which the byte alias collapses into one hex string. -/
def jsonOfSequence (element : Desc) (spelling : Spelling) (elements : List Value) :
    Except Err Json := do
  if spelling.isByte then return .str (toHex (← byteRun elements))
  return .arr (← jsonOfEach element spelling elements).toArray
termination_by (sizeOf elements, 1)

/-- Each element of a sequence written on its own, against the one type they share. -/
def jsonOfEach (element : Desc) (spelling : Spelling) : List Value → Except Err (List Json)
  | [] => .ok []
  | value :: rest => do
    let head ← jsonOf element spelling value
    let tail ← jsonOfEach element spelling rest
    return head :: tail
termination_by values => (sizeOf values, 0)

/-- Each field of a struct written on its own, under the spelling recorded at its position. -/
def jsonOfFields : List Desc → Spelling → Nat → List Value → Except Err (List Json)
  | [], _, _, [] => .ok []
  | field :: fields, spelling, position, value :: values => do
    let head ← jsonOf field (spelling.part position) value
    let tail ← jsonOfFields fields spelling (position + 1) values
    return head :: tail
  | _, _, _, _ => .error .typeMismatch
termination_by _ _ _ values => (sizeOf values, 1)

end

mutual

/--
The value a document holds, read against the declaration it is written under.

Every refusal here names the mapping rather than the machinery that caught it.
-/
def valueOf (shape : Desc) (spelling : Spelling) (document : Json) : Except Err Value :=
  match shape with
  | .bool => match document with
    | .bool b => .ok (.bool b)
    | _ => .error .typeMismatch
  | .uint width => do
    if spelling.isByte && width == 1 then
      let .str text := document | throw .typeMismatch
      let data ← ofHex text
      if data.size != 1 then throw (.hexLength 1 data.size)
      return .uint data[0]!.toNat
    let n ← readNat document
    if n ≥ 2 ^ (8 * width) then throw (.uintRange (2 ^ (8 * width)) n)
    return .uint n
  | .byteVector length => do
    let data ← ofHex (← collectionHex document)
    if data.size != length then throw (.hexLength length data.size)
    return .bytes data
  | .byteList limit => do
    let data ← ofHex (← collectionHex document)
    if data.size > limit then throw (.documentOverLimit limit data.size)
    return .bytes data
  | .bitVector _ | .bitList _ | .progressiveBitList _ => readBitfield shape document
  | .vector element length => do
    let elements ← valueOfSequence element (spelling.part 0) document
    if elements.length != length then throw (.count length elements.length)
    return .seq elements
  | .list element limit => do
    let elements ← valueOfSequence element (spelling.part 0) document
    if elements.length > limit then throw (.documentOverLimit limit elements.length)
    return .seq elements
  | .progressiveList element limit => do
    let elements ← valueOfSequence element (spelling.part 0) document
    if let some bound := limit then
      if elements.length > bound then throw (.documentOverLimit bound elements.length)
    return .seq elements
  | .container names fields | .progressiveContainer _ names fields => do
    let .obj _ := document | throw .structNotAnObject
    -- The specification permits ignoring an undeclared field; this refuses one instead.
    if let some extra := (objectNames document).find? fun name => !names.contains name then
      throw (.undeclaredField extra)
    return .seq (← valueOfFields fields names spelling 0 document)
  | .compatibleUnion selectors options => do
    let .obj _ := document | throw .structNotAnObject
    -- An empty object asks for a default, and no option of a union stands above the others.
    if (objectNames document).isEmpty then throw .noDefault
    -- A union is written as two fields, and any other one is refused as for a struct.
    if let some extra := (objectNames document).find? fun name => name != "selector" && name != "data" then
      throw (.undeclaredField extra)
    let some selectorField := (document.getObjVal? "selector").toOption
      | throw (.missingField "selector")
    let some payload := (document.getObjVal? "data").toOption | throw (.missingField "data")
    valueOfOption selectors options spelling 0 (← readNat selectorField) payload
termination_by (sizeOf shape, 0, 0)

/-- The elements a sequence document holds, which the byte alias writes as one hex string. -/
def valueOfSequence (element : Desc) (spelling : Spelling) (document : Json) :
    Except Err (List Value) := do
  if spelling.isByte then
    return byteElements (← ofHex (← collectionHex document))
  let .arr entries := document | throw .typeMismatch
  valueOfEntries element spelling entries.toList
termination_by (sizeOf element, 2, 0)

/-- Each entry of a sequence document read on its own, against the one type they share. -/
def valueOfEntries (element : Desc) (spelling : Spelling) : List Json → Except Err (List Value)
  | [] => .ok []
  | entry :: rest => do
    let head ← valueOf element spelling entry
    let tail ← valueOfEntries element spelling rest
    return head :: tail
termination_by entries => (sizeOf element, 1, entries.length)

/-- Each field of a struct read out of the object, under the name it was declared with. -/
def valueOfFields : List Desc → List String → Spelling → Nat → Json → Except Err (List Value)
  | [], _, _, _, _ => .ok []
  | field :: fields, names, spelling, position, document => do
    let name := names.getD position ""
    let some part := (document.getObjVal? name).toOption | throw (.missingField name)
    let head ← valueOf field (spelling.part position) part
    let tail ← valueOfFields fields names spelling (position + 1) document
    return head :: tail
termination_by fields => (sizeOf fields, 0, 0)

/--
The value of the option a selector names, under that selector.

The option is searched for here rather than looked up and returned.

What is read then stays a part of the union's own declaration.
-/
def valueOfOption : List Nat → List Desc → Spelling → Nat → Nat → Json → Except Err Value
  | [], [], _, _, selector, _ => .error (.undeclaredSelector selector)
  | chosen :: selectors, option :: options, spelling, position, selector, payload =>
    if chosen == selector then do
      return .union selector (← valueOf option (spelling.part position) payload)
    else valueOfOption selectors options spelling (position + 1) selector payload
  -- Selectors and options that do not pair up name no union.
  | _, _, _, _, _, _ => .error .badDeclaration
termination_by _ options => (sizeOf options, 0, 0)

end

end EthLib.Serialization.Ssz
