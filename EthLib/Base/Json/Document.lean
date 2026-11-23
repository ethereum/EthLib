module

public import EthLib.Base.Json
public import Lean.Data.Json.Basic

/-!
# JSON documents held as text

A JSON text reads as a Lean JSON document, with the reader of RFC 8259 in this library.

A document prints as a text that reads back, each object with its names in increasing order.

[RFC 8259 §4][object] leaves a repeated name in an object unpredictable, and the reader refuses one.

[object]: https://www.rfc-editor.org/rfc/rfc8259#section-4
-/

@[expose] public section

namespace EthLib.Base.Json

open Lean

/-! ## Reading -/

/-- The largest power of ten that a number may scale its digits by.

[RFC 8259 §9][limits] lets a reader limit the range of numbers.

The power counts after the digits of the fraction, so `0.5e100001` scales by `10^100000`.

So a number has at most 100000 more digits than its text writes.

A negative power costs nothing to hold, so it has no bound.

[limits]: https://www.rfc-editor.org/rfc/rfc8259#section-9
-/
def maxExponent : Nat := 100000

/-- A number as a Lean JSON number, `mantissa * 10^-exponent`.

A Lean JSON number has no positive power of ten, so the digits take it.

A power of ten above the limit is refused, since its digits would grow without bound. -/
def Number.toJsonNumber (number : Number) : Option JsonNumber :=
  match number.exponent with
  -- `m * 10^x` for `x >= 0` is the integer `m * 10^x` itself.
  | .ofNat x => if x ≤ maxExponent then some ⟨number.mantissa * (10 ^ x : Nat), 0⟩ else none
  -- `m * 10^-(x + 1)` is the mantissa `m` with the exponent `x + 1`.
  | .negSucc x => some ⟨number.mantissa, x + 1⟩

mutual

/-- The Lean JSON document of a value, or why there is none. -/
def Value.toJson (value : Value) : Except String Lean.Json :=
  match value with
  | .null => .ok .null
  | .bool b => .ok (.bool b)
  | .num number =>
    match number.toJsonNumber with
    | some number => .ok (.num number)
    | none => .error s!"a number scales by a power of ten above {maxExponent}"
  | .str text => .ok (.str text)
  | .arr items => do return .arr (← itemsToJson items #[])
  | .obj members => do return .obj (← membersToJson members ∅)
termination_by structural value

/-- The Lean JSON documents of the items of an array, after those already read. -/
def itemsToJson (items : List Value) (acc : Array Lean.Json) : Except String (Array Lean.Json) :=
  match items with
  | [] => .ok acc
  | item :: rest => do itemsToJson rest (acc.push (← item.toJson))
termination_by structural items

/-- The members of an object, in the order of the text, inserted after those already read.

A name that comes twice is refused. -/
def membersToJson (members : List (String × Value)) (acc : Std.TreeMap.Raw String Lean.Json) :
    Except String (Std.TreeMap.Raw String Lean.Json) :=
  match members with
  | [] => .ok acc
  | (name, item) :: rest =>
    -- RFC 8259 §4: the names within an object SHOULD be unique.
    if acc.contains name then .error s!"the name {name} appears twice in an object" else do
    membersToJson rest (acc.insert name (← item.toJson))
termination_by structural members

end

/-- The document that a JSON text holds, or why it holds none. -/
def ofText (text : String) : Except String Lean.Json :=
  match read text with
  | some value => value.toJson
  | none => .error "the text is not JSON"

/-! ## Printing -/

/-- A character of a string as the text writes it, RFC 8259 §7. -/
def escape (acc : String) (c : Char) : String :=
  -- RFC 8259 §7: the quotation mark, the reverse solidus and the control characters are escaped.
  if c = '"' then acc ++ "\\\""
  else if c = '\\' then acc ++ "\\\\"
  -- The line feed and the carriage return take their two-character escapes.
  else if c = '\n' then acc ++ "\\n"
  else if c = '\r' then acc ++ "\\r"
  -- Any other control character, U+0000 to U+001F, takes `\u00` and two hex digits.
  else if h : c.toNat < 0x20 then
    acc ++ "\\u00" |>.push (hexDigitChar ⟨c.toNat / 16, by omega⟩)
      |>.push (hexDigitChar ⟨c.toNat % 16, Nat.mod_lt _ (by decide)⟩)
  else acc.push c

/-- A string as the text writes it, between quotation marks, after the text already written. -/
def writeString (text : String) (acc : String) : String :=
  -- A string with no character to escape is copied at once.
  if plainEnd text.startPos = text.endPos then ((acc.push '"') ++ text).push '"'
  else (text.toList.foldl escape (acc.push '"')).push '"'

/-- A number as the text writes it, after the text already written.

The digits of the mantissa come first, then `e-` and the exponent when it is not zero. -/
def writeNumber (number : JsonNumber) (acc : String) : String :=
  -- RFC 8259 §6: `m * 10^-e` is `m`, or `m` then `e-` and the decimal digits of `e`.
  if number.exponent = 0 then acc ++ number.mantissa.repr
  else acc ++ number.mantissa.repr ++ "e-" ++ number.exponent.repr

mutual

/-- A document as the text writes it, after the text already written. -/
def write (document : Lean.Json) (acc : String) : String :=
  match document with
  -- RFC 8259 §3: the three literal names, in lowercase.
  | .null => acc ++ "null"
  | .bool true => acc ++ "true"
  | .bool false => acc ++ "false"
  | .num number => writeNumber number acc
  | .str text => writeString text acc
  -- RFC 8259 §5: an array is its values between brackets, separated by commas.
  | .arr ⟨items⟩ => (writeItems items (acc.push '[') true).push ']'
  -- RFC 8259 §4: an object is its members between braces, separated by commas.
  | .obj ⟨⟨members⟩⟩ => (writeMembers members (acc.push '{') true).1.push '}'
termination_by structural document

/-- The values of an array, each after a comma but the first. -/
def writeItems (items : List Lean.Json) (acc : String) (first : Bool) : String :=
  match items with
  | [] => acc
  | item :: rest => writeItems rest (write item (if first then acc else acc.push ',')) false
termination_by structural items

/-- The members of an object in the order of its tree, each after a comma but the first.

That order is increasing in the names when the tree is well formed.

The flag that comes back says whether no member came yet. -/
def writeMembers (members : Std.DTreeMap.Internal.Impl String fun _ => Lean.Json) (acc : String)
    (first : Bool) : String × Bool :=
  match members with
  | .leaf => (acc, first)
  | .inner _ name item left right =>
    let (acc, first) := writeMembers left acc first
    -- RFC 8259 §4: `member = string name-separator value`.
    let acc := writeString name (if first then acc else acc.push ',')
    writeMembers right (write item (acc.push ':')) false
termination_by structural members

end

/-- The text of a document.

A document whose objects repeat no name reads back from it, rebuilt. -/
def toText (document : Lean.Json) : String :=
  write document ""

end EthLib.Base.Json
