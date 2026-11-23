module

public import EthLib.Base.Hex

/-!
# JSON text

The grammar is [RFC 8259 §§2 to 7][json], and a step comment names the rule of the grammar.

The reader keeps every value, and a number exactly as its digits write it.

[json]: https://www.rfc-editor.org/rfc/rfc8259#section-2
-/

@[expose] public section

namespace EthLib.Base.Json

/-- A JSON number as `mantissa * 10^exponent`, without expanding its exponent. -/
structure Number where
  mantissa : Int
  exponent : Int
  deriving DecidableEq, Repr

/-- A JSON value, with the members of an object and the items of an array in the order of the text.

An object keeps every member, so a name may appear more than once. -/
inductive Value where
  | null
  | bool (b : Bool)
  | num (value : Number)
  | str (text : String)
  | arr (items : List Value)
  | obj (members : List (String × Value))

/-- The four whitespace characters of RFC 8259 §2. -/
def whitespace (c : Char) : Bool :=
  -- RFC 8259 §2: `ws = *( %x20 / %x09 / %x0A / %x0D )`.
  c = ' ' || c = '\t' || c = '\n' || c = '\r'

/-- The decimal digits of RFC 8259 §6. -/
def digit (c : Char) : Bool :=
  -- RFC 8259 §6: `DIGIT`, the characters `%x30-39`.
  '0' ≤ c && c ≤ '9'

/-- The value of a list of characters already checked as decimal digits. -/
def digitsValue (chars : List Char) : Nat :=
  -- Base 10, most significant digit first: `v := 10 v + d` for each digit `d`.
  chars.foldl (fun acc c => 10 * acc + c.toNat - '0'.toNat) 0

/-- Four hexadecimal digits of a Unicode escape, RFC 8259 §7. -/
def hex4 (chars : List Char) : Option (Nat × List Char) := do
  -- RFC 8259 §7: `4HEXDIG`, whose letters A to F may be uppercase or lowercase.
  let [a, b, c, d] := chars.take 4 | none
  let read (c : Char) : Option Nat := (hexValue? c).map UInt8.toNat
  -- The value of the four digits, `16^3 a + 16^2 b + 16 c + d`.
  return (4096 * (← read a) + 256 * (← read b) + 16 * (← read c) + (← read d), chars.drop 4)

/-- A Unicode escape, combining a surrogate pair and refusing an unpaired surrogate. -/
def unicodeEscape (chars : List Char) : Option (Char × List Char) := do
  -- RFC 8259 §7: `\u` and four hexadecimal digits that encode the code point.
  let (n, rest) ← hex4 chars
  -- §7: a character outside the Basic Multilingual Plane is a UTF-16 surrogate pair.
  --
  -- That is 12 characters: a high surrogate, then `\u` and a low surrogate.
  if 0xd800 ≤ n && n < 0xdc00 then
    let '\\' :: 'u' :: tail := rest | none
    let (low, tail) ← hex4 tail
    if 0xdc00 ≤ low && low < 0xe000 then
      -- The code point is `0x10000 + 1024 (high - 0xD800) + (low - 0xDC00)`.
      return (Char.ofNat (0x10000 + 1024 * (n - 0xd800) + low - 0xdc00), tail)
    -- Not in RFC 8259: its grammar admits an unpaired surrogate, such as `\uDEAD`.
    --
    -- §8.2 leaves the meaning of one unpredictable, and EthLib refuses it, high or low.
    --
    -- A Lean string holds no surrogate code point.
    else none
  else if 0xdc00 ≤ n && n < 0xe000 then none
  -- A character of the Basic Multilingual Plane is its code point.
  else return (Char.ofNat n, rest)

/-- The characters after an opening quote, through the closing quote, RFC 8259 §7. -/
def string (fuel : Nat) (chars : List Char) (acc : List Char := []) :
    Option (String × List Char) :=
  match fuel, chars with
  -- Each step reads at least one character, so the fuel bounds the length of the string.
  | 0, _ => none
  -- RFC 8259 §7: `string = quotation-mark *char quotation-mark`, so a quotation mark ends it.
  | _ + 1, '"' :: rest => some (String.ofList acc.reverse, rest)
  -- `escape %x75 4HEXDIG`: a reverse solidus, `u` and four hexadecimal digits.
  | n + 1, '\\' :: 'u' :: rest => do
    let (c, rest) ← unicodeEscape rest
    string n rest (c :: acc)
  -- The two-character escapes of §7: a reverse solidus, then one of eight characters.
  --
  -- The quotation mark, the reverse solidus and the solidus stand for themselves.
  --
  -- The letters `b`, `f`, `n`, `r` and `t` stand for U+0008, U+000C, U+000A, U+000D and U+0009.
  | n + 1, '\\' :: c :: rest => do
    let decoded ← match c with
      | '"' => some '"' | '\\' => some '\\' | '/' => some '/'
      | 'b' => some '\x08' | 'f' => some '\x0c' | 'n' => some '\n'
      | 'r' => some '\r' | 't' => some '\t' | _ => none
    string n rest (decoded :: acc)
  -- `unescaped = %x20-21 / %x23-5B / %x5D-10FFFF`: the control characters U+0000 to U+001F fail.
  --
  -- The quotation mark and the reverse solidus are read by the cases above.
  | n + 1, c :: rest =>
    if c.toNat < 0x20 then none else string n rest (c :: acc)
  -- A string without its closing quotation mark.
  | _, [] => none

/-- A JSON number and the characters after it, with the grammar of RFC 8259 §6. -/
def number (chars : List Char) : Option (Number × List Char) := do
  -- RFC 8259 §6: `number = [ minus ] int [ frac ] [ exp ]`.
  let (negative, chars) := match chars with
    | '-' :: rest => (true, rest)
    | _ => (false, chars)
  -- `int = zero / ( digit1-9 *DIGIT )`: one digit at least, and a leading zero only in 0 itself.
  let (whole, rest) := chars.span digit
  if whole.isEmpty || (whole.head? = some '0' && whole.length > 1) then none else do
  -- `frac = decimal-point 1*DIGIT`.
  let (fraction, rest) ← match rest with
    | '.' :: tail =>
      let (digits, tail) := tail.span digit
      if digits.isEmpty then none else some (digits, tail)
    | _ => some ([], rest)
  -- `exp = e [ minus / plus ] 1*DIGIT`, with `e = %x65 / %x45`.
  let (exponent, rest) ← match rest with
    | e :: tail =>
      if e = 'e' || e = 'E' then do
        let (minus, tail) := match tail with
          | '-' :: xs => (true, xs)
          | '+' :: xs => (false, xs)
          | _ => (false, tail)
        let (digits, tail) := tail.span digit
        if digits.isEmpty then none else
          let exp := digitsValue digits
          some ((if minus then -(exp : Int) else exp), tail)
      else some (0, rest)
    | [] => some (0, rest)
  -- The value is `m * 10^(x - f)`, for `m` the digits of the integer and the fraction together.
  --
  -- `x` is the exponent and `f` the count of fraction digits, so no precision is lost.
  let value := digitsValue (whole ++ fraction)
  return (⟨if negative then -(value : Int) else value, exponent - fraction.length⟩, rest)

mutual

/-- Read one JSON value and the characters after it. -/
def value (fuel : Nat) (chars : List Char) : Option (Value × List Char) :=
  match fuel with
  | 0 => none
  | n + 1 => do
    -- RFC 8259 §2: whitespace may come before a value.
    match chars.dropWhile whitespace with
    -- §3: `value = false / null / true / object / array / number / string`.
    --
    -- A string, §7.
    | '"' :: rest =>
      let (text, rest) ← string n rest
      return (.str text, rest)
    -- An object, §4, `begin-object` with the whitespace after it.
    | '{' :: rest =>
      let (members, rest) ← object n (rest.dropWhile whitespace) [] true
      return (.obj members, rest)
    -- An array, §5, `begin-array` with the whitespace after it.
    | '[' :: rest =>
      let (items, rest) ← array n (rest.dropWhile whitespace) [] true
      return (.arr items, rest)
    -- The three literal names, §3, in lowercase.
    | 't' :: 'r' :: 'u' :: 'e' :: rest => return (.bool true, rest)
    | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => return (.bool false, rest)
    | 'n' :: 'u' :: 'l' :: 'l' :: rest => return (.null, rest)
    -- Otherwise a number, §6.
    | rest =>
      let (num, rest) ← number rest
      return (.num num, rest)

/-- Read the members and closing brace of an object, the members read so far newest first. -/
def object (fuel : Nat) (chars : List Char) (acc : List (String × Value)) (empty : Bool) :
    Option (List (String × Value) × List Char) :=
  match fuel with
  | 0 => none
  | n + 1 => do
    match chars with
    -- RFC 8259 §4: `object = begin-object [ member *( value-separator member ) ] end-object`.
    --
    -- `end-object` here closes an empty object, and fails after a `value-separator`.
    | '}' :: rest => if empty then some (acc.reverse, rest) else none
    -- `member = string name-separator value`.
    | '"' :: rest =>
      let (key, rest) ← string n rest
      let ':' :: rest := rest.dropWhile whitespace | none
      let (item, rest) ← value n rest
      match rest.dropWhile whitespace with
      -- `end-object` after the last member.
      | '}' :: tail => some (((key, item) :: acc).reverse, tail)
      -- `value-separator`, then another member.
      | ',' :: tail => object n (tail.dropWhile whitespace) ((key, item) :: acc) false
      | _ => none
    | _ => none

/-- Read the items and closing bracket of an array, the items read so far newest first. -/
def array (fuel : Nat) (chars : List Char) (acc : List Value) (empty : Bool) :
    Option (List Value × List Char) :=
  match fuel with
  | 0 => none
  | n + 1 => do
    match chars with
    -- RFC 8259 §5: `array = begin-array [ value *( value-separator value ) ] end-array`.
    --
    -- `end-array` here closes an empty array, and fails after a `value-separator`.
    | ']' :: rest => if empty then some (acc.reverse, rest) else none
    | _ =>
      let (item, rest) ← value n chars
      match rest.dropWhile whitespace with
      -- `end-array` after the last value.
      | ']' :: tail => some ((item :: acc).reverse, tail)
      -- `value-separator`, then another value.
      | ',' :: tail => array n (tail.dropWhile whitespace) (item :: acc) false
      | _ => none

end

/-- Read one complete JSON text, with nothing but whitespace after its value, RFC 8259 §2. -/
def read (text : String) : Option Value := do
  let chars := text.toList
  -- RFC 8259 §2: `JSON-text = ws value ws`.
  --
  -- The recursion budget comes from the input length, not a fixed nesting limit.
  --
  -- It is twice the length plus one: an array spends a step on an item before its separator.
  let (document, rest) ← value (2 * chars.length + 1) chars
  -- Only whitespace follows the value.
  if (rest.dropWhile whitespace).isEmpty then some document else none

end EthLib.Base.Json
