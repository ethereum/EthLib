module

public import EthLib.Base.Hex

/-!
# JSON text

The grammar is [RFC 8259 §§2 to 7][json], and a step comment names the rule of the grammar.

The reader keeps every value, and a number exactly as its digits write it.

It reads the text in place, by its positions, and copies each run of plain characters at once.

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
  -- RFC 8259 §6 uses `DIGIT`, the core rule `%x30-39` of RFC 5234, Appendix B.1.
  '0' ≤ c && c ≤ '9'

variable {text : String}

/-- The position after the whitespace that starts at a position, RFC 8259 §2. -/
def skipWhitespace (p : text.Pos) : text.Pos :=
  if h : p = text.endPos then p
  else if whitespace (p.get h) then skipWhitespace (p.next h) else p
termination_by p
decreasing_by exact String.Pos.lt_next

/-- The position after one given character, if that character comes next. -/
def expect (p : text.Pos) (c : Char) : Option text.Pos :=
  if h : p = text.endPos then none else if p.get h = c then some (p.next h) else none

/-- A character that a string holds without an escape, RFC 8259 §7. -/
def plain (c : Char) : Bool :=
  -- `unescaped = %x20-21 / %x23-5B / %x5D-10FFFF`.
  --
  -- So no quotation mark, no reverse solidus and no control character.
  !(c = '"' || c = '\\' || c.toNat < 0x20)

/-- The end of the characters that a string holds without an escape, RFC 8259 §7. -/
def plainEnd (p : text.Pos) : text.Pos :=
  if h : p = text.endPos then p
  else if plain (p.get h) then plainEnd (p.next h) else p
termination_by p
decreasing_by exact String.Pos.lt_next

/-- The value of decimal digits after one more digit, the most significant first.

The character is a decimal digit; for any other character the value means nothing. -/
def digitStep (value : Nat) (c : Char) : Nat :=
  -- Base 10: `v := 10 v + d` for the digit `d`.
  10 * value + c.toNat - '0'.toNat

/-- The decimal digits from a position, read after a value and a count of digits already read.

The result is the value of all the digits, their count and the position after them. -/
def digits (p : text.Pos) (value count : Nat) : Nat × Nat × text.Pos :=
  if h : p = text.endPos then (value, count, p)
  else
    let c := p.get h
    if digit c then digits (p.next h) (digitStep value c) (count + 1) else (value, count, p)
termination_by p
decreasing_by exact String.Pos.lt_next

/-- One hexadecimal digit of a Unicode escape, RFC 8259 §7, in either letter case. -/
def hexDigit (p : text.Pos) : Option (Nat × text.Pos) :=
  if h : p = text.endPos then none
  else (hexValue? (p.get h)).map fun v => (v.toNat, p.next h)

/-- Four hexadecimal digits of a Unicode escape, RFC 8259 §7. -/
def hex4 (p : text.Pos) : Option (Nat × text.Pos) := do
  -- RFC 8259 §7: `4HEXDIG`, with the core rule `HEXDIG` of RFC 5234, Appendix B.1.
  --
  -- §7 lets its letters A to F be uppercase or lowercase.
  let (a, p) ← hexDigit p
  let (b, p) ← hexDigit p
  let (c, p) ← hexDigit p
  let (d, p) ← hexDigit p
  -- The value of the four digits, `16^3 a + 16^2 b + 16 c + d`.
  return (4096 * a + 256 * b + 16 * c + d, p)

/-- A Unicode escape, combining a surrogate pair and refusing an unpaired surrogate. -/
def unicodeEscape (p : text.Pos) : Option (Char × text.Pos) := do
  -- RFC 8259 §7: `\u` and four hexadecimal digits that encode the code point.
  let (n, rest) ← hex4 p
  -- §7: a character outside the Basic Multilingual Plane is a UTF-16 surrogate pair.
  --
  -- That is 12 characters: a high surrogate, then `\u` and a low surrogate.
  if 0xd800 ≤ n && n < 0xdc00 then
    let tail ← expect rest '\\'
    let tail ← expect tail 'u'
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

/-- The character that a two-character escape stands for, RFC 8259 §7. -/
def shortEscape (c : Char) : Option Char :=
  -- The quotation mark, the reverse solidus and the solidus stand for themselves.
  --
  -- The letters `b`, `f`, `n`, `r` and `t` stand for U+0008, U+000C, U+000A, U+000D and U+0009.
  match c with
  | '"' => some '"' | '\\' => some '\\' | '/' => some '/'
  | 'b' => some '\x08' | 'f' => some '\x0c' | 'n' => some '\n'
  | 'r' => some '\r' | 't' => some '\t' | _ => none

/-- The characters after an opening quote, through the closing quote, RFC 8259 §7.

The characters read so far come first in the result. -/
def string (fuel : Nat) (p : text.Pos) (acc : String) : Option (String × text.Pos) :=
  match fuel with
  -- Each step reads a run without an escape, then the closing quote or one escape.
  --
  -- So the fuel bounds the count of escapes, not the length of the string.
  | 0 => none
  | n + 1 =>
    -- The characters without an escape are copied at once.
    let q := plainEnd p
    let piece := text.extract p q
    let acc := if acc.isEmpty then piece else acc ++ piece
    if h : q = text.endPos then none
    else
      let c := q.get h
      let q := q.next h
      -- RFC 8259 §7: `string = quotation-mark *char quotation-mark`, so a quotation mark ends it.
      if c = '"' then some (acc, q)
      -- `char = escape (...)`: a reverse solidus, then `u` and four hex digits.
      --
      -- Or the reverse solidus, then one of eight characters.
      else if c = '\\' then
        if h : q = text.endPos then none
        else if q.get h = 'u' then do
          let (decoded, q) ← unicodeEscape (q.next h)
          string n q (acc.push decoded)
        else do
          let decoded ← shortEscape (q.get h)
          string n (q.next h) (acc.push decoded)
      -- `unescaped` excludes the control characters U+0000 to U+001F, so one fails.
      else none

/-- A JSON number and the position after it, with the grammar of RFC 8259 §6. -/
def number (p : text.Pos) : Option (Number × text.Pos) := do
  -- RFC 8259 §6: `number = [ minus ] int [ frac ] [ exp ]`.
  let (negative, p) := match expect p '-' with
    | some q => (true, q)
    | none => (false, p)
  -- `int = zero / ( digit1-9 *DIGIT )`: one digit at least, and a leading zero only in 0 itself.
  let zero := (expect p '0').isSome
  let (whole, wholeCount, p) := digits p 0 0
  if wholeCount = 0 || (zero && wholeCount > 1) then none else do
  -- `frac = decimal-point 1*DIGIT`.
  --
  -- Its digits continue the value of the integer, so the digits of both make one mantissa.
  let (mantissa, fractionCount, p) ← match expect p '.' with
    | some q =>
      let (value, count, q) := digits q whole 0
      if count = 0 then none else some (value, count, q)
    | none => some (whole, 0, p)
  -- `exp = e [ minus / plus ] 1*DIGIT`, with `e = %x65 / %x45`.
  let marker := match expect p 'e' with
    | some q => some q
    | none => expect p 'E'
  let (exponent, p) ← match marker with
    | some q =>
      let (minus, q) := match expect q '-' with
        | some r => (true, r)
        | none => match expect q '+' with
          | some r => (false, r)
          | none => (false, q)
      let (value, count, q) := digits q 0 0
      if count = 0 then none else some ((if minus then -(value : Int) else value), q)
    | none => some (0, p)
  -- The value is `m * 10^(x - f)`, for `m` the digits of the integer and the fraction together.
  --
  -- `x` is the exponent and `f` the count of fraction digits, so no precision is lost.
  return (⟨if negative then -(mantissa : Int) else mantissa, exponent - fractionCount⟩, p)

mutual

/-- Read one JSON value and the position after it. -/
def value (fuel : Nat) (p : text.Pos) : Option (Value × text.Pos) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    -- RFC 8259 §2: whitespace may come before a value.
    let p := skipWhitespace p
    if h : p = text.endPos then none
    else
      let c := p.get h
      let q := p.next h
      -- §3: `value = false / null / true / object / array / number / string`.
      --
      -- A string, §7.
      if c = '"' then do
        let (content, q) ← string n q ""
        return (.str content, q)
      -- An object, §4, `begin-object` with the whitespace after it.
      else if c = '{' then do
        let (members, q) ← object n (skipWhitespace q) [] true
        return (.obj members, q)
      -- An array, §5, `begin-array` with the whitespace after it.
      else if c = '[' then do
        let (items, q) ← array n (skipWhitespace q) [] true
        return (.arr items, q)
      -- The three literal names, §3, in lowercase.
      else if c = 't' then do
        let q ← expect (← expect (← expect q 'r') 'u') 'e'
        return (.bool true, q)
      else if c = 'f' then do
        let q ← expect (← expect (← expect (← expect q 'a') 'l') 's') 'e'
        return (.bool false, q)
      else if c = 'n' then do
        let q ← expect (← expect (← expect q 'u') 'l') 'l'
        return (.null, q)
      -- Otherwise a number, §6.
      else do
        let (num, q) ← number p
        return (.num num, q)

/-- Read the members and closing brace of an object, the members read so far newest first. -/
def object (fuel : Nat) (p : text.Pos) (acc : List (String × Value)) (empty : Bool) :
    Option (List (String × Value) × text.Pos) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    if h : p = text.endPos then none
    else
      let c := p.get h
      let q := p.next h
      -- RFC 8259 §4: `object = begin-object [ member *( value-separator member ) ] end-object`.
      --
      -- `end-object` here closes an empty object, and fails after a `value-separator`.
      if c = '}' then if empty then some (acc.reverse, q) else none
      -- `member = string name-separator value`.
      else if c = '"' then do
        let (key, q) ← string n q ""
        let q ← expect (skipWhitespace q) ':'
        let (item, q) ← value n q
        let q := skipWhitespace q
        if h : q = text.endPos then none
        else
          let c := q.get h
          -- `end-object` after the last member.
          if c = '}' then some (((key, item) :: acc).reverse, q.next h)
          -- `value-separator`, then another member.
          else if c = ',' then object n (skipWhitespace (q.next h)) ((key, item) :: acc) false
          else none
      else none

/-- Read the items and closing bracket of an array, the items read so far newest first. -/
def array (fuel : Nat) (p : text.Pos) (acc : List Value) (empty : Bool) :
    Option (List Value × text.Pos) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    if h : p = text.endPos then none
    -- RFC 8259 §5: `array = begin-array [ value *( value-separator value ) ] end-array`.
    --
    -- `end-array` here closes an empty array, and fails after a `value-separator`.
    else if p.get h = ']' then if empty then some (acc.reverse, p.next h) else none
    else do
      let (item, q) ← value n p
      let q := skipWhitespace q
      if h : q = text.endPos then none
      else
        let c := q.get h
        -- `end-array` after the last value.
        if c = ']' then some ((item :: acc).reverse, q.next h)
        -- `value-separator`, then another value.
        else if c = ',' then array n (skipWhitespace (q.next h)) (item :: acc) false
        else none

end

/-- Read one complete JSON text, with nothing but whitespace after its value, RFC 8259 §2. -/
def read (text : String) : Option Value := do
  -- RFC 8259 §2: `JSON-text = ws value ws`.
  --
  -- The recursion budget comes from the input length, not a fixed nesting limit.
  --
  -- It is twice the length plus one: an opening bracket or brace spends two steps on one character.
  let (document, rest) ← value (2 * text.length + 1) text.startPos
  -- Only whitespace follows the value.
  if skipWhitespace rest = text.endPos then some document else none

end EthLib.Base.Json
