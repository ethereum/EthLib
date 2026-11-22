module

/-!
# JSON fields of a JWT

The grammar is [RFC 8259 §§2 to 7][json], and a step comment names the rule of the grammar.

Strings and numbers keep their values; the reader checks and skips all other JSON values.

[json]: https://www.rfc-editor.org/rfc/rfc8259#section-2
-/

@[expose] public section

namespace EthLib.Engine.Jwt.Json

/-- A JSON number as `mantissa * 10^exponent`, without expanding its exponent. -/
structure Number where
  mantissa : Int
  exponent : Int
  deriving DecidableEq, Repr

/-- The scalar values the JWT profile reads; other JSON values need only syntax validation. -/
inductive Value where
  | str (text : String)
  | num (value : Number)
  | other
  deriving Repr

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
  let read (c : Char) : Option Nat :=
    if digit c then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
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
  -- The fuel starts above the count of characters, and each step reads at least one.
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

/-- Read one JSON value, retaining only the scalar forms the JWT profile uses. -/
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
      let (text, rest) ← string (rest.length + 1) rest
      return (.str text, rest)
    -- An object, §4, `begin-object` with the whitespace after it.
    | '{' :: rest =>
      let (_, rest) ← object n (rest.dropWhile whitespace) [] true
      return (.other, rest)
    -- An array, §5, `begin-array` with the whitespace after it.
    | '[' :: rest =>
      let rest ← array n (rest.dropWhile whitespace) true
      return (.other, rest)
    -- The three literal names, §3, in lowercase.
    | 't' :: 'r' :: 'u' :: 'e' :: rest => return (.other, rest)
    | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => return (.other, rest)
    | 'n' :: 'u' :: 'l' :: 'l' :: rest => return (.other, rest)
    -- Otherwise a number, §6.
    | rest =>
      let (num, rest) ← number rest
      return (.num num, rest)

/-- Read object fields; the last duplicate name wins, as RFC 7515 §4 permits. -/
def object (fuel : Nat) (chars : List Char) (acc : List (String × Value)) (empty : Bool) :
    Option (List (String × Value) × List Char) :=
  match fuel with
  | 0 => none
  | n + 1 => do
    match chars with
    -- RFC 8259 §4: `object = begin-object [ member *( value-separator member ) ] end-object`.
    --
    -- `end-object` here closes an empty object, and fails after a `value-separator`.
    | '}' :: rest => if empty then some (acc, rest) else none
    -- `member = string name-separator value`.
    | '"' :: rest =>
      let (key, rest) ← string (rest.length + 1) rest
      let ':' :: rest := rest.dropWhile whitespace | none
      let (item, rest) ← value n rest
      -- The newest member comes first, so a lookup finds the lexically last of duplicate names.
      --
      -- RFC 7515 §4 and RFC 7519 §4 allow that reading of duplicate names.
      match rest.dropWhile whitespace with
      -- `end-object` after the last member.
      | '}' :: tail => some ((key, item) :: acc, tail)
      -- `value-separator`, then another member.
      | ',' :: tail => object n (tail.dropWhile whitespace) ((key, item) :: acc) false
      | _ => none
    | _ => none

/-- Check the elements and closing bracket of an array. -/
def array (fuel : Nat) (chars : List Char) (empty : Bool) : Option (List Char) :=
  match fuel with
  | 0 => none
  | n + 1 => do
    match chars with
    -- RFC 8259 §5: `array = begin-array [ value *( value-separator value ) ] end-array`.
    --
    -- `end-array` here closes an empty array, and fails after a `value-separator`.
    | ']' :: rest => if empty then some rest else none
    | _ =>
      let (_, rest) ← value n chars
      match rest.dropWhile whitespace with
      -- `end-array` after the last value.
      | ']' :: tail => some tail
      -- `value-separator`, then another value.
      | ',' :: tail => array n (tail.dropWhile whitespace) false
      | _ => none

end

/-- Read one complete JSON object, with no text after it, RFC 8259 §§2 and 4. -/
def fields (text : String) : Option (List (String × Value)) := do
  let chars := text.toList
  -- RFC 8259 §2: `JSON-text = ws value ws`, here with an object as the value.
  let '{' :: rest := chars.dropWhile whitespace | none
  -- The recursion budget comes from the input length, not a fixed nesting limit.
  let (members, rest) ← object (2 * chars.length + 1) (rest.dropWhile whitespace) [] true
  -- Only whitespace follows the object.
  if (rest.dropWhile whitespace).isEmpty then some members else none

/-- Compare a NumericDate with an integral clock, exactly and without expanding a huge exponent. -/
def within (time : Number) (clock : Nat) : Bool :=
  -- Engine authentication, JWT claims: `iat` within +-60 seconds of the current time.
  --
  -- RFC 7519 §2: a NumericDate counts seconds and may be non-integer.
  --
  -- The test is `lo <= t <= hi` for `t = m * 10^e`, exactly.
  let lo := (clock : Int) - 60
  let hi := (clock : Int) + 60
  if time.exponent ≥ 0 then
    if time.mantissa = 0 then decide (lo ≤ 0 ∧ 0 ≤ hi)
    -- With `m` nonzero and `e` above the digit count of `hi`, `|t| >= 10^e > hi >= |lo|`.
    --
    -- So `t` is outside the interval, and `10^e` is never computed.
    else if time.exponent.toNat > (clock + 60).repr.length then false
    else
      let seconds := time.mantissa * (10 ^ time.exponent.toNat : Nat)
      decide (lo ≤ seconds ∧ seconds ≤ hi)
  else
    -- A magnitude below one has floor/ceiling known without constructing the denominator.
    let n := (-time.exponent).toNat
    let (floor, ceiling) := if n > time.mantissa.natAbs.repr.length then
      if time.mantissa = 0 then (0, 0)
      else if time.mantissa > 0 then (0, 1) else (-1, 0)
    else
      let scale : Int := (10 ^ n : Nat)
      let floor := time.mantissa / scale
      (floor, if time.mantissa % scale = 0 then floor else floor + 1)
    -- For integer bounds, `lo <= t <= hi` exactly when `lo <= floor(t)` and `ceil(t) <= hi`.
    decide (lo ≤ floor ∧ ceiling ≤ hi)

end EthLib.Engine.Jwt.Json
