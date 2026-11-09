module

/-!
# JSON fields of a JWT

The grammar is [RFC 8259 §§2 to 7][json].

Strings and numbers keep their values; the reader checks and skips all other JSON values.

The recursion budget comes from the input length, not a fixed nesting limit.

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
def whitespace (c : Char) : Bool := c = ' ' || c = '\t' || c = '\n' || c = '\r'

/-- The decimal digits of RFC 8259 §6. -/
def digit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- The value of a list of characters already checked as decimal digits. -/
def digitsValue (chars : List Char) : Nat :=
  chars.foldl (fun acc c => 10 * acc + c.toNat - '0'.toNat) 0

/-- Four hexadecimal digits of a Unicode escape, RFC 8259 §7. -/
def hex4 (chars : List Char) : Option (Nat × List Char) := do
  let [a, b, c, d] := chars.take 4 | none
  let read (c : Char) : Option Nat :=
    if digit c then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  return (4096 * (← read a) + 256 * (← read b) + 16 * (← read c) + (← read d), chars.drop 4)

/-- A Unicode escape, combining a surrogate pair and refusing an unpaired surrogate. -/
def unicodeEscape (chars : List Char) : Option (Char × List Char) := do
  let (n, rest) ← hex4 chars
  if 0xd800 ≤ n && n < 0xdc00 then
    let '\\' :: 'u' :: tail := rest | none
    let (low, tail) ← hex4 tail
    if 0xdc00 ≤ low && low < 0xe000 then
      return (Char.ofNat (0x10000 + 1024 * (n - 0xd800) + low - 0xdc00), tail)
    else none
  else if 0xdc00 ≤ n && n < 0xe000 then none
  else return (Char.ofNat n, rest)

/-- The characters after an opening quote, through the closing quote, RFC 8259 §7. -/
def string (fuel : Nat) (chars : List Char) (acc : List Char := []) :
    Option (String × List Char) :=
  match fuel, chars with
  | 0, _ => none
  | _ + 1, '"' :: rest => some (String.ofList acc.reverse, rest)
  | n + 1, '\\' :: 'u' :: rest => do
    let (c, rest) ← unicodeEscape rest
    string n rest (c :: acc)
  | n + 1, '\\' :: c :: rest => do
    let decoded ← match c with
      | '"' => some '"' | '\\' => some '\\' | '/' => some '/'
      | 'b' => some '\x08' | 'f' => some '\x0c' | 'n' => some '\n'
      | 'r' => some '\r' | 't' => some '\t' | _ => none
    string n rest (decoded :: acc)
  | n + 1, c :: rest =>
    if c.toNat < 0x20 then none else string n rest (c :: acc)
  | _, [] => none

/-- A JSON number and the characters after it, with the grammar of RFC 8259 §6. -/
def number (chars : List Char) : Option (Number × List Char) := do
  let (negative, chars) := match chars with
    | '-' :: rest => (true, rest)
    | _ => (false, chars)
  let (whole, rest) := chars.span digit
  if whole.isEmpty || (whole.head? = some '0' && whole.length > 1) then none else do
  let (fraction, rest) ← match rest with
    | '.' :: tail =>
      let (digits, tail) := tail.span digit
      if digits.isEmpty then none else some (digits, tail)
    | _ => some ([], rest)
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
  let value := digitsValue (whole ++ fraction)
  return (⟨if negative then -(value : Int) else value, exponent - fraction.length⟩, rest)

mutual

/-- Read one JSON value, retaining only the scalar forms the JWT profile uses. -/
def value (fuel : Nat) (chars : List Char) : Option (Value × List Char) :=
  match fuel with
  | 0 => none
  | n + 1 => do
    match chars.dropWhile whitespace with
    | '"' :: rest =>
      let (text, rest) ← string (rest.length + 1) rest
      return (.str text, rest)
    | '{' :: rest =>
      let (_, rest) ← object n (rest.dropWhile whitespace) [] true
      return (.other, rest)
    | '[' :: rest =>
      let rest ← array n (rest.dropWhile whitespace) true
      return (.other, rest)
    | 't' :: 'r' :: 'u' :: 'e' :: rest => return (.other, rest)
    | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => return (.other, rest)
    | 'n' :: 'u' :: 'l' :: 'l' :: rest => return (.other, rest)
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
    | '}' :: rest => if empty then some (acc, rest) else none
    | '"' :: rest =>
      let (key, rest) ← string (rest.length + 1) rest
      let ':' :: rest := rest.dropWhile whitespace | none
      let (item, rest) ← value n rest
      match rest.dropWhile whitespace with
      | '}' :: tail => some ((key, item) :: acc, tail)
      | ',' :: tail => object n (tail.dropWhile whitespace) ((key, item) :: acc) false
      | _ => none
    | _ => none

/-- Check the elements and closing bracket of an array. -/
def array (fuel : Nat) (chars : List Char) (empty : Bool) : Option (List Char) :=
  match fuel with
  | 0 => none
  | n + 1 => do
    match chars with
    | ']' :: rest => if empty then some rest else none
    | _ =>
      let (_, rest) ← value n chars
      match rest.dropWhile whitespace with
      | ']' :: tail => some tail
      | ',' :: tail => array n (tail.dropWhile whitespace) false
      | _ => none

end

/-- Read one complete JSON object, with no text after it, RFC 8259 §§2 and 4. -/
def fields (text : String) : Option (List (String × Value)) := do
  let chars := text.toList
  let '{' :: rest := chars.dropWhile whitespace | none
  let (members, rest) ← object (2 * chars.length + 1) (rest.dropWhile whitespace) [] true
  if (rest.dropWhile whitespace).isEmpty then some members else none

/-- Compare a NumericDate with an integral clock, exactly and without expanding a huge exponent. -/
def within (time : Number) (clock : Nat) : Bool :=
  let lo := (clock : Int) - 60
  let hi := (clock : Int) + 60
  if time.exponent ≥ 0 then
    if time.mantissa = 0 then decide (lo ≤ 0 ∧ 0 ≤ hi)
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
    decide (lo ≤ floor ∧ ceiling ≤ hi)

end EthLib.Engine.Jwt.Json
