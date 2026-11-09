module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Cryptography.Keystore

/-!
# Exports: ERC-2335 keystores and Unicode NFKD

JSON text is parsed at this boundary, outside the specification's decoder of JSON values.

A linear pass first refuses deep nesting, long digit runs and large positive exponents.

Each could make the parser exhaust its stack, its time or its memory.

The bounds refuse some valid JSON, such as `0.0e10000`, that no keystore writer produces.

The exports return the code and message of the step that failed.
-/

public section

namespace EthLib.Cryptography.Keystore.Exports

open EthLib.Exports (Result PyValue pyExport)

/-- Unicode 16.0.0 Normalization Form KD, UAX #15 rev. 56, §1.3. -/
@[export eth_keystore_nfkd]
def nfkd (args : PyValue) : Result PyValue :=
  pyExport (fun text : String => pure (Base.Unicode.nfkd text)) args

/-- NFKD, control removal and UTF-8 encoding, ERC-2335 "Password requirements". -/
@[export eth_keystore_password]
def password (args : PyValue) : Result PyValue :=
  pyExport (fun text : String => pure (passwordBytes text)) args

/-- The deepest nesting of arrays and objects accepted; a keystore nests four levels. -/
def maxDepth : Nat := 64

/-- The longest run of digits accepted, enough for any 256-bit integer.

The parser takes time quadratic in the length of a run.
-/
def maxDigits : Nat := 80

/-- The largest sum of the positive exponents of all numbers in the text.

The parser multiplies by ten to each such exponent, so the sum bounds the digits it creates.
-/
def maxExponentSum : Nat := 4096

/-- The state of the screen after a prefix of the text. -/
structure Screen where
  /-- Whether the prefix ends inside a string. -/
  inString : Bool := false
  /-- Whether the prefix ends just after a backslash inside a string. -/
  escaped : Bool := false
  /-- The arrays and objects open at the end of the prefix. -/
  depth : Nat := 0
  /-- The last character of the prefix. -/
  previous : Char := ' '
  /-- The length of the run of digits that ends the prefix, outside strings. -/
  digits : Nat := 0
  /-- Inside an exponent: whether it is negative, and its value so far if it is not. -/
  exponent : Option (Bool × Nat) := none
  /-- The sum of the positive exponents so far, including the one in progress. -/
  exponentSum : Nat := 0
  /-- The first reason to refuse the text, if any. -/
  refused : Option String := none

/-- One character outside a string and outside an exponent. -/
def Screen.outside (s : Screen) (c : Char) : Screen :=
  if c = '"' then { s with inString := true }
  else if c = '[' ∨ c = '{' then
    if s.depth + 1 > maxDepth then { s with refused := some "nesting too deep" }
    else { s with depth := s.depth + 1 }
  else if c = ']' ∨ c = '}' then { s with depth := s.depth - 1 }
  else if (c = 'e' ∨ c = 'E') ∧ (s.previous.isDigit ∨ s.previous = '.') then
    { s with exponent := some (false, 0) }
  else s

/-- One character outside a string, inside an exponent, given its sign and value so far. -/
def Screen.inExponent (s : Screen) (c : Char) (negative : Bool) (value : Nat) : Screen :=
  if (c = '+' ∨ c = '-') ∧ (s.previous = 'e' ∨ s.previous = 'E') then
    { s with exponent := some (c = '-', value) }
  else if c.isDigit ∧ !negative then
    let next := 10 * value + (c.toNat - '0'.toNat)
    let sum := s.exponentSum - value + next
    if sum > maxExponentSum then { s with refused := some "exponents too large" }
    else { s with exponent := some (false, next), exponentSum := sum }
  else if c.isDigit then s
  else { s with exponent := none }.outside c

/-- One more character of the text. -/
def Screen.step (s : Screen) (c : Char) : Screen :=
  if s.refused.isSome then s
  else if s.inString then
    if s.escaped then { s with escaped := false, previous := c }
    else { s with escaped := c = '\\', inString := c ≠ '"', previous := c }
  else
    let digits := if c.isDigit then s.digits + 1 else 0
    if digits > maxDigits then { s with refused := some "digit run too long" }
    else
      let s := { s with digits }
      let s := match s.exponent with
        | some (negative, value) => s.inExponent c negative value
        | none => s.outside c
      { s with previous := c }

/-- Refuse text that the parser would take too long on, or expand or recurse into too far. -/
def screen (text : String) : Except String Unit :=
  match (text.foldl Screen.step {}).refused with
  | some reason => .error reason
  | none => .ok ()

/-- Read JSON text at the boundary, then run the specified keystore decryption.

The arguments are the text, the password, and the memory and work limits of key derivation.
-/
def decryptOf (args : String × String × Nat × Nat) : Result ByteArray := do
  let (text, password, memory, work) := args
  let invalid (reason : String) :=
    let error := KeystoreError.invalidJson reason
    (error.code, s!"{repr error}")
  (screen text).mapError invalid
  let value ← (Lean.Json.parse text).mapError invalid
  (Keystore.decrypt ⟨memory, work⟩ value password).mapError fun error =>
    (error.code, s!"{repr error}")

/-- Decrypt an ERC-2335 JSON keystore and return its secret octets. -/
@[export eth_keystore_decrypt]
def decrypt (args : PyValue) : Result PyValue := pyExport decryptOf args

end EthLib.Cryptography.Keystore.Exports
