module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Cryptography.Keystore

/-!
# Exports: ERC-2335 keystores and Unicode NFKD

JSON text is parsed at this boundary, outside the specification's decoder of JSON values.

A screen runs first, so that no text can make the parser exhaust memory or stack.

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

/-- The most significant digits of a positive exponent accepted, so a number stays small.

The parser multiplies by ten to the exponent, so `1e1000000000` alone would need gigabytes.
-/
def maxExponentDigits : Nat := 4

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
  /-- Inside an exponent: whether it is negative, and its significant digits so far. -/
  exponent : Option (Bool × Nat) := none
  /-- The first reason to refuse the text, if any. -/
  refused : Option String := none

/-- One character outside a string and outside an exponent. -/
def Screen.outside (s : Screen) (c : Char) : Screen :=
  let s := { s with previous := c }
  if c = '"' then { s with inString := true }
  else if c = '[' ∨ c = '{' then
    if s.depth + 1 > maxDepth then { s with refused := some "nesting too deep" }
    else { s with depth := s.depth + 1 }
  else if c = ']' ∨ c = '}' then { s with depth := s.depth - 1 }
  else s

/-- One more character of the text. -/
def Screen.step (s : Screen) (c : Char) : Screen :=
  if s.refused.isSome then s
  else if s.inString then
    if s.escaped then { s with escaped := false, previous := c }
    else { s with escaped := c = '\\', inString := c ≠ '"', previous := c }
  else match s.exponent with
    | some (negative, digits) =>
      if (c = '+' ∨ c = '-') ∧ (s.previous = 'e' ∨ s.previous = 'E') then
        { s with exponent := some (c = '-', digits), previous := c }
      else if c.isDigit then
        -- Leading zeros do not change the exponent.
        let digits := if c = '0' ∧ digits = 0 then 0 else digits + 1
        if !negative ∧ digits > maxExponentDigits then
          { s with refused := some "exponent too large" }
        else { s with exponent := some (negative, digits), previous := c }
      else { s with exponent := none }.outside c
    | none =>
      if (c = 'e' ∨ c = 'E') ∧ (s.previous.isDigit ∨ s.previous = '.') then
        { s with exponent := some (false, 0), previous := c }
      else s.outside c

/-- Refuse text that the parser would expand into a huge number or recurse into too deeply. -/
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
