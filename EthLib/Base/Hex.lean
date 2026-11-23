module

/-!
# `Base.Hex`

The sixteen hex digits, as the encodings that write bytes in hex use them.

Decoding reads digits in either letter case, or in lowercase only.

Long inputs do not grow the stack.
-/

@[expose] public section

namespace EthLib.Base

/-- The sixteen hex digits in lowercase, in order of value. -/
def hexAlphabet : Array Char :=
  #['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']

/-- The lowercase hex digit of a value below sixteen. -/
def hexDigitChar (n : Fin 16) : Char :=
  hexAlphabet[n]

/-- The two lowercase hex digits of a byte, high digit first. -/
def byteHexDigits (byte : UInt8) : List Char :=
  [hexDigitChar ⟨byte.toNat / 16, by have := byte.toNat_lt; omega⟩,
    hexDigitChar ⟨byte.toNat % 16, by omega⟩]

/-- Bytes as lowercase hex digits behind `0x`, two digits per byte. -/
def hexString (bytes : List UInt8) : String :=
  bytes.foldl (init := "0x") fun text byte => (byteHexDigits byte).foldl String.push text

/-- A number as lowercase hex digits behind `0x`, padded with zeros to at least `width` digits.

A number with more digits than the width keeps all of them. -/
def hexNat (width value : Nat) : String :=
  let digits := Nat.toDigits 16 value
  "0x" ++ String.ofList (List.replicate (width - digits.length) '0' ++ digits)

/-- The value of one hex digit.

A digit may be in either letter case, or only in lowercase when uppercase is not allowed. -/
def hexValue? (c : Char) (upper : Bool := true) : Option UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
  else if upper ∧ 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
  else none

/-- The bytes so far, then one byte for each pair of digits.

An odd count of digits, or a character that is not a digit, gives nothing. -/
def hexBytesFrom? : List Char → ByteArray → Option ByteArray
  | [], out => some out
  | [_], _ => none
  | high :: low :: rest, out => do
    hexBytesFrom? rest (out.push (16 * (← hexValue? high) + (← hexValue? low)))

/-- The bytes that a run of hex digits holds, with no `0x` marker. -/
def hexBytes? (digits : List Char) : Option ByteArray :=
  hexBytesFrom? digits .empty

end EthLib.Base
