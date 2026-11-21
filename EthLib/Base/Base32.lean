module

public import EthLib.Base.BigEndian

/-!
# `Base.Base32`

The base32 of RFC 4648, without padding.

The alphabet is Table 3 of [RFC 4648 §6](https://www.rfc-editor.org/rfc/rfc4648#section-6).

The values 0 to 25 are `A` to `Z`, and 26 to 31 are `2` to `7`.

Each group of five bytes, 40 bits, becomes eight characters of five bits each.

A last group of one to four bytes becomes two, four, five or seven characters.

Its unused low bits are zero.

The decoder accepts only what the encoder writes, so every byte string has exactly one text.

It rejects the padding character `=` and the lowercase letters, which are not in the alphabet.

It also rejects a last character whose unused bits are not zero, as RFC 4648 §3.5 allows.
-/

@[expose] public section

namespace EthLib.Base.Base32

/-- Why the base32 decoder refused its input.

A position counts the characters of the text from 0. -/
inductive Base32Error where
  /-- The character `c` at `position` is outside the alphabet. -/
  | invalidChar (position : Nat) (c : Char)
  /-- A text of `length` characters, whose last group of 1, 3 or 6 characters holds no bytes. -/
  | invalidLength (length : Nat)
  /-- The last group, which ends at `position`, has unused low bits that are not zero. -/
  | nonZeroPadBits (position : Nat)
  deriving Repr, DecidableEq

/-- The character of a five-bit value, from Table 3 of RFC 4648 §6. -/
def encodeQuint (v : Nat) : Char :=
  if v < 26 then Char.ofNat (65 + v) else Char.ofNat (50 + (v - 26))

/-- The five-bit value of a character of the alphabet, or `none` for any other character. -/
def decodeQuint (c : Char) : Option Nat :=
  if 65 ≤ c.toNat ∧ c.toNat < 91 then some (c.toNat - 65)
  else if 50 ≤ c.toNat ∧ c.toNat < 56 then some (c.toNat - 50 + 26)
  else none

/-- The `count` characters of a number below `32 ^ count`, the first one the highest. -/
def digits : Nat → Nat → List Char
  | 0, _ => []
  | count + 1, n => encodeQuint (n / 32 ^ count % 32) :: digits count n

/-- The number of characters of a group of `size` bytes: its bits, five at a time, rounded up. -/
def charCount (size : Nat) : Nat := (8 * size + 4) / 5

/-- The characters of a group of at most five bytes.

Its bits come first, then zero bits up to a whole number of characters. -/
def encodeGroup (group : List UInt8) : List Char :=
  let count := charCount group.length
  digits count (bytesToNat group * 2 ^ (5 * count - 8 * group.length))

/-- The characters of a byte string, five bytes at a time. -/
def encodeList : List UInt8 → List Char
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => encodeGroup [b0, b1, b2, b3, b4] ++ encodeList rest
  | group => encodeGroup group

/-- The number that a list of characters writes after `acc`, the first character the highest.

The first character is at position `start` of the text. -/
def value (start acc : Nat) : List Char → Except Base32Error Nat
  | [] => return acc
  | c :: rest => do
    let some v := decodeQuint c | throw (.invalidChar start c)
    value (start + 1) (acc * 32 + v) rest

/-- The number of bytes of a group of `count` characters, if a group can have that many. -/
def byteCount : Nat → Option Nat
  | 0 => some 0
  | 2 => some 1
  | 4 => some 2
  | 5 => some 3
  | 7 => some 4
  | 8 => some 5
  | _ => none

/-- The bytes of a group of at most eight characters, which start at position `start`.

Its unused low bits must be zero. -/
def decodeGroup (start : Nat) (group : List Char) : Except Base32Error (List UInt8) := do
  let some size := byteCount group.length | throw (.invalidLength (start + group.length))
  let n ← value start 0 group
  let pad := 5 * group.length - 8 * size
  unless n % 2 ^ pad = 0 do throw (.nonZeroPadBits (start + group.length - 1))
  return natToBytes size (n / 2 ^ pad)

/-- The bytes of a list of characters, eight characters at a time.

The first character of the list is at position `start` of the text. -/
def decodeList (start : Nat) : List Char → Except Base32Error (List UInt8)
  | c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest => do
    let group ← decodeGroup start [c0, c1, c2, c3, c4, c5, c6, c7]
    return group ++ (← decodeList (start + 8) rest)
  | group => decodeGroup start group

/-- The base32 text of a byte string, without padding. -/
def encode (bytes : ByteArray) : String :=
  String.ofList (encodeList bytes.data.toList)

/-- The byte string of a base32 text without padding.

It fails unless the encoder writes exactly this text. -/
def decode (text : String) : Except Base32Error ByteArray := do
  return ⟨(← decodeList 0 text.toList).toArray⟩

end EthLib.Base.Base32
