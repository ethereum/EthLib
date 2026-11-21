module

public import EthLib.Base.BigEndian

/-!
# `Base.Base32`

The base32 of [RFC 4648 §6](https://www.rfc-editor.org/rfc/rfc4648#section-6), without padding.

The decoder accepts only the text that the encoder writes, so each byte string has one text.
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

/-- The character of a five-bit value, from Table 3 of RFC 4648 §6.

The alphabet is `ABCDEFGHIJKLMNOPQRSTUVWXYZ234567`, value 0 first.

- `0` (`00000`) to `25` (`11001`) are `A` to `Z`.
- `26` (`11010`) to `31` (`11111`) are `2` to `7`.
-/
def encodeQuint (v : Nat) : Char :=
  -- The 26 letters come first, so `v` below 26 is the letter `v` places after `A`.
  -- The digits follow, so `v` from 26 is the digit `v - 26` places after `2`.
  if v < 26 then Char.ofNat ('A'.toNat + v) else Char.ofNat ('2'.toNat + (v - 26))

/-- The five-bit value of a character of the alphabet, or `none` for any other character.

The padding character `=` and the lowercase letters are not in the alphabet. -/
def decodeQuint (c : Char) : Option Nat :=
  -- `A` to `Z` are the values 0 to 25.
  if 'A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat then some (c.toNat - 'A'.toNat)
  -- `2` to `7` are the values 26 to 31, after the 26 letters.
  else if '2'.toNat ≤ c.toNat ∧ c.toNat ≤ '7'.toNat then some (c.toNat - '2'.toNat + 26)
  else none

/-- The `count` characters of a number below `32 ^ count`, the first one the highest. -/
def digits : Nat → Nat → List Char
  | 0, _ => []
  -- The highest of the `count + 1` digits in base 32, then the `count` digits below it.
  | count + 1, n => encodeQuint (n / 32 ^ count % 32) :: digits count n

/-- The number of characters that encode `size` bytes: `ceil(8 * size / 5)`.

Each character holds 5 bits, so `8 * size` bits need that many characters, the last one partly full.

- 1 byte, 8 bits: 2 characters.
- 2 bytes, 16 bits: 4 characters.
- 3 bytes, 24 bits: 5 characters.
- 4 bytes, 32 bits: 7 characters.
- 5 bytes, 40 bits: 8 characters.
-/
def charCount (size : Nat) : Nat :=
  -- Adding 4 before dividing by 5 rounds the quotient up.
  (8 * size + 4) / 5

/-- The characters of a group of at most five bytes.

Its bits come first, then zero bits up to a whole number of characters. -/
def encodeGroup (group : List UInt8) : List Char :=
  let count := charCount group.length
  -- Shift the bits of the group up past the zero bits that complete the last character.
  -- Example, RFC 4648 §10: the byte `f` = `01100110` takes two characters, 10 bits.
  -- Two zero bits complete them: `01100 11000` = 12, 24 = `M`, `Y`.
  digits count (bytesToNat group <<< (5 * count - 8 * group.length))

/-- The characters of a byte string, five bytes at a time.

Five bytes are 40 bits, exactly eight characters, so only the last group can be shorter. -/
def encodeList : List UInt8 → List Char
  -- Five bytes fill eight characters exactly, so the next group starts on a fresh character.
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => encodeGroup [b0, b1, b2, b3, b4] ++ encodeList rest
  -- The last zero to four bytes, completed with zero bits.
  | group => encodeGroup group

/-- The number that a list of characters writes after `acc`, the first character the highest.

The first character is at position `start` of the text. -/
def value (start acc : Nat) : List Char → Except Base32Error Nat
  | [] => return acc
  | c :: rest => do
    -- A character outside the alphabet fails, with its position.
    let some v := decodeQuint c | throw (.invalidChar start c)
    -- Append the digit `v` in base 32.
    value (start + 1) (acc * 32 + v) rest

/-- The number of bytes of a group of `count` characters, if a group can have that many.

It inverts the character count of a group.

No group of bytes takes 1, 3 or 6 characters, so those counts fail. -/
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
  -- A count of 1, 3 or 6 characters writes no whole number of bytes.
  let some size := byteCount group.length | throw (.invalidLength (start + group.length))
  -- The bits of the characters, as one number.
  let n ← value start 0 group
  -- The zero bits that the encoder wrote after the bytes.
  let pad := 5 * group.length - 8 * size
  -- RFC 4648 §3.5 lets a decoder reject nonzero padding bits, so that each text is canonical.
  unless n % 2 ^ pad = 0 do throw (.nonZeroPadBits (start + group.length - 1))
  -- Drop the padding bits and write the rest as `size` big-endian bytes.
  return natToBytes size (n >>> pad)

/-- The bytes of a list of characters, eight characters at a time.

The first character of the list is at position `start` of the text. -/
def decodeList (start : Nat) : List Char → Except Base32Error (List UInt8)
  | c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest => do
    -- Eight characters are 40 bits, exactly five bytes.
    let group ← decodeGroup start [c0, c1, c2, c3, c4, c5, c6, c7]
    return group ++ (← decodeList (start + 8) rest)
  -- The last zero to seven characters.
  | group => decodeGroup start group

/-- The base32 text of a byte string, without padding. -/
def encode (bytes : ByteArray) : String :=
  String.ofList (encodeList bytes.data.toList)

/-- The byte string of a base32 text without padding.

It fails unless the encoder writes exactly this text. -/
def decode (text : String) : Except Base32Error ByteArray := do
  return ⟨(← decodeList 0 text.toList).toArray⟩

end EthLib.Base.Base32
