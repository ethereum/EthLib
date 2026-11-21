module

/-!
# `Base.Base64`

The URL-safe base64 of [RFC 4648 §5][rfc], without padding.

The decoder accepts only the text that the encoder writes, so each byte string has one text.

[rfc]: https://www.rfc-editor.org/rfc/rfc4648#section-5
-/

@[expose] public section

namespace EthLib.Base.Base64

/-- Why the base64 decoder refused its input.

A position counts the characters of the text from 0. -/
inductive Base64Error where
  /-- The character `c` at `position` is outside the URL-safe alphabet. -/
  | invalidChar (position : Nat) (c : Char)
  /-- A text of `length` characters, whose last group of one character holds no whole byte. -/
  | invalidLength (length : Nat)
  /-- The last character `c`, at `position`, has unused low bits that are not zero. -/
  | nonZeroPadBits (position : Nat) (c : Char)
  deriving Repr, DecidableEq

/-- The character of a six-bit value, from Table 2 of RFC 4648 §5.

The alphabet is `ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_`, value 0 first.

- `0` to `25` are `A` to `Z`.
- `26` to `51` are `a` to `z`.
- `52` to `61` are `0` to `9`.
- `62` is `-` and `63` is `_`.
-/
def encodeSextet (v : Nat) : Char :=
  -- The 26 uppercase letters.
  if v < 26 then Char.ofNat ('A'.toNat + v)
  -- The 26 lowercase letters.
  else if v < 52 then Char.ofNat ('a'.toNat + (v - 26))
  -- The 10 digits.
  else if v < 62 then Char.ofNat ('0'.toNat + (v - 52))
  -- The two URL-safe symbols.
  else if v = 62 then '-'
  else '_'

/-- The six-bit value of a character of the alphabet, or `none` for any other character.

The padding character `=` and the symbols `+` and `/` of standard base64 are not in the alphabet. -/
def decodeSextet (c : Char) : Option Nat :=
  -- `A` to `Z` are the values 0 to 25.
  if 'A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat then some (c.toNat - 'A'.toNat)
  -- `a` to `z` are the values 26 to 51.
  else if 'a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat then some (c.toNat - 'a'.toNat + 26)
  -- `0` to `9` are the values 52 to 61.
  else if '0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat then some (c.toNat - '0'.toNat + 52)
  else if c = '-' then some 62
  else if c = '_' then some 63
  else none

/-- The characters of a byte string, three bytes at a time.

Three bytes are 24 bits, exactly four characters, so only the last group can be shorter. -/
def encodeList : List UInt8 → List Char
  -- Three bytes fill four characters exactly, so the next group starts on a fresh character.
  | b0 :: b1 :: b2 :: rest =>
    -- The 24 bits of the three bytes, `b0` highest.
    let n := b0.toNat * 2 ^ 16 + b1.toNat * 2 ^ 8 + b2.toNat
    -- The four six-bit values of `n`, highest first.
    encodeSextet (n / 2 ^ 18) :: encodeSextet (n / 2 ^ 12 % 64) ::
      encodeSextet (n / 2 ^ 6 % 64) :: encodeSextet (n % 64) :: encodeList rest
  -- Two bytes left: 16 bits in three characters, with two zero bits at the end.
  | [b0, b1] =>
    let n := b0.toNat * 2 ^ 16 + b1.toNat * 2 ^ 8
    [encodeSextet (n / 2 ^ 18), encodeSextet (n / 2 ^ 12 % 64), encodeSextet (n / 2 ^ 6 % 64)]
  -- One byte left: 8 bits in two characters, with four zero bits at the end.
  | [b0] =>
    let n := b0.toNat * 2 ^ 16
    [encodeSextet (n / 2 ^ 18), encodeSextet (n / 2 ^ 12 % 64)]
  -- No bytes, no characters.
  | [] => []

/-- The six-bit value of the character at a position, or an error outside the alphabet. -/
def readSextet (position : Nat) (c : Char) : Except Base64Error Nat :=
  match decodeSextet c with
  | some v => .ok v
  | none => .error (.invalidChar position c)

/-- The bytes of a list of characters, four characters at a time.

The first character of the list is at position `start` of the text. -/
def decodeList (start : Nat) : List Char → Except Base64Error (List UInt8)
  -- Four characters fill three bytes exactly.
  | c0 :: c1 :: c2 :: c3 :: rest => do
    -- The 24 bits of the four characters, `c0` highest.
    let n := (← readSextet start c0) * 2 ^ 18 + (← readSextet (start + 1) c1) * 2 ^ 12
      + (← readSextet (start + 2) c2) * 2 ^ 6 + (← readSextet (start + 3) c3)
    let bytes ← decodeList (start + 4) rest
    -- The three bytes of `n`, highest first.
    return UInt8.ofNat (n / 2 ^ 16) :: UInt8.ofNat (n / 2 ^ 8 % 256) :: UInt8.ofNat (n % 256)
      :: bytes
  -- Three characters hold two bytes, and their last two bits must be zero.
  | [c0, c1, c2] => do
    let n := (← readSextet start c0) * 2 ^ 18 + (← readSextet (start + 1) c1) * 2 ^ 12
      + (← readSextet (start + 2) c2) * 2 ^ 6
    if n % 2 ^ 8 = 0 then
      return [UInt8.ofNat (n / 2 ^ 16), UInt8.ofNat (n / 2 ^ 8 % 256)]
    else
      throw (.nonZeroPadBits (start + 2) c2)
  -- Two characters hold one byte, and their last four bits must be zero.
  | [c0, c1] => do
    let n := (← readSextet start c0) * 2 ^ 18 + (← readSextet (start + 1) c1) * 2 ^ 12
    if n % 2 ^ 16 = 0 then
      return [UInt8.ofNat (n / 2 ^ 16)]
    else
      throw (.nonZeroPadBits (start + 1) c1)
  -- One character holds only six bits, less than a byte.
  | [_] => throw (.invalidLength (start + 1))
  | [] => return []

/-- The URL-safe base64 text of a byte string, without padding. -/
def encode (bytes : ByteArray) : String :=
  String.ofList (encodeList bytes.data.toList)

/-- The byte string of a URL-safe base64 text without padding.

It fails unless the encoder writes exactly this text. -/
def decode (text : String) : Except Base64Error ByteArray := do
  let bytes ← decodeList 0 text.toList
  return ⟨bytes.toArray⟩

end EthLib.Base.Base64
