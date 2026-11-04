module

/-!
# `Networking.Enr.Base64`

The URL-safe base64 of RFC 4648, without padding.

The alphabet is Table 2 of [RFC 4648 §5](https://www.rfc-editor.org/rfc/rfc4648#section-5).

Each group of three bytes, 24 bits, becomes four characters of six bits each.

A last group of one or two bytes becomes two or three characters, and the unused low bits are zero.

```text
[ b0: 8 | b1: 8 | b2: 8 ]  ->  [ c0: 6 | c1: 6 | c2: 6 | c3: 6 ]
```

The decoder accepts only what the encoder writes.

It rejects the padding character `=`, which is not in the alphabet.

It also rejects a last character whose unused bits are not zero, as RFC 4648 §3.5 allows.

So every byte string has exactly one text.
-/

@[expose] public section

namespace EthLib.Networking.Enr.Base64

/-- Why the base64 decoder refused its input. -/
inductive Base64Error where
  /-- A character outside the URL-safe alphabet. -/
  | invalidChar (c : Char)
  /-- A last group of one character, which holds no whole byte. -/
  | invalidLength
  /-- A last character whose unused low bits are not zero. -/
  | nonZeroPadBits
  deriving Repr, DecidableEq

/-- The character of a six-bit value, from Table 2 of RFC 4648 §5.

The values 0 to 25 are `A` to `Z`, 26 to 51 are `a` to `z`, and 52 to 61 are `0` to `9`.

62 is `-` and 63 is `_`. -/
def encodeSextet (v : Nat) : Char :=
  if v < 26 then Char.ofNat (65 + v)
  else if v < 52 then Char.ofNat (97 + (v - 26))
  else if v < 62 then Char.ofNat (48 + (v - 52))
  else if v = 62 then '-'
  else '_'

/-- The six-bit value of a character of the alphabet, or `none` for any other character. -/
def decodeSextet (c : Char) : Option Nat :=
  if 65 ≤ c.toNat ∧ c.toNat < 91 then some (c.toNat - 65)
  else if 97 ≤ c.toNat ∧ c.toNat < 123 then some (c.toNat - 97 + 26)
  else if 48 ≤ c.toNat ∧ c.toNat < 58 then some (c.toNat - 48 + 52)
  else if c = '-' then some 62
  else if c = '_' then some 63
  else none

/-- The characters of a byte string, three bytes at a time. -/
def encodeList : List UInt8 → List Char
  | b0 :: b1 :: b2 :: rest =>
    let n := b0.toNat * 2 ^ 16 + b1.toNat * 2 ^ 8 + b2.toNat
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
  | [] => []

/-- The six-bit value of a character, or an error for a character outside the alphabet. -/
def readSextet (c : Char) : Except Base64Error Nat :=
  match decodeSextet c with
  | some v => .ok v
  | none => .error (.invalidChar c)

/-- The bytes of a list of characters, four characters at a time. -/
def decodeList : List Char → Except Base64Error (List UInt8)
  | c0 :: c1 :: c2 :: c3 :: rest => do
    let n := (← readSextet c0) * 2 ^ 18 + (← readSextet c1) * 2 ^ 12
      + (← readSextet c2) * 2 ^ 6 + (← readSextet c3)
    let bytes ← decodeList rest
    return UInt8.ofNat (n / 2 ^ 16) :: UInt8.ofNat (n / 2 ^ 8 % 256) :: UInt8.ofNat (n % 256)
      :: bytes
  -- Three characters hold two bytes, and their last two bits must be zero.
  | [c0, c1, c2] => do
    let n := (← readSextet c0) * 2 ^ 18 + (← readSextet c1) * 2 ^ 12 + (← readSextet c2) * 2 ^ 6
    if n % 2 ^ 8 = 0 then
      return [UInt8.ofNat (n / 2 ^ 16), UInt8.ofNat (n / 2 ^ 8 % 256)]
    else
      throw .nonZeroPadBits
  -- Two characters hold one byte, and their last four bits must be zero.
  | [c0, c1] => do
    let n := (← readSextet c0) * 2 ^ 18 + (← readSextet c1) * 2 ^ 12
    if n % 2 ^ 16 = 0 then
      return [UInt8.ofNat (n / 2 ^ 16)]
    else
      throw .nonZeroPadBits
  | [_] => throw .invalidLength
  | [] => return []

/-- The URL-safe base64 text of a byte string, without padding. -/
def encode (bytes : ByteArray) : String :=
  String.ofList (encodeList bytes.data.toList)

/-- The byte string of a URL-safe base64 text without padding.

It fails unless the encoder writes exactly this text. -/
def decode (text : String) : Except Base64Error ByteArray := do
  let bytes ← decodeList text.toList
  return ⟨bytes.toArray⟩

end EthLib.Networking.Enr.Base64
