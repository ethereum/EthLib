module

public import EthLib.Networking.Encoding.Varint

/-!
# Multiformats unsigned varints

libp2p writes lengths and headers as unsigned varints.

They are protobuf varints that must be minimally encoded, as [the format][uvarint] says.

They hold at most nine bytes, so a value is below `2^63`, as [the practical maximum][max] says.

The decoder checks that bound on the value, which a minimal encoding of nine bytes at most meets.

A varint here is read from the start of an input, and the bytes after it are returned.

[uvarint]: https://github.com/multiformats/unsigned-varint/blob/dd184f1ce89c81808503bb719b5fcb13844d08f3/README.md#spec
[max]: https://github.com/multiformats/unsigned-varint/blob/dd184f1ce89c81808503bb719b5fcb13844d08f3/README.md#practical-maximum-of-9-bytes-for-security
-/

@[expose] public section

namespace EthLib.Networking.Encoding.Uvarint

/-- The most bytes an unsigned varint may hold. -/
def maxLength : Nat := 9

/-- The first value that does not fit nine bytes of seven bits. -/
def bound : Nat := 2 ^ 63

/-- Why the unsigned varint at the start of an input was refused. -/
inductive UvarintError where
  /-- The prefix is not a minimal protobuf varint of a 64-bit value. -/
  | varint (error : Varint.VarintError)
  /-- The value is from `2^63` to below `2^64`, so its encoding needs a tenth byte.

  A larger value fails earlier, as a varint that overflows or runs too long. -/
  | tooLarge
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor. -/
def UvarintError.code : UvarintError → UInt32
  | .varint _ => 1
  | .tooLarge => 2

/-- The unsigned varint of a value below `2^63`.

A larger value is outside the format.

Its encoding is that of the value modulo `2^64`, so it decodes to another value or is refused. -/
def encode (n : Nat) : List UInt8 :=
  Varint.encode (UInt64.ofNat n)

/-- The value of the unsigned varint at the start of the input, and the bytes after it. -/
def decode (bytes : List UInt8) : Except UvarintError (Nat × List UInt8) := do
  let (head, rest) := Varint.split bytes
  let value ← (Varint.decode head).mapError .varint
  if bound ≤ value.toNat then throw .tooLarge
  return (value.toNat, rest)

end EthLib.Networking.Encoding.Uvarint
