module

/-!
# A 32-bit CRC

A 32-bit cyclic redundancy check, for any generator polynomial of degree 32.

CRC-32 and CRC-32C are this CRC with two generators.

It detects errors and authenticates nothing: anyone can recompute it.

A message of n bits is a polynomial M(x) over GF(2), whose coefficients are bits.

The CRC is the complemented remainder of a division by the generator G(x).

The process is the one of RFC 3720 §12.1, which CRC-32 shares, and each step is marked on its line:
<https://www.rfc-editor.org/rfc/rfc3720#section-12.1>

A polynomial of degree below 32 is a `UInt32`, with bit i holding the coefficient of x^i.

The division runs one coefficient at a time, to be read against its sources, not for speed.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Crc

/--
One more coefficient `c` of M(x) enters the division of M(x) * x^32 by G(x).

The generator `g` is G(x) without its x^32 term.

If `r` is the remainder of A(x) * x^32, the result is the remainder of (x * A(x) + c) * x^32.

Multiplying by x moves the coefficient of x^31 up to x^32, where `c` joins it.

When their sum is 1, subtracting G(x) cancels the x^32 term.

Over GF(2), subtracting is XOR.
-/
def shift (g : UInt32) (r : UInt32) (c : Bool) : UInt32 :=
  -- "The polynomial is multiplied by x^32 then divided by G(x)", one coefficient at a time.
  --
  -- No zeros are appended: `c` joins the term of x^32 directly.
  if (r >>> 31 == 1) ^^ c then (r <<< 1) ^^^ g else r <<< 1

/--
The eight bits of a byte enter the division as the next eight coefficients of M(x).

The least significant bit of a byte is its highest coefficient, so it enters first.
-/
def shiftByte (g : UInt32) (r : UInt32) (byte : UInt8) : UInt32 :=
  -- "bit 7 of the lowest numbered byte is considered the most significant bit (x^n-1)", then bit 6.
  --
  -- RFC 3720 §2.3.3 numbers bits from the most significant, so its bit 7 is worth 2^0.
  (List.range 8).foldl (fun acc i => shift g acc ((byte >>> i.toUInt8) &&& 1 == 1)) r

/--
The remainder R(x) of a message, before its complement.

On a message of 32 bits or more, a division from `0xffffffff` instead of 0 has the same effect.

A shorter message also starts from `0xffffffff`, as the CRC catalogue does:
<https://reveng.sourceforge.io/crc-catalogue/17plus.htm>
-/
def remainder (g : UInt32) (data : ByteArray) : UInt32 :=
  -- "The most significant 32 bits are complemented".
  --
  -- The division starts from `0xffffffff` instead of 0, which has the same effect.
  --
  -- So leading zero bytes change the CRC.
  --
  -- Then each byte of M(x), the lowest numbered first, enters the division.
  data.data.toList.foldl (shiftByte g) 0xffffffff

/-- The bits of a byte in reverse order: the bit worth 2^i moves to 2^(7 - i). -/
def reverseBits (byte : UInt8) : UInt8 :=
  (List.range 8).foldl (fun acc i => acc ||| (((byte >>> i.toUInt8) &&& 1) <<< (7 - i).toUInt8)) 0

/-- The four digest bytes: the CRC, which is R(x) complemented. -/
def digest (g : UInt32) (data : ByteArray) : Vector UInt8 4 :=
  -- "The coefficients of R(x) are considered a 32 bit sequence": the `UInt32` already is one.
  --
  -- "The bit sequence is complemented and the result is the CRC."
  let crc := ~~~(remainder g data)
  -- "The CRC bits are mapped into the digest word".
  --
  -- Byte 0 holds x^31 down to x^24, byte 1 x^23 down to x^16, and so on.
  --
  -- In each byte, the highest power goes to the least significant bit, RFC 3720's bit 7.
  --
  -- Each shift leaves the highest power of a byte at 2^7, and reversing moves it to 2^0.
  #v[reverseBits (crc >>> 24).toUInt8, reverseBits (crc >>> 16).toUInt8,
    reverseBits (crc >>> 8).toUInt8, reverseBits crc.toUInt8]

/-- The CRC as a number: the digest bytes read least significant byte first. -/
def value (g : UInt32) (data : ByteArray) : UInt32 :=
  let d := digest g data
  d[0].toUInt32 ||| d[1].toUInt32 <<< 8 ||| d[2].toUInt32 <<< 16 ||| d[3].toUInt32 <<< 24

end EthLib.Cryptography.Hash.Crc
