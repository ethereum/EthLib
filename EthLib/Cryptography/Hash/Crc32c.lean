module

/-!
# CRC-32C

CRC-32C, the Castagnoli CRC of [RFC 3720 §12.1][rfc3720-12.1].

The Snappy framing format §3 checks each data chunk with it:
<https://github.com/google/snappy/blob/f82bff66afe0de4c9ae22f8c4ef84e3c2233e799/framing_format.txt>

It detects errors and authenticates nothing: anyone can recompute it.

The RFC reads a message of n bits as a polynomial M(x) over GF(2).

Coefficients are bits, and adding is XOR.

The CRC is the complemented remainder of a division by a generator G(x):

- One coefficient enters the division at a time.
- A byte enters bit by bit, in the order the RFC fixes.
- The remainder R(x) is complemented and mapped into four digest bytes.

A polynomial of degree below 32 is a `UInt32`, with bit i holding the coefficient of x^i.

The RFC numbers the bits of a byte the other way: bit 0 is the most significant.

[RFC 3720 §2.3.3][rfc3720-2.3.3] fixes that order.

The division runs one coefficient at a time, to be read against the RFC, not for speed.

[rfc3720-12.1]: https://www.rfc-editor.org/rfc/rfc3720#section-12.1
[rfc3720-2.3.3]: https://www.rfc-editor.org/rfc/rfc3720#section-2.3.3
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Crc32c

/--
The generator G(x) of RFC 3720 §12.1, without its x^32 term.

The RFC writes G(x) as `0x11edc6f41`.

A remainder has degree at most 31, so the division step handles the x^32 term itself.
-/
def generator : UInt32 := 0x1edc6f41

/--
One more coefficient `c` of M(x) enters the division of M(x) * x^32 by G(x).

If `r` is the remainder of A(x) * x^32, the result is the remainder of (x * A(x) + c) * x^32.

Multiplying by x moves the coefficient of x^31 up to x^32, where `c` joins it.

When their sum is 1, subtracting G(x) cancels the x^32 term.

Over GF(2), subtracting is XOR.
-/
def shift (r : UInt32) (c : Bool) : UInt32 :=
  if (r >>> 31 == 1) ^^ c then (r <<< 1) ^^^ generator else r <<< 1

/--
The eight bits of a byte enter the division as the next eight coefficients of M(x).

RFC 3720 §12.1 makes bit 7 of the first byte the highest coefficient.

Bit 7 is the least significant bit (§2.3.3), so each byte enters least significant bit first.
-/
def shiftByte (r : UInt32) (byte : UInt8) : UInt32 :=
  -- Step i reads the bit worth 2^i.
  (List.range 8).foldl (fun acc i => shift acc ((byte >>> i.toUInt8) &&& 1 == 1)) r

/--
The remainder R(x) of RFC 3720 §12.1.

The RFC complements the 32 highest coefficients of M(x), multiplies by x^32 and divides by G(x).

On a message of 32 bits or more, a division from `0xffffffff` instead of 0 has the same effect.

The RFC never divides a shorter message.

A shorter message, such as an empty Snappy chunk, also starts from `0xffffffff`.

That is the initial value of CRC-32/ISCSI in the CRC catalogue:
<https://reveng.sourceforge.io/crc-catalogue/17plus.htm#crc.cat.crc-32-iscsi>
-/
def remainder (data : ByteArray) : UInt32 :=
  data.data.toList.foldl shiftByte 0xffffffff

/-- The bits of a byte in reverse order: the bit worth 2^i moves to 2^(7 - i). -/
def reverseBits (byte : UInt8) : UInt8 :=
  (List.range 8).foldl (fun acc i => acc ||| (((byte >>> i.toUInt8) &&& 1) <<< (7 - i).toUInt8)) 0

/--
The four digest bytes of RFC 3720 §12.1: the CRC, which is R(x) complemented.

- Byte 0 holds x^31 down to x^24, byte 1 holds x^23 down to x^16, and so on.
- In each byte, the highest power goes to bit 7, the least significant bit (§2.3.3).
-/
def digest (data : ByteArray) : Vector UInt8 4 :=
  let crc := ~~~(remainder data)
  -- Each shift leaves the highest power of a byte at 2^7, and reversing moves it to 2^0.
  #v[reverseBits (crc >>> 24).toUInt8, reverseBits (crc >>> 16).toUInt8,
    reverseBits (crc >>> 8).toUInt8, reverseBits crc.toUInt8]

/--
CRC-32C as a number: the digest bytes read least significant byte first.

It is CRC-32/ISCSI of the CRC catalogue.
-/
def crc32c (data : ByteArray) : UInt32 :=
  let d := digest data
  d[0].toUInt32 ||| d[1].toUInt32 <<< 8 ||| d[2].toUInt32 <<< 16 ||| d[3].toUInt32 <<< 24

end EthLib.Cryptography.Hash.Crc32c
