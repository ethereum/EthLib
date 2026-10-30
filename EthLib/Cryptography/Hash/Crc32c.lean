/-!
# `Hash.Crc32c`

CRC-32C, the Castagnoli CRC, as RFC 3720 §12.1 defines it for the iSCSI digests.

RFC 7143, which obsoletes RFC 3720, keeps the same process in §13.1.

The Snappy framing format, last revised 2013-10-25, checks the uncompressed data of each data chunk with it, after a masking of its own.

RFC 3720 §12.1 says these digests "only have error detection significance".

Anyone can recompute a CRC, so it authenticates nothing.

The RFC reads a message of `n` bits as a polynomial M(x) of degree `n - 1` over GF(2), where coefficients are bits and adding is XOR.

It defines the CRC through a division by a generator G(x), and the definitions follow that process:

```text
generator   G(x), the divisor
shift       one coefficient of M(x) enters the division
shiftByte   the eight coefficients of one byte, in the order the RFC fixes
remainder   R(x), the remainder of the complemented M(x) * x^32
digest      R(x) complemented, mapped into the four bytes of the digest word
crc32c      the digest word read as a little-endian number
```

A polynomial of degree below 32 is stored as a `UInt32`, bit `i` holding the coefficient of `x^i`.

The RFC numbers the bits of a byte the other way: bit 0 is the most significant and bit 7 the least (RFC 3720 §2.3.3).

The division runs one coefficient at a time, to be read against the RFC, not for speed.

The CRC catalogue cited below is Greg Cook's [Catalogue of parametrised CRC algorithms](https://reveng.sourceforge.io/crc-catalogue/17plus.htm#crc.cat.crc-32-iscsi), last updated 11 December 2024.

It lists CRC-32C as CRC-32/ISCSI.
-/

namespace EthLib.Cryptography.Hash.Crc32c

/--
The generator polynomial G(x) of RFC 3720 §12.1, without its `x^32` term.

The RFC writes G(x) as `0x11edc6f41`, so G(x) is `x^32` plus the polynomial `0x1edc6f41`.

A remainder has degree at most 31, so `shift` handles the `x^32` term itself.
-/
def generator : UInt32 := 0x1edc6f41

/--
One more coefficient `c` of M(x) enters the division of `M(x) * x^32` by G(x).

If `r` is the remainder of `A(x) * x^32`, the result is the remainder of `(x * A(x) + c) * x^32`.

That is the remainder of `x * r + c * x^32`.

Multiplying `r` by `x` moves its coefficient of `x^31` up to `x^32`, where `c` joins it.

When their sum is 1, subtracting G(x) cancels the `x^32` term, and over GF(2) subtracting is XOR.
-/
def shift (r : UInt32) (c : Bool) : UInt32 :=
  if (r >>> 31 == 1) ^^ c then (r <<< 1) ^^^ generator else r <<< 1

/--
The eight bits of `byte` enter the division as the next eight coefficients of M(x).

RFC 3720 §12.1 makes bit 7 of the first byte the highest coefficient, followed by bit 6, through bit 0 of the last byte.

Bit 7 is the least significant bit (§2.3.3), so each byte enters least significant bit first.
-/
def shiftByte (r : UInt32) (byte : UInt8) : UInt32 :=
  -- Step `i` reads the bit worth `2^i`.
  (List.range 8).foldl (fun acc i => shift acc ((byte >>> i.toUInt8) &&& 1 == 1)) r

/--
R(x) of RFC 3720 §12.1, for a message of `n` bits.

The RFC complements the 32 highest coefficients of M(x), multiplies by `x^32` and divides by G(x).

Each `shift` multiplies the remainder by `x` and adds its coefficient times `x^32`, modulo G(x).

So starting from `0xffffffff` instead of 0 adds `(x^31 + ... + 1) * x^n` to the dividend `M(x) * x^32`.

For `n >= 32`, adding it is the same as complementing the 32 highest coefficients of M(x) before the multiplication.

RFC 3720 never applies the process to fewer than 32 bits.

Its digests cover a header of at least 48 bytes or a data segment padded to four-byte words, and an empty data segment has none (§10.2, §10.2.3).

A shorter message still starts from `0xffffffff`, the initial value of CRC-32/ISCSI in the CRC catalogue.
-/
def remainder (data : ByteArray) : UInt32 :=
  data.data.toList.foldl shiftByte 0xffffffff

/-- The bits of a byte in reverse order: the bit worth `2^i` moves to `2^(7 - i)`. -/
def reverseBits (byte : UInt8) : UInt8 :=
  (List.range 8).foldl (fun acc i => acc ||| (((byte >>> i.toUInt8) &&& 1) <<< (7 - i).toUInt8)) 0

/--
The digest word of RFC 3720 §12.1: the CRC, which is R(x) complemented, mapped into four bytes.

Byte 0 holds the coefficients of `x^31` down to `x^24`, byte 1 those of `x^23` down to `x^16`, and so on.

In each byte the highest power goes to bit 7, the least significant bit (§2.3.3):

```text
    coefficients   x^31 .. x^24 | x^23 .. x^16 | x^15 .. x^8 | x^7 .. x^0
    digest byte          0      |       1      |      2      |     3
    bit worth       2^0 .. 2^7  |  2^0 .. 2^7  |  2^0 .. 2^7 | 2^0 .. 2^7
```
-/
def digest (data : ByteArray) : Vector UInt8 4 :=
  let crc := ~~~(remainder data)
  -- After the shift, the highest power of each byte is worth `2^7`, and `reverseBits` moves it to `2^0`.
  #v[reverseBits (crc >>> 24).toUInt8, reverseBits (crc >>> 16).toUInt8,
    reverseBits (crc >>> 8).toUInt8, reverseBits crc.toUInt8]

/--
CRC-32C as a number: the digest word read least significant byte first.

Bit `k` of the number is the coefficient of `x^(31 - k)` in the CRC.

It is CRC-32/ISCSI of the CRC catalogue.
-/
def crc32c (data : ByteArray) : UInt32 :=
  let d := digest data
  d[0].toUInt32 ||| d[1].toUInt32 <<< 8 ||| d[2].toUInt32 <<< 16 ||| d[3].toUInt32 <<< 24

end EthLib.Cryptography.Hash.Crc32c
