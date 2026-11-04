module

public import EthLib.Cryptography.Hash.Crc

/-!
# CRC-32C

CRC-32C, the Castagnoli CRC of [RFC 3720 §12.1][rfc3720-12.1].

The Snappy framing format §3 checks each data chunk with it:
<https://github.com/google/snappy/blob/f82bff66afe0de4c9ae22f8c4ef84e3c2233e799/framing_format.txt>

It is the 32-bit CRC with the generator of the RFC.

The RFC numbers the bits of a byte from the most significant: bit 0 is worth 2^7.

[RFC 3720 §2.3.3][rfc3720-2.3.3] fixes that order.

So the RFC's bit 7 of a byte, its highest coefficient, is the least significant bit.

[rfc3720-12.1]: https://www.rfc-editor.org/rfc/rfc3720#section-12.1
[rfc3720-2.3.3]: https://www.rfc-editor.org/rfc/rfc3720#section-2.3.3
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Crc32c

/--
The generator G(x) of RFC 3720 §12.1, without its x^32 term.

The RFC writes G(x) as `0x11edc6f41`.
-/
def generator : UInt32 := 0x1edc6f41

/--
The remainder R(x) of RFC 3720 §12.1, before its complement.

The RFC never divides a message shorter than 32 bits.

A shorter message, such as an empty Snappy chunk, starts from `0xffffffff` as a longer one does.

That is the initial value of CRC-32/ISCSI in the CRC catalogue.
-/
def remainder (data : ByteArray) : UInt32 :=
  Crc.remainder generator data

/--
The four digest bytes of RFC 3720 §12.1: the CRC, which is R(x) complemented.

- Byte 0 holds x^31 down to x^24, byte 1 holds x^23 down to x^16, and so on.
- In each byte, the highest power goes to bit 7, the least significant bit (§2.3.3).
-/
def digest (data : ByteArray) : Vector UInt8 4 :=
  Crc.digest generator data

/--
CRC-32C as a number: the digest bytes read least significant byte first.

It is CRC-32/ISCSI of the CRC catalogue.
-/
def crc32c (data : ByteArray) : UInt32 :=
  Crc.value generator data

end EthLib.Cryptography.Hash.Crc32c
