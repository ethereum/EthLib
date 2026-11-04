module

public import EthLib.Cryptography.Hash.Crc

/-!
# CRC-32

CRC-32, the CRC of ISO 3309 and ITU-T V.42 §8.1.1.6.2 that gzip uses.

[RFC 1952 §2.3.1][rfc1952-2.3.1] names it, and its §8 gives sample code.

The fork identifier of [EIP-2124][eip2124] checksums the genesis hash and the forks with it.

It is the 32-bit CRC with the generator of those standards.

[rfc1952-2.3.1]: https://www.rfc-editor.org/rfc/rfc1952#section-2.3.1
[eip2124]: https://eips.ethereum.org/EIPS/eip-2124#specification
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Crc32

/--
The generator G(x) of CRC-32, without its x^32 term.

G(x) = x^32 + x^26 + x^23 + x^22 + x^16 + x^12 + x^11 + x^10 + x^8 + x^7 + x^5 + x^4 + x^2 + x + 1.

The sample code of RFC 1952 §8 holds it with its 32 bits reversed, as `0xedb88320`.
-/
def generator : UInt32 := 0x04c11db7

/-- The four digest bytes of CRC-32: the highest power of each byte at its least significant bit. -/
def digest (data : ByteArray) : Vector UInt8 4 :=
  Crc.digest generator data

/--
CRC-32 as a number: the digest bytes read least significant byte first.

It is the value of the sample code of RFC 1952 §8, and CRC-32/ISO-HDLC of the CRC catalogue.
-/
def crc32 (data : ByteArray) : UInt32 :=
  Crc.value generator data

end EthLib.Cryptography.Hash.Crc32
