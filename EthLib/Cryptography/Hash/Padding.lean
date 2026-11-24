module

/-!
# Merkle-Damgård padding of 64-byte blocks

SHA-256 ([FIPS 180-4 §5.1.1][fips]) and MD4 ([RFC 1320 §3.1 and §3.2][rfc1320]) pad alike.

They differ only in the byte order of the length, so each hash passes its own length bytes.

RIPEMD-160 takes the padding of MD4.

[fips]: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf
[rfc1320]: https://www.rfc-editor.org/rfc/rfc1320#section-3.1
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Padding

/-- The zero bytes between the `0x80` byte and the length, so that the blocks are whole.

They are the fewest that bring the message, that byte, them and the length to whole blocks. -/
def paddingZeros (size : Nat) : Nat :=
  -- RFC 1320 §3.1 and FIPS 180-4 §5.1.1: zeros until the size is 448 bits modulo 512.
  --
  -- In bytes: the message, the byte `0x80` and the zeros fill all but 8 bytes of a block.
  (64 - (size + 9) % 64) % 64

/-- The padded message: the message, the byte `0x80`, the zeros, then the 8 length bytes.

The message is whole bytes, so the bit 1 and the seven zero bits after it are the byte `0x80`. -/
def pad (lengthBytes : Nat → ByteArray) (message : ByteArray) : ByteArray :=
  message.push 0x80 ++ ⟨Array.replicate (paddingZeros message.size) 0⟩ ++
    lengthBytes message.size

end EthLib.Cryptography.Hash.Padding
