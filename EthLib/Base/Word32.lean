module

/-!
# `Base.Word32`

The 32-bit little-endian words that several hashes and ciphers read and write.

Among them, ChaCha20 follows RFC 8439 §§2.1 and 2.3, and Salsa20/8 follows RFC 7914 §3.
-/

@[expose] public section

namespace EthLib.Base

/-- Rotate a 32-bit word left by `shift` bits, counted modulo 32. -/
@[inline] def rotl32 (x shift : UInt32) : UInt32 :=
  -- The bits shifted out at the top come back in at the bottom.
  (x <<< shift) ||| (x >>> (32 - shift))

/-- Four bytes, least significant first, read as a 32-bit word. -/
@[inline] def uint32OfBytes (b0 b1 b2 b3 : UInt8) : UInt32 :=
  -- Byte `i` lands at bits `8i` to `8i + 7`.
  b0.toUInt32 ||| b1.toUInt32 <<< 8 ||| b2.toUInt32 <<< 16 ||| b3.toUInt32 <<< 24

/-- Byte `i` of the little-endian encoding of a 32-bit word, for `i` below 4.

For example, byte 1 of `0x12345678` is `0x56`. -/
@[inline] def uint32Byte (word : UInt32) (i : Nat) : UInt8 :=
  -- Bring bits `8i` to `8i + 7` to the bottom, then keep the low byte.
  (word >>> UInt32.ofNat (8 * i)).toUInt8

end EthLib.Base
