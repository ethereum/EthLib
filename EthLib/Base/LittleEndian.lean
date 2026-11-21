module

/-!
# `Base.LittleEndian`

Little-endian integers: a number written as bytes, and bytes read back as a number.
-/

@[expose] public section

namespace EthLib.Base

/-- The `k` low bytes of `n`, least significant first.

An unsigned integer of `k` bytes is below `256 ^ k`, and its bytes are exact.

A larger `n` keeps only `n % 256 ^ k`.

For example, the two low bytes of `0x1234` are `[0x34, 0x12]`. -/
def uintToBytes (k n : Nat) : Vector UInt8 k :=
  -- Byte `i` holds bits `8i` to `8i + 7`.
  Vector.ofFn fun i => UInt8.ofNat (n >>> (8 * i.val))

/-- The number whose little-endian bytes these are.

For example, `[0x34, 0x12]` reads as `0x1234`. -/
def bytesToUint {k : Nat} (bytes : Vector UInt8 k) : Nat :=
  -- Horner's rule from the most significant byte down.
  bytes.toArray.foldr (fun byte acc => byte.toNat + 256 * acc) 0

/-- At most eight bytes, read as a little-endian `UInt64`.

Fewer than eight bytes are allowed, and `k` bytes read as a value below `256^k`.

The bound on `k` keeps the value below `2^64`, so it never wraps. -/
def bytesToUint64 {k : Nat} (data : Vector UInt8 k) (_ : k ≤ 8 := by decide) : UInt64 :=
  UInt64.ofNat (bytesToUint data)

/-! ## 32-bit words

These helpers serve the ciphers whose state is a list of little-endian 32-bit words.
-/

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
