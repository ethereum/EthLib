module

/-!
# `Base.ByteOrder`

An integer written in base 256, one digit per byte.

A little-endian encoding puts the least significant byte first.
-/

@[expose] public section

namespace EthLib.Base.ByteOrder

/-- The `n` low bytes of `x`, least significant first.

A number below `256 ^ n` is written exactly, and a larger one keeps only `x % 256 ^ n`.

For example, the two low bytes of `0x1234` are `[0x34, 0x12]`. -/
def toLE (n x : Nat) : Vector UInt8 n :=
  -- Byte `i` holds bits `8i` to `8i + 7`.
  Vector.ofFn fun i => UInt8.ofNat (x >>> (8 * i.val))

/-- The number whose `n` bytes these are, the least significant first.

It is below `256 ^ n`.

For example, `[0x34, 0x12]` reads as `0x1234`. -/
def ofLE {n : Nat} (bytes : Vector UInt8 n) : Nat :=
  -- Horner's rule from the most significant byte, the last one, down.
  bytes.toArray.foldr (fun b acc => b.toNat + 256 * acc) 0

end EthLib.Base.ByteOrder
