module

/-!
# `Base.LittleEndian`

Little-endian integers: a number written as bytes, and bytes read back as a number.

The first byte is the least significant one:

```text
    [0x34, 0x12]  reads as  0x34 + 256 * 0x12 = 0x1234
```
-/

@[expose] public section

namespace EthLib.Base

/-- The `k` low bytes of `n`, least significant first.

An unsigned integer of `k` bytes is below `256 ^ k`, and its bytes are exact.

A larger `n` keeps only `n % 256 ^ k`.

For example, the two low bytes of `0x1234` are `[0x34, 0x12]`. -/
def uintToBytes (k n : Nat) : Vector UInt8 k :=
  -- Byte `i` holds bits `8i` to `8i + 7`.
  Vector.ofFn fun i => UInt8.ofNat (n / 256 ^ i.val)

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

end EthLib.Base
