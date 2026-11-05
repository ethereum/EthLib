module

/-!
# `Base.Bytes`

Byte strings of a fixed length, with the length in the type.

Source: section 3 of the Yellow Paper, Shanghai version, in
[`Paper.tex` at `efc5f9a`](https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex).

It writes `B_n` for the byte strings of length `n`.

A read of one byte of an untyped string gives zero past its end.
-/

@[expose] public section

namespace EthLib.Base

/-- `B_8`: exactly 8 bytes, such as the nonce of a block header. -/
abbrev Bytes8 := Vector UInt8 8

/-- `B_32`: exactly 32 bytes, such as a storage key. -/
abbrev Bytes32 := Vector UInt8 32

/-- `B_256`: exactly 256 bytes, such as the logs bloom of a block header. -/
abbrev Bytes256 := Vector UInt8 256

/-! ## Crossing to and from untyped bytes -/

/-- The bytes of a fixed-size object, in order.

Examples:
* `(packBytes #v[10, 20]).data = #[10, 20]`
* `(packBytes #v[10, 20]).size = 2`
-/
def packBytes {n : Nat} (v : Vector UInt8 n) : ByteArray :=
  -- The length invariant is discarded, not checked: every object has one.
  ⟨v.toArray⟩

/-- Read the `n` bytes of a buffer that start at an offset.

The caller proves the buffer has room, so the read needs no fallback byte.

Example, with `b = ByteArray.mk #[10, 20, 30, 40]`:
* `readBytes b 1 2 _ = #v[20, 30]`
-/
def readBytes (b : ByteArray) (offset n : Nat) (h : offset + n ≤ b.size) :
    Vector UInt8 n :=
  -- Every index below the object's length lands inside the buffer.
  Vector.ofFn fun i => b.data[offset + i.val]'(by
    simp only [ByteArray.size] at h
    omega)

/-- The byte at index `i` of the buffer, or `0` past its end.

It reads the byte in place, since the array of all the bytes would cost a copy of the buffer. -/
@[inline] def byteAt (data : ByteArray) (i : Nat) : UInt8 :=
  if h : i < data.size then data[i] else 0

/-! ## Bitwise operations -/

/-- The exclusive or of two byte strings of one length, byte by byte. -/
def xorBytes {n : Nat} (a b : Vector UInt8 n) : Vector UInt8 n :=
  Vector.zipWith (· ^^^ ·) a b

end EthLib.Base
