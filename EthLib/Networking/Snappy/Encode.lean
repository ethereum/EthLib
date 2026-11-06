module

public import EthLib.Networking.Snappy.Block

/-!
# `Networking.Snappy.Encode`

The elements that a Snappy compressor writes, from `format_description.txt` of `google/snappy`:
<https://github.com/google/snappy/blob/7406111ac4ae539ea0db8b7ea2dc76730cd957f4/format_description.txt>.

- A copy with a one-byte offset holds a length of 4 to 11 and an offset below 2048 (§2.2.1).
- A copy with a two-byte offset holds a length of 1 to 64 and an offset below 65536 (§2.2.2).
- A literal holds any run of bytes (§2.1), which the block encoder already writes.

A copy longer than 64 bytes is written as several copies of one offset.

The decoder reads these bytes back as the copy they were written for.

This file only writes elements, and it never decides which bytes to copy.
-/

@[expose] public section

namespace EthLib.Networking.Snappy

/-- The most bytes one copy element holds, whatever its offset width (§2.2.2). -/
def maxCopyLength : Nat := 64

/-- The offsets below this bound fit a copy with a one-byte offset (§2.2.1).

Its offset has 11 bits: eight after the tag, and three in the tag.
-/
def copyOneOffsetBound : Nat := 2048

/-- The offsets below this bound fit a copy with a two-byte offset (§2.2.2). -/
def copyTwoOffsetBound : Nat := 65536

/-- A copy element with a one-byte offset, for a length of 4 to 11 and an offset below 2048.

The tag holds the kind `01` and the length minus 4 in bits 2 to 4.

Its bits 5 to 7 hold offset bits 8 to 10.

One byte after the tag holds the low eight bits of the offset.
-/
def copyOne (offset len : Nat) : List UInt8 :=
  [UInt8.ofNat (1 + (len - 4) * 4 + offset / 256 * 32), UInt8.ofNat (offset % 256)]

/-- A copy element with a two-byte offset, for a length of 1 to 64 and an offset below 65536.

The tag holds the kind `10` and the length minus 1 in its upper six bits.

Two little-endian bytes after the tag hold the offset.
-/
def copyTwo (offset len : Nat) : List UInt8 :=
  [UInt8.ofNat (2 + (len - 1) * 4), UInt8.ofNat (offset % 256), UInt8.ofNat (offset / 256)]

/-- The shortest copy element for a length of 1 to 64 and an offset below 65536. -/
def copyElement (offset len : Nat) : List UInt8 :=
  if 4 ≤ len ∧ len ≤ 11 ∧ offset < copyOneOffsetBound then copyOne offset len
  else copyTwo offset len

/-- Append copy elements of one offset that together copy `len` bytes.

Each element copies up to 64 bytes, and the last one copies what remains.
-/
def emitCopies (offset : Nat) (out : ByteArray) (len : Nat) : ByteArray :=
  if len = 0 then out
  else emitCopies offset (out ++ ⟨(copyElement offset (min len maxCopyLength)).toArray⟩)
    (len - min len maxCopyLength)
termination_by len
decreasing_by simp only [maxCopyLength]; omega

/-- Append the bytes of `src` from `lo` up to `hi` as one literal, or nothing if there are none. -/
def emitLiteral (out src : ByteArray) (lo hi : Nat) : ByteArray :=
  if lo < hi then out ++ ⟨(literal (src.extract lo hi).data.toList).toArray⟩ else out

end EthLib.Networking.Snappy
