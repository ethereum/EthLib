module

public import EthLib.Networking.Snappy.Block

/-!
# `Networking.Snappy.Encode`

The elements that a Snappy compressor writes, from `format_description.txt` of `google/snappy`:
<https://github.com/google/snappy/blob/7406111ac4ae539ea0db8b7ea2dc76730cd957f4/format_description.txt>.

- A copy with a one-byte offset holds a length of 4 to 11 and an offset of 1 to 2047 (§2.2.1).
- A copy with a two-byte offset holds a length of 1 to 64 and an offset of 1 to 65535 (§2.2.2).
- A literal of 1 to 2^32 bytes holds its data unchanged (§2.1).

This file only writes elements, and it never decides which bytes to copy.
-/

@[expose] public section

namespace EthLib.Networking.Snappy

/-- The most bytes that one copy element copies.

A copy with a two-byte or four-byte offset copies up to 64 bytes (§2.2.2, §2.2.3).
-/
def maxCopyLength : Nat := 64

/-- The offsets below this bound fit a copy with a one-byte offset (§2.2.1).

The offset of such a copy has 11 bits: eight after the tag, and three in the tag.
-/
def copyOneOffsetBound : Nat := 2048

/-- The offsets below this bound fit a copy with a two-byte offset (§2.2.2). -/
def copyTwoOffsetBound : Nat := 65536

/-- A copy element with a one-byte offset, for a length of 4 to 11 and an offset of 1 to 2047.

Its layout is that of §2.2.1.
-/
def copyOne (offset len : Nat) : List UInt8 :=
  -- §2.2.1: the tag holds the type 01, then len - 4 in bits 2 to 4.
  --
  -- Its bits 5 to 7 hold the upper three of the 11 offset bits.
  --
  -- The lower eight bits of the offset are stored in a byte following the tag byte.
  [UInt8.ofNat (1 + (len - 4) * 4 + offset / 256 * 32), UInt8.ofNat (offset % 256)]

/-- A copy element with a two-byte offset, for a length of 1 to 64 and an offset of 1 to 65535.

Its layout is that of §2.2.2.
-/
def copyTwo (offset len : Nat) : List UInt8 :=
  -- §2.2.2: the tag holds the type 10, and len - 1 in its upper six bits, bits 2 to 7.
  --
  -- The offset is a little-endian 16-bit integer in the two bytes following the tag byte.
  [UInt8.ofNat (2 + (len - 1) * 4), UInt8.ofNat (offset % 256), UInt8.ofNat (offset / 256)]

/-- The shortest copy element for a length of 1 to 64 and an offset of 1 to 65535.

An offset of 0 can be encoded, but it is not legal (§2.2).

Other arguments give an element that does not encode them.

The decoder reads these bytes back as the copy they were written for. -/
def copyElement (offset len : Nat) : List UInt8 :=
  -- §2.2.1 takes two bytes and §2.2.2 takes three, when the length and offset fit both.
  --
  -- The format lets a compressor choose either, and EthLib writes the shorter.
  if 4 ≤ len ∧ len ≤ 11 ∧ offset < copyOneOffsetBound then copyOne offset len
  else copyTwo offset len

/-- Append copy elements of one offset that together copy `len` bytes.

An element copies 64 bytes while at least 68 remain, then 60 if more than 64 remain.

The last element copies the rest, so 4 to 64 bytes when `len` is at least 4.

The reference compressor splits a copy the same way, in `EmitCopy` of [`snappy.cc`][snappy.cc].

[snappy.cc]: https://github.com/google/snappy/blob/7406111ac4ae539ea0db8b7ea2dc76730cd957f4/snappy.cc
-/
def emitCopies (offset : Nat) (out : ByteArray) (len : Nat) : ByteArray :=
  if len = 0 then out
  else
    -- §2.2.2: one element copies at most 64 bytes.
    --
    -- Leave at least four bytes for the last element.
    let n :=
      if maxCopyLength + 4 ≤ len then maxCopyLength
      else if maxCopyLength < len then maxCopyLength - 4
      else len
    emitCopies offset (out ++ ⟨(copyElement offset n).toArray⟩) (len - n)
termination_by len
decreasing_by simp only [maxCopyLength]; grind

/-- Append the bytes of `src` from `lo` up to `hi` as one literal, or nothing if there are none.

A literal holds 1 to 2^32 bytes (§2.1).
-/
def emitLiteral (out src : ByteArray) (lo hi : Nat) : ByteArray :=
  if lo < hi then
    -- §2.1: the tag and the length of the literal.
    let out := out ++ ⟨(literalHeader (hi - lo)).toArray⟩
    -- §2.1: then the literal itself, unchanged, from `src` straight to the end of the output.
    src.copySlice lo out out.size (hi - lo) false
  else out

end EthLib.Networking.Snappy
