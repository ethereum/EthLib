module

public import EthLib.Networking.Encoding.Varint
public import EthLib.Networking.Snappy.Encode

/-!
# `Networking.Snappy.Compress`

Compression to the Snappy block format.

Source: [`format_description.txt`][format] of `google/snappy`.

Its opening text describes the format, and not how the compressor works.

So one input has many valid blocks.

This compressor scans the input once, from the front:

- A table of 2^14 slots maps the hash of four bytes to the last scanned position with that hash.
- At each position, the table proposes an earlier position.
- A proposal counts if it lies less than 65536 bytes back and matches at least four bytes.
- The bytes since the last copy are then written as one literal, followed by the copy.
- The scan then goes on from the end of the copy.
- Without a proposal that counts, the scan moves one byte on.
- At the end of the input, the bytes since the last copy are written as one literal.

The table is a hint.

The compressor reads the input to find how far a proposal matches.

So a wrong proposal costs only compression, never correctness.

A match longer than 64 bytes is written as several copies of one offset (§2.2.2).

The input must have at most 2^32 - 1 bytes, the largest length that a preamble can declare (§1).

A longer input gives a preamble out of range, so decompression rejects the block.

[format]: https://github.com/google/snappy/blob/7406111ac4ae539ea0db8b7ea2dc76730cd957f4/format_description.txt
-/

@[expose] public section

namespace EthLib.Networking.Snappy

/-- The number of bits of a slot of the table of positions.

The table of positions has 2^14 slots, so a slot has 14 bits.
-/
def tableBits : Nat := 14

/-- The fewest matching bytes for which the compressor writes a copy.

A copy element takes two or three bytes, so a shorter copy saves nothing.
-/
def minCopyLength : Nat := 4

/-- The slot of the four bytes that start at `i`: the top 14 bits of a 32-bit product.

The four bytes, read little-endian, are multiplied by 0x1e35a7bd modulo 2^32.

The reference compressor also hashes with this multiplier and the upper bits of the product.

See `TableEntry` of [`snappy.cc`][snappy.cc].

[snappy.cc]: https://github.com/google/snappy/blob/7406111ac4ae539ea0db8b7ea2dc76730cd957f4/snappy.cc
-/
def hashSlot (src : ByteArray) (i : Nat) (h : i + 4 ≤ src.size) : Nat :=
  let word := src[i].toNat + 256 * src[i + 1].toNat + 65536 * src[i + 2].toNat +
    16777216 * src[i + 3].toNat
  word * 0x1e35a7bd % 2 ^ 32 / 2 ^ (32 - tableBits)

/-- How many bytes from `j` agree with the bytes from `c`, for a position `c` before `j`.

The count stops at the end of the input.

The bytes from `c` may run past `j`, since a copy may overlap what it writes (§2.2).

The count `m` grows by one per agreeing byte, so a long match runs as a loop on a constant stack.
-/
def matchLength (src : ByteArray) (c j : Nat) (hc : c < j) (m : Nat := 0) : Nat :=
  if h : j + m < src.size then
    if src[c + m]'(by omega) = src[j + m] then matchLength src c j hc (m + 1) else m
  else m
termination_by src.size - (j + m)

/-- Append to `out` the elements for the bytes of `src` from `lit` on, with the scan at `i`.

The bytes from `lit` up to `i` wait for a literal or a copy.

The table holds a position for each slot, from which the scan proposes a copy.
-/
def compressLoop (src : ByteArray) (table : Array Nat) (i lit : Nat) (out : ByteArray) :
    ByteArray :=
  if h : i + minCopyLength ≤ src.size then
    let s := hashSlot src i h
    let c := table.getD s 0
    let table := table.setIfInBounds s i
    if hc : c < i ∧ i - c < copyTwoOffsetBound then
      -- The match length, computed once for this step.
      let len := matchLength src c i hc.1
      if hl : minCopyLength ≤ len then
        compressLoop src table (i + len) (i + len)
          (emitCopies (i - c) (emitLiteral out src lit i) len)
      else compressLoop src table (i + 1) lit out
    else compressLoop src table (i + 1) lit out
  else emitLiteral out src lit src.size
termination_by src.size - i
decreasing_by all_goals (have : minCopyLength = 4 := rfl; (try simp only [s, c, len] at *); omega)

/-- A Snappy block of the input: the length as a varint, then literals and copies.

The input must have at most 2^32 - 1 bytes, the largest length that a preamble can declare (§1).

A longer input gives a preamble out of range, so decompression rejects the block.
-/
def compress (src : ByteArray) : ByteArray :=
  ⟨(EthLib.Networking.Encoding.Varint.encodeAux src.size preambleMaxLength).toArray⟩ ++
    compressLoop src (Array.replicate (2 ^ tableBits) 0) 0 0 ByteArray.empty

end EthLib.Networking.Snappy
