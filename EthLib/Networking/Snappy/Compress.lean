module

public import EthLib.Networking.Snappy.Encode

/-!
# `Networking.Snappy.Compress`

Compression to the Snappy block format.

Source: `format_description.txt` of `google/snappy`, at
<https://github.com/google/snappy/blob/7406111ac4ae539ea0db8b7ea2dc76730cd957f4/format_description.txt>.

The format leaves the choice of copies to the compressor (§2).

So many blocks decompress to one input.

This compressor scans the input once, from the front:

- A table of 2^14 slots maps a hash of four bytes to the last position that began with them.
- At each position, the table proposes an earlier position.
- A proposal counts when it lies less than 65536 bytes back and agrees with the input on at least
  four bytes.
- The bytes since the last copy are then written as one literal, followed by the copy.
- Without a proposal that counts, the scan moves one byte on.

The table is a hint.

The compressor reads the input to find how far a proposal agrees.

So a wrong proposal costs compression and never correctness.

A copy of one offset longer than 64 bytes is written as several copies.

The size of the input must stay below 2^32, which a preamble can declare (§1).
-/

@[expose] public section

namespace EthLib.Networking.Snappy

/-- The number of slots of the table of positions, 2^14. -/
def tableBits : Nat := 14

/-- The offsets of copies stay below this bound, which a two-byte offset holds (§2.2.2). -/
def window : Nat := copyTwoOffsetBound

/-- The fewest bytes of agreement for which a copy is worth writing. -/
def minMatch : Nat := 4

/-- The slot of the four bytes that start at `i`: the high bits of a multiple of their number.

The multiplier is odd, so it mixes the low bytes into the high bits.
-/
def slot (src : ByteArray) (i : Nat) (h : i + 4 ≤ src.size) : Nat :=
  let word := src[i].toNat + 256 * src[i + 1].toNat + 65536 * src[i + 2].toNat +
    16777216 * src[i + 3].toNat
  word * 506832829 % 2 ^ 32 / 2 ^ (32 - tableBits)

/-- How many bytes from `j` agree with the bytes from `c`, for a position `c` before `j`.

The count stops at the end of the input.

The bytes from `c` may run past `j`, since a copy may overlap what it writes (§2.2).
-/
def matchLength (src : ByteArray) (c j : Nat) (hc : c < j) : Nat :=
  if h : j < src.size then
    if src[c]'(by omega) = src[j] then matchLength src (c + 1) (j + 1) (by omega) + 1 else 0
  else 0
termination_by src.size - j

/-- The block of `src` from position `i` on, appended to `out`.

The bytes from `lit` up to `i` have not been written.

The table holds a position for each slot, from which the scan proposes a copy.
-/
def compressLoop (src : ByteArray) (table : Array Nat) (i lit : Nat) (out : ByteArray) :
    ByteArray :=
  if h : i + minMatch ≤ src.size then
    let s := slot src i h
    let c := table.getD s 0
    let table := table.setIfInBounds s i
    if hc : c < i ∧ i - c < window then
      if hl : minMatch ≤ matchLength src c i hc.1 then
        compressLoop src table (i + matchLength src c i hc.1) (i + matchLength src c i hc.1)
          (emitCopies (i - c) (emitLiteral out src lit i) (matchLength src c i hc.1))
      else compressLoop src table (i + 1) lit out
    else compressLoop src table (i + 1) lit out
  else emitLiteral out src lit src.size
termination_by src.size - i
decreasing_by all_goals (have : minMatch = 4 := rfl; (try simp only [s, c] at *); omega)

/-- A Snappy block of `src`: the length as a varint, then literals and copies.

The input has at most 2^32 - 1 bytes, the most a preamble may declare (§1).
-/
def compress (src : ByteArray) : ByteArray :=
  ⟨(EthLib.Networking.Encoding.Varint.encodeAux src.size preambleMaxLength).toArray⟩ ++
    compressLoop src (Array.replicate (2 ^ tableBits) 0) 0 0 ByteArray.empty

end EthLib.Networking.Snappy
