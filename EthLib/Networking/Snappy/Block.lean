module

public import EthLib.Base.Length
public import EthLib.Base.LittleEndian

/-!
# `Networking.Snappy.Block`

Decompression of the Snappy block format.

Source: `format_description.txt` of `google/snappy`, at
<https://github.com/google/snappy/blob/7406111ac4ae539ea0db8b7ea2dc76730cd957f4/format_description.txt>.

Gossip on the consensus layer compresses every message with it.

A block is a preamble, then elements:

- The preamble is the uncompressed length, as a varint (§1).
- A literal is bytes copied straight to the output (§2.1).
- A copy repeats bytes already written, some distance back (§2.2).

The low two bits of an element's first byte, its tag, name its kind:

- `00`: a literal.
- `01`: a copy with a one-byte offset.
- `10`: a copy with a two-byte offset.
- `11`: a copy with a four-byte offset.

A peer controls every byte, so decompression is total and names each way a block can be malformed.

The output is a byte array, so a copy reads each of its bytes in one step.

A copy then costs its length, amortized, however far back it reaches.

The array grows as bytes arrive, and never reserves the declared length, which a peer controls.

The bytes of one literal element are here too, for the compressor and the proofs (§2.1).

The compressor, which writes literals and copies, is in its own module.
-/

@[expose] public section

namespace EthLib.Networking.Snappy

open EthLib.Base (bytesToUint uintToBytes)

/-- The most bytes the preamble may occupy.

The length is at most 2^32 - 1, and five groups of seven bits hold 35 bits (§1).
-/
def preambleMaxLength : Nat := 5

/-- The largest uncompressed length a block may declare (§1). -/
def maxUncompressedLength : Nat := 2 ^ 32 - 1

/-- The continuation bit of a preamble byte, `0x80`.

It is set on every preamble byte but the last.

The seven bits below it carry the value, so it is also the radix.
-/
def continuation : Nat := 128

/-- Every way decompression can reject its input. -/
inductive SnappyError where
  /-- The input ended inside the preamble. -/
  | preambleTruncated
  /-- The preamble did not end within five bytes. -/
  | preambleTooLong
  /-- The preamble declared more than 2^32 - 1 bytes. -/
  | preambleTooLarge (declared : Nat)
  /-- A literal, or its length bytes, ran past the end of the input. -/
  | literalPastEnd
  /-- The offset bytes of a copy ran past the end of the input. -/
  | copyPastEnd
  /-- A copy with offset zero, which the format forbids (§2.2). -/
  | copyOffsetZero
  /-- A copy reaching before the first byte of the output (§2.2). -/
  | copyOffsetTooLarge (offset : Nat)
  /-- The output stops short of the declared length, or an element would take it past. -/
  | lengthMismatch (declared actual : Nat)
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

A new constructor takes a new code, so that each code keeps its meaning. -/
def SnappyError.code : SnappyError → UInt32
  | .preambleTruncated => 1
  | .preambleTooLong => 2
  | .preambleTooLarge _ => 3
  | .literalPastEnd => 4
  | .copyPastEnd => 5
  | .copyOffsetZero => 6
  | .copyOffsetTooLarge _ => 7
  | .lengthMismatch .. => 8

/-- Read the preamble, at most `fuel` more bytes deep.

Returns the length and the bytes after the preamble.

# Why no minimal encoding

The format sets no minimality rule.

So `80 00` is a valid preamble for the length zero.

The consensus-layer varint rejects it, so this reader is separate.
-/
def readPreambleAux : List UInt8 → Nat → Nat → Nat → Except SnappyError (Nat × List UInt8)
  | [], _, _, _ => .error .preambleTruncated
  -- Five bytes all carried the continuation bit.
  | _ :: _, _, _, 0 => .error .preambleTooLong
  | b :: bs, acc, shift, fuel + 1 =>
      -- Add this byte's seven value bits at their place.
      let acc := acc + (b.toNat % continuation) * 2 ^ shift
      if b.toNat < continuation then
        .ok (acc, bs)
      else
        readPreambleAux bs acc (shift + 7) fuel

/-- The uncompressed length a block declares, and the bytes after the preamble (§1). -/
def readPreamble (bs : List UInt8) : Except SnappyError (Nat × List UInt8) :=
  match readPreambleAux bs 0 0 preambleMaxLength with
  | .error e => .error e
  | .ok (len, rest) =>
      -- Five bytes hold 35 bits, so the range is checked separately.
      if maxUncompressedLength < len then
        .error (.preambleTooLarge len)
      else
        .ok (len, rest)

/-- The uncompressed length a block declares, read from its first bytes alone (§1).

The preamble takes at most five bytes, so this reads no more, and decompresses nothing. -/
def declaredLength (bs : ByteArray) : Except SnappyError Nat :=
  (readPreamble (bs.extract 0 preambleMaxLength).toList).map (·.1)

/-- Copy the given number of bytes from `offset` back onto the end of the output (§2.2).

Each byte is read `offset` back from the current end.

So a copy longer than its offset reads bytes it has written, and repeats itself, as §2.2 allows.

An offset of 0 reads the most recent byte, as an offset of 1 does. -/
def copyBytes (out : ByteArray) (offset : Nat) : Nat → Except SnappyError ByteArray
  | 0 => .ok out
  | len + 1 =>
      if h : max offset 1 ≤ out.size then
        copyBytes (out.push out[out.size - max offset 1]) offset len
      else
        -- The copy reaches before the first byte written.
        .error (.copyOffsetTooLarge offset)

-- Each length an element declares is checked in as many steps as that length.
attribute [local instance high] Base.Length.decideLeLength Base.Length.decideLengthLt

/-- Decode the elements of a block onto the end of the output, up to the declared length.

An element that would take the output past the declared length is rejected before it is written.

So the output never holds more than the declared length.

The fuel bounds the number of elements.

Each element takes at least its tag byte, so the input length is enough fuel.
-/
def decompressElements (declared : Nat) :
    List UInt8 → ByteArray → Nat → Except SnappyError ByteArray
  | [], out, _ => .ok out
  -- Out of fuel: unreachable when the fuel is at least the input length.
  | _ :: _, _, 0 => .error .literalPastEnd
  | tag :: rest, out, fuel + 1 =>
      -- The element kind, and the six bits above it.
      let t := tag.toNat % 4
      let upper := tag.toNat / 4
      if t == 0 then
        -- A literal of up to 60 bytes stores its length minus one in the tag (§2.1).
        if upper < 60 then
          let len := upper + 1
          if rest.length < len then
            .error .literalPastEnd
          else if declared < out.size + len then
            .error (.lengthMismatch declared (out.size + len))
          else
            decompressElements declared (rest.drop len) (out ++ (rest.take len).toByteArray) fuel
        -- Tags 60 to 63 say that 1 to 4 little-endian bytes hold the length minus one (§2.1).
        else
          let extra := upper - 59
          if rest.length < extra then
            .error .literalPastEnd
          else
            let len := bytesToUint (rest.take extra).toArray.toVector + 1
            let rest := rest.drop extra
            if rest.length < len then
              .error .literalPastEnd
            else if declared < out.size + len then
              .error (.lengthMismatch declared (out.size + len))
            else
              decompressElements declared (rest.drop len) (out ++ (rest.take len).toByteArray) fuel
      else
        -- A copy: the tag fixes the width of the offset (§2.2.1 to §2.2.3).
        let width := if t == 1 then 1 else if t == 2 then 2 else 4
        -- The length minus 4 is in tag bits 2 to 4 for a one-byte offset, else the length minus 1.
        let len := if t == 1 then 4 + upper % 8 else upper + 1
        if rest.length < width then
          .error .copyPastEnd
        else
          -- A one-byte-offset copy keeps the top three of its 11 offset bits in tag bits 5 to 7.
          let offset :=
            if t == 1 then upper / 8 * 256 + bytesToUint (rest.take 1).toArray.toVector
            else bytesToUint (rest.take width).toArray.toVector
          if offset == 0 then
            .error .copyOffsetZero
          else if declared < out.size + len then
            .error (.lengthMismatch declared (out.size + len))
          else
            match copyBytes out offset len with
            | .error e => .error e
            | .ok out => decompressElements declared (rest.drop width) out fuel

/-- The byte array that a Snappy block, read as a list, decompresses to, or why it is not valid. -/
def decompressToArray (bs : List UInt8) : Except SnappyError ByteArray :=
  match readPreamble bs with
  | .error e => .error e
  | .ok (declared, rest) =>
      match decompressElements declared rest ByteArray.empty rest.length with
      | .error e => .error e
      | .ok out =>
          -- The output must have exactly the declared length: no truncation, no padding.
          if out.size == declared then
            .ok out
          else
            .error (.lengthMismatch declared out.size)

/-- The bytes a Snappy block decompresses to, as a list, or why it is not a valid block. -/
def decompressList (bs : List UInt8) : Except SnappyError (List UInt8) :=
  (decompressToArray bs).map fun out => out.data.toList

/-- The bytes a Snappy block decompresses to, or why it is not a valid block. -/
def decompress (bs : ByteArray) : Except SnappyError ByteArray :=
  decompressToArray bs.toList

/-- The fewest bytes that hold `n` little-endian, for `n < 2^32` (§2.1). -/
def literalLengthBytes (n : Nat) : Nat :=
  if n < 2 ^ 8 then 1 else if n < 2 ^ 16 then 2 else if n < 2 ^ 24 then 3 else 4

/-- The tag and the length bytes of a literal of `n` bytes, for `n` from 1 to 2^32 (§2.1).

A length up to 60 sits in the tag as the length minus one.

A longer length is written, minus one, in 1 to 4 bytes after the tag.

The six upper bits of the tag then hold 59 plus that count, so 60 to 63.
-/
def literalHeader (n : Nat) : List UInt8 :=
  if n - 1 < 60 then
    [UInt8.ofNat ((n - 1) * 4)]
  else
    let k := literalLengthBytes (n - 1)
    UInt8.ofNat ((59 + k) * 4) :: (uintToBytes k (n - 1)).toList

/-- One literal element that holds `data`, of 1 to 2^32 bytes: its header, then the data (§2.1). -/
def literal (data : List UInt8) : List UInt8 :=
  literalHeader data.length ++ data

end EthLib.Networking.Snappy
