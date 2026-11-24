module

public import EthLib.Base.ByteOrder
public import EthLib.Networking.Encoding.Varint

/-!
# `Networking.Snappy.Block`

Decompression of the Snappy block format, with which consensus gossip compresses every message.

Source: [`format_description.txt`][format] of `google/snappy`, §1 and §2.

[format]: https://github.com/google/snappy/blob/7406111ac4ae539ea0db8b7ea2dc76730cd957f4/format_description.txt
-/

@[expose] public section

namespace EthLib.Networking.Snappy

open EthLib.Base (ByteOrder.ofLE ByteOrder.toLE)

/-- The most bytes the preamble may occupy.

The length is at most 2^32 - 1, and five groups of seven bits hold 35 bits (§1).
-/
def preambleMaxLength : Nat := 5

/-- The largest uncompressed length a block may declare (§1). -/
def maxUncompressedLength : Nat := 2 ^ 32 - 1

/-- Every way decompression can reject its input.

A peer controls every byte, so decompression is total and names each way a block can be malformed.
-/
inductive SnappyError where
  /-- The input ended inside the preamble. -/
  | preambleTruncated
  /-- The preamble did not end within five bytes. -/
  | preambleTooLong
  /-- The preamble declared more than 2^32 - 1 bytes. -/
  | preambleTooLarge (declared : Nat)
  /-- A literal, or its length bytes, ran past the end of the input.

  It needs `needed` more input bytes for its length or its data, and only `available` remain. -/
  | literalPastEnd (needed available : Nat)
  /-- The offset bytes of a copy ran past the end of the input.

  The copy needs `needed` offset bytes, and `available` are left after its tag. -/
  | copyPastEnd (needed available : Nat)
  /-- A copy with offset zero, which the format forbids (§2.2).

  The copy would have started at the output position `position`. -/
  | copyOffsetZero (position : Nat)
  /-- A copy reaching before the first byte of the output (§2.2).

  The copy reaches `offset` bytes back, at least one, and the output holds only `written` bytes. -/
  | copyOffsetTooLarge (offset written : Nat)
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
  | .literalPastEnd .. => 4
  | .copyPastEnd .. => 5
  | .copyOffsetZero _ => 6
  | .copyOffsetTooLarge .. => 7
  | .lengthMismatch .. => 8

/-- The uncompressed length a block declares, and the bytes after the preamble (§1). -/
def readPreamble (bs : List UInt8) : Except SnappyError (Nat × List UInt8) :=
  -- §1: given the maximum 2^32 - 1, 5 bytes are sufficient for any value.
  let window := bs.take preambleMaxLength
  -- §1: the upper bit of a byte is set iff there are more bytes, so the last byte has it clear.
  let last := window.findIdx (·.toNat < Encoding.Varint.continuation)
  if last < window.length then
    -- §1: the lower 7 bits of each byte are data, little-endian.
    --
    -- The format sets no minimality rule, so 0x80 0x00 is a valid preamble for the length zero.
    --
    -- The consensus-layer varint rejects it, and this reader takes the value with no such check.
    let len := Encoding.Varint.valueOf (bs.take (last + 1))
    -- §1: the length is at most 2^32 - 1.
    --
    -- Five bytes hold 35 bits, so the range is checked separately.
    if maxUncompressedLength < len then
      .error (.preambleTooLarge len)
    else
      .ok (len, bs.drop (last + 1))
  -- No last byte among the first five: too long if a sixth byte follows, else truncated.
  --
  -- §1 names neither failure.
  --
  -- A sixth byte exceeds the 5 bytes of §1, and an early end leaves the varint unfinished.
  else if preambleMaxLength < bs.length then
    .error .preambleTooLong
  else
    .error .preambleTruncated

/-- The uncompressed length a block declares, read from its first bytes alone (§1).

The preamble takes at most five bytes, so this reads no more, and decompresses nothing. -/
def declaredLength (bs : ByteArray) : Except SnappyError Nat :=
  (readPreamble (bs.extract 0 preambleMaxLength).toList).map (·.1)

/-- Copy the given number of bytes from `offset` back onto the end of the output (§2.2).

The output is a byte array, so the copy reads each of its bytes in one step.

A copy then costs its length, amortized, however far back it reaches. -/
def copyBytes (out : ByteArray) (offset : Nat) : Nat → Except SnappyError ByteArray
  | 0 => .ok out
  | len + 1 =>
      -- §2.2: offset > current decompressed position is not allowed.
      --
      -- So the block cannot start with a copy, as §2 says.
      --
      -- Not in §2.2: an offset of 0, which is not legal, reads as 1, so the index stays in range.
      --
      -- The decoder of the elements rejects that offset before it calls this copy.
      if h : max offset 1 ≤ out.size then
        -- §2.2: the next byte is the one `offset` bytes back from the current position.
        --
        -- A length larger than the offset reads bytes this copy wrote: the run-length form of §2.2.
        copyBytes (out.push out[out.size - max offset 1]) offset len
      else
        -- The copy reaches before the first byte written.
        .error (.copyOffsetTooLarge offset out.size)

/-- Whether a list has at least `n` elements, read in at most `n` steps.

A decoder checks each length it reads against the rest of its input.

Reading the whole rest each time would make a long input cost time quadratic in its length.

A decoder that opens the instances below locally pays only the bound at each check. -/
def hasAtLeast {α : Type} : Nat → List α → Bool
  -- Any list has at least zero elements, so the rest is never read.
  | 0, _ => true
  | _ + 1, [] => false
  -- One element meets one unit of the bound.
  | n + 1, _ :: rest => hasAtLeast n rest

/-- The check reads the length of the list against the bound. -/
theorem hasAtLeast_iff {α : Type} (n : Nat) (l : List α) :
    hasAtLeast n l = true ↔ n ≤ l.length := by
  induction n generalizing l with
  | zero => simp [hasAtLeast]
  | succ n ih => cases l <;> simp [hasAtLeast, ih]

/-- A list at least as long as a bound, decided in as many steps as the bound. -/
@[instance_reducible] def decideLeLength {α : Type} (n : Nat) (l : List α) :
    Decidable (n ≤ l.length) :=
  decidable_of_iff _ (hasAtLeast_iff n l)

/-- A list shorter than a bound, decided in as many steps as the bound. -/
@[instance_reducible] def decideLengthLt {α : Type} (l : List α) (n : Nat) :
    Decidable (l.length < n) :=
  decidable_of_iff (¬ hasAtLeast n l = true) (by rw [hasAtLeast_iff]; omega)

-- Each length an element declares is checked in as many steps as that length.
attribute [local instance high] decideLeLength decideLengthLt

/-- Decode the elements of a block onto the end of the output, up to the declared length.

An element that would take the output past that length is rejected before it is written.

So the output never holds more than the declared length.

The fuel bounds the number of elements.
-/
def decompressElements (declared : Nat) :
    List UInt8 → ByteArray → Nat → Except SnappyError ByteArray
  | [], out, _ => .ok out
  -- Out of fuel: unreachable when the fuel is at least the input length.
  --
  -- Each element takes at least its tag byte, so the input length is enough fuel.
  --
  -- The fields of this error are therefore arbitrary.
  | l@(_ :: _), _, 0 => .error (.literalPastEnd (l.length + 1) l.length)
  | tag :: rest, out, fuel + 1 =>
      -- §2: the lower two bits of the tag byte give the type of the element.
      let t := tag.toNat % 4
      -- §2: the upper six bits of the tag are element-dependent.
      let upper := tag.toNat / 4
      -- §2: type 00 is a literal (§2.1).
      if t == 0 then
        -- §2.1: for a literal of up to 60 bytes, the upper six bits of the tag hold len - 1.
        if upper < 60 then
          let len := upper + 1
          -- §2.1: the literal follows immediately, so the input must hold its len bytes.
          if rest.length < len then
            .error (.literalPastEnd len rest.length)
          -- Not in §2: an element that takes the output past the declared length is rejected.
          --
          -- The check comes before the write, so the output never exceeds the length of §1.
          else if declared < out.size + len then
            .error (.lengthMismatch declared (out.size + len))
          else
            -- §2.1: the len bytes go to the output unchanged.
            decompressElements declared (rest.drop len) (out ++ (rest.take len).toByteArray) fuel
        -- §2.1: upper six bits of 60, 61, 62 or 63 say that 1 to 4 bytes hold len - 1.
        --
        -- Not in §2.1: this form is read for any len, also for one of 60 bytes or fewer.
        else
          let extra := upper - 59
          if rest.length < extra then
            .error (.literalPastEnd extra rest.length)
          else
            -- §2.1: len - 1 is stored after the tag byte, little-endian.
            let len := ByteOrder.ofLE (rest.take extra).toArray.toVector + 1
            let rest := rest.drop extra
            -- §2.1: the literal itself follows after the length.
            if rest.length < len then
              .error (.literalPastEnd len rest.length)
            -- Not in §2: the same check against the declared length as for a short literal.
            else if declared < out.size + len then
              .error (.lengthMismatch declared (out.size + len))
            else
              decompressElements declared (rest.drop len) (out ++ (rest.take len).toByteArray) fuel
      else
        -- §2: types 01, 10 and 11 are copies with a 1-byte, 2-byte or 4-byte offset.
        let width := if t == 1 then 1 else if t == 2 then 2 else 4
        -- §2.2.1: len - 4 is stored in bits 2 to 4 of the tag byte.
        --
        -- §2.2.2 and §2.2.3: len - 1 is stored in the upper six bits, bits 2 to 7, of the tag byte.
        let len := if t == 1 then 4 + upper % 8 else upper + 1
        if rest.length < width then
          .error (.copyPastEnd width rest.length)
        else
          -- §2.2.1: the offset has 11 bits, the upper three in tag bits 5 to 7.
          --
          -- The lower eight are in the byte after the tag.
          --
          -- §2.2.2 and §2.2.3: the offset is a little-endian 16-bit or 32-bit integer.
          let offset :=
            if t == 1 then upper / 8 * 256 + ByteOrder.ofLE (rest.take 1).toArray.toVector
            else ByteOrder.ofLE (rest.take width).toArray.toVector
          -- §2.2: offsets of zero can be encoded, but are not legal.
          if offset == 0 then
            .error (.copyOffsetZero out.size)
          -- Not in §2.2: the same check against the declared length as for a literal.
          else if declared < out.size + len then
            .error (.lengthMismatch declared (out.size + len))
          else
            -- §2.2: copy len bytes from offset bytes back, which must not pass the first byte.
            match copyBytes out offset len with
            | .error e => .error e
            | .ok out => decompressElements declared (rest.drop width) out fuel

/-- The byte array that a Snappy block, read as a list, decompresses to, or why it is not valid. -/
def decompressToArray (bs : List UInt8) : Except SnappyError ByteArray :=
  -- §1: the block starts with the uncompressed length.
  match readPreamble bs with
  | .error e => .error e
  | .ok (declared, rest) =>
      -- §2: then elements in any order, up to the end of the input.
      --
      -- A block is thus a preamble that declares the uncompressed length, then literals and copies.
      --
      -- The array grows as bytes arrive, and never reserves the declared length, set by a peer.
      --
      -- Each element takes at least its tag byte, so the input length is enough fuel.
      match decompressElements declared rest ByteArray.empty rest.length with
      | .error e => .error e
      | .ok out =>
          -- §1: the preamble is the uncompressed length.
          --
          -- So the output must have exactly the declared length: no truncation, no padding.
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
  -- §2.1 lets 1 to 4 bytes hold len - 1, and EthLib writes the fewest.
  if n < 2 ^ 8 then 1 else if n < 2 ^ 16 then 2 else if n < 2 ^ 24 then 3 else 4

/-- The tag and the length bytes of a literal of `n` bytes, for `n` from 1 to 2^32 (§2.1). -/
def literalHeader (n : Nat) : List UInt8 :=
  -- §2.1: for len up to 60, the upper six bits of the tag hold len - 1, above the type 00.
  if n - 1 < 60 then
    [UInt8.ofNat ((n - 1) * 4)]
  -- §2.1: for a longer literal, len - 1 is stored after the tag byte, little-endian.
  else
    let k := literalLengthBytes (n - 1)
    -- §2.1: the upper six bits of the tag are 60, 61, 62 or 63 for 1 to 4 bytes, so 59 + k.
    UInt8.ofNat ((59 + k) * 4) :: (ByteOrder.toLE k (n - 1)).toList

/-- One literal element that holds `data`, of 1 to 2^32 bytes (§2.1).

It is here for the proofs and the compressor, which writes literals and copies in its own module. -/
def literal (data : List UInt8) : List UInt8 :=
  -- §2.1: the tag and the length, then the literal itself.
  literalHeader data.length ++ data

end EthLib.Networking.Snappy
