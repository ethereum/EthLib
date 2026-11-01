module

/-!
# `Networking.Snappy.Block`

Decompression of the Snappy block format.

The format is [`format_description.txt`](https://github.com/google/snappy/blob/7406111ac4ae539ea0db8b7ea2dc76730cd957f4/format_description.txt) of `google/snappy`.

Gossip on the consensus layer compresses every message with it, per [`phase0/p2p-interface.md`](https://github.com/ethereum/consensus-specs/blob/55a48db47eff748266187888f01227940e3e7e64/specs/phase0/p2p-interface.md#encodings), "Encodings".

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

The output is kept most recent byte first.

A copy that reaches k bytes back then reads index k - 1.

The result is reversed once at the end.

The code is written for clarity, not speed.

Compression is out of scope.
-/

@[expose] public section

namespace EthLib.Networking.Snappy

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
  /-- The output length differs from the length the preamble declared. -/
  | lengthMismatch (declared actual : Nat)
  deriving Repr, DecidableEq

/-- Bytes read as a little-endian number. -/
def leValue : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leValue bs

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

/-- Copy `n` bytes from `offset` back onto the output, most recent byte first.

Each byte is read after the previous one is written.

So a copy longer than its offset repeats its own output, as §2.2 allows.
-/
def copyBytes (out : List UInt8) (offset : Nat) : Nat → Except SnappyError (List UInt8)
  | 0 => .ok out
  | n + 1 =>
      match out[offset - 1]? with
      -- Fewer than `offset` bytes are written so far.
      | none => .error (.copyOffsetTooLarge offset)
      | some b => copyBytes (b :: out) offset n

/-- Decode the elements of a block onto the output, most recent byte first.

The fuel bounds the number of elements.

Each element takes at least its tag byte, so the input length is enough fuel.
-/
def decompressElements : List UInt8 → List UInt8 → Nat → Except SnappyError (List UInt8)
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
          else
            decompressElements (rest.drop len) ((rest.take len).reverse ++ out) fuel
        -- Tags 60 to 63 say that 1 to 4 little-endian bytes hold the length minus one (§2.1).
        else
          let extra := upper - 59
          if rest.length < extra then
            .error .literalPastEnd
          else
            let len := leValue (rest.take extra) + 1
            let rest := rest.drop extra
            if rest.length < len then
              .error .literalPastEnd
            else
              decompressElements (rest.drop len) ((rest.take len).reverse ++ out) fuel
      else
        -- A copy: the tag fixes the width of the offset (§2.2.1 to §2.2.3).
        let width := if t == 1 then 1 else if t == 2 then 2 else 4
        -- A one-byte-offset copy holds the length minus four in tag bits 2 to 4.
        -- The other copies hold the length minus one in the six upper bits.
        let len := if t == 1 then 4 + upper % 8 else upper + 1
        if rest.length < width then
          .error .copyPastEnd
        else
          -- A one-byte-offset copy keeps the top three of its 11 offset bits in tag bits 5 to 7.
          let offset :=
            if t == 1 then upper / 8 * 256 + leValue (rest.take 1)
            else leValue (rest.take width)
          if offset == 0 then
            .error .copyOffsetZero
          else
            match copyBytes out offset len with
            | .error e => .error e
            | .ok out => decompressElements (rest.drop width) out fuel

/-- The bytes a Snappy block decompresses to, or why it is not a valid block. -/
def decompressList (bs : List UInt8) : Except SnappyError (List UInt8) :=
  match readPreamble bs with
  | .error e => .error e
  | .ok (declared, rest) =>
      match decompressElements rest [] rest.length with
      | .error e => .error e
      | .ok out =>
          -- The output must have exactly the declared length: no truncation, no padding.
          if out.length == declared then
            .ok out.reverse
          else
            .error (.lengthMismatch declared out.length)

/-- The bytes a Snappy block decompresses to, or why it is not a valid block. -/
def decompress (bs : ByteArray) : Except SnappyError ByteArray :=
  (decompressList bs.toList).map fun out => ⟨out.toArray⟩

end EthLib.Networking.Snappy
