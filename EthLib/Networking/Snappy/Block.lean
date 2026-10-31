module

/-!
# `Networking.Snappy.Block`

Decompression of Snappy's block format, which gossip messages on the
consensus layer are compressed with.

A block is the length of the uncompressed data as a varint, followed by
elements. Each element is either a literal, copied straight out, or a copy
of bytes already written:

```text
tag & 3 = 00   literal
tag & 3 = 01   copy, 1-byte offset
tag & 3 = 10   copy, 2-byte offset
tag & 3 = 11   copy, 4-byte offset
```

Source: `format_description.txt` in `google/snappy`.

A decoder reads untrusted bytes from any peer, so it is total and rejects
every malformed input with a typed error. Compression is out of scope.

## The output is accumulated in reverse

`decompressElements` carries the bytes written so far with the most recent
first. A copy reaches `offset` bytes back, which in that order is simply
index `offset - 1`, and a copy longer than its offset re-reads bytes this
same copy has just written — which is what the format calls for, and what
makes a run of one byte expand. The result is reversed once at the end.
-/

@[expose] public section

namespace EthLib.Networking.Snappy

/-- The most bytes the preamble may occupy.

The uncompressed length is a `uint32`, and five groups of seven bits cover
thirty-five. -/
def preambleMaxLength : Nat := 5

/-- The largest uncompressed length a block may declare. -/
def maxUncompressedLength : Nat := 2 ^ 32 - 1

/-- The value of the continuation bit, set on every preamble byte but the
last. Seven payload bits sit below it, so its value is also the radix. -/
def continuation : Nat := 128

/-- Every way decompression can reject its input. -/
inductive SnappyError where
  /-- The bytes ran out inside the preamble. -/
  | preambleTruncated
  /-- The preamble did not end within `preambleMaxLength` bytes. -/
  | preambleTooLong
  /-- The preamble declared more than `maxUncompressedLength` bytes. -/
  | preambleTooLarge (declared : Nat)
  /-- A literal, or the extra length bytes of one, ran past the end of the
  input. -/
  | literalPastEnd
  /-- A copy's offset bytes ran past the end of the input. -/
  | copyPastEnd
  /-- A copy offset of zero, which names no byte. -/
  | copyOffsetZero
  /-- A copy offset reaching before the start of the output. -/
  | copyOffsetTooLarge (offset : Nat)
  /-- The output length differed from the one the preamble declared. -/
  | lengthMismatch (declared actual : Nat)
  deriving Repr, DecidableEq

/-- The value of `bs` read as a little-endian integer. -/
def leValue : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leValue bs

/-- Read the preamble: the uncompressed length, and the bytes after it.

Snappy requires no minimal encoding, so this does not call
`Varint.decode`, which rejects one: the reference implementation accepts
`80 00` and `80 80 80 80 00` as encodings of zero. The cap and the
`uint32` range are the rules that do apply. -/
def readPreambleAux : List UInt8 → Nat → Nat → Nat → Except SnappyError (Nat × List UInt8)
  | [], _, _, _ => .error .preambleTruncated
  | _ :: _, _, _, 0 => .error .preambleTooLong
  | b :: bs, acc, shift, fuel + 1 =>
      let acc := acc + (b.toNat % continuation) * 2 ^ shift
      if b.toNat < continuation then
        .ok (acc, bs)
      else
        readPreambleAux bs acc (shift + 7) fuel

/-- The uncompressed length a block declares, and the bytes after it. -/
def readPreamble (bs : List UInt8) : Except SnappyError (Nat × List UInt8) :=
  match readPreambleAux bs 0 0 preambleMaxLength with
  | .error e => .error e
  | .ok (len, rest) =>
      if maxUncompressedLength < len then
        .error (.preambleTooLarge len)
      else
        .ok (len, rest)

/-- Copy `n` bytes from `offset` back, onto the reversed output `out`.

Each byte is read after the previous one was written, so a copy longer
than its offset repeats what it has already produced. -/
def copyBytes (out : List UInt8) (offset : Nat) : Nat → Except SnappyError (List UInt8)
  | 0 => .ok out
  | n + 1 =>
      match out[offset - 1]? with
      | none => .error (.copyOffsetTooLarge offset)
      | some b => copyBytes (b :: out) offset n

/-- Decode the elements of a block onto the reversed output `out`.

`fuel` bounds the number of elements. Every element consumes at least its
tag byte, so the length of the input is enough, which is what
`decompress` supplies. -/
def decompressElements : List UInt8 → List UInt8 → Nat → Except SnappyError (List UInt8)
  | [], out, _ => .ok out
  | _ :: _, _, 0 => .error .literalPastEnd
  | tag :: rest, out, fuel + 1 =>
      let t := tag.toNat % 4
      let upper := tag.toNat / 4
      if t == 0 then
        -- A literal. Lengths up to 60 ride in the tag; above that the tag
        -- names how many little-endian bytes carry the length.
        if upper < 60 then
          let len := upper + 1
          if rest.length < len then
            .error .literalPastEnd
          else
            decompressElements (rest.drop len) ((rest.take len).reverse ++ out) fuel
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
        -- A copy. The width of the offset follows from the tag, and the
        -- length is in the tag's upper bits.
        let width := if t == 1 then 1 else if t == 2 then 2 else 4
        let len := if t == 1 then 4 + upper % 8 else upper + 1
        if rest.length < width then
          .error .copyPastEnd
        else
          let offset :=
            if t == 1 then upper / 8 * 256 + (rest.take 1).foldl (fun _ b => b.toNat) 0
            else leValue (rest.take width)
          if offset == 0 then
            .error .copyOffsetZero
          else
            match copyBytes out offset len with
            | .error e => .error e
            | .ok out => decompressElements (rest.drop width) out fuel

/-- The bytes a Snappy block decompresses to, or why it is not one. -/
def decompressList (bs : List UInt8) : Except SnappyError (List UInt8) :=
  match readPreamble bs with
  | .error e => .error e
  | .ok (declared, rest) =>
      match decompressElements rest [] rest.length with
      | .error e => .error e
      | .ok out =>
          if out.length == declared then
            .ok out.reverse
          else
            .error (.lengthMismatch declared out.length)

/-- The bytes a Snappy block decompresses to, or why it is not one. -/
def decompress (bs : ByteArray) : Except SnappyError ByteArray :=
  (decompressList bs.toList).map fun out => ⟨out.toArray⟩

end EthLib.Networking.Snappy
