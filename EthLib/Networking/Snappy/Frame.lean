module

public import EthLib.Cryptography.Hash.Crc32c
public import EthLib.Networking.Snappy.Block

/-!
# `Networking.Snappy.Frame`

The Snappy framing format, from `framing_format.txt` of `google/snappy`:

<https://github.com/google/snappy/blob/7406111ac4ae539ea0db8b7ea2dc76730cd957f4/framing_format.txt>

Consensus-layer peers compress request and response messages with it.

A stream is a sequence of chunks with nothing between them (§1):

```text
    [ type: 1 | length: 3, little-endian | data: length ]
```

The first chunk is the stream identifier (§4.1).

A data chunk starts with a masked CRC-32C of its uncompressed data (§3).

A peer controls every byte, so decoding is total and names each way a stream can be malformed.

The decoder reads the whole stream at once.

The encoder writes uncompressed chunks only.

It gives proofs, tests and bindings a stream to decode, and it is not a compressor.
-/

@[expose] public section

namespace EthLib.Networking.Snappy

open EthLib.Base (bytesToUint uintToBytes)
open EthLib.Cryptography.Hash.Crc32c (crc32c)

/-- The ten bytes every stream starts with (§4.1).

They are a chunk of type `0xff` and length 6, holding "sNaPpY" in ASCII.
-/
def streamIdentifier : List UInt8 := [0xff, 0x06, 0x00, 0x00, 0x73, 0x4e, 0x61, 0x50, 0x70, 0x59]

/-- The type of a stream identifier chunk (§4.1). -/
def streamIdentifierType : UInt8 := 0xff

/-- The type of a compressed data chunk (§4.2). -/
def compressedType : UInt8 := 0x00

/-- The type of an uncompressed data chunk (§4.3). -/
def uncompressedType : UInt8 := 0x01

/-- The most uncompressed bytes one data chunk may hold (§4.2).

§4.3 says an uncompressed chunk "should" respect it, and the decoder rejects one that does not.
-/
def maxChunkLength : Nat := 65536

/-- The masked CRC-32C that a data chunk stores (§3).

The CRC is rotated right by 15 bits, then `0xa282ead8` is added modulo 2^32.
-/
def maskedCrc (data : ByteArray) : UInt32 :=
  let crc := crc32c data
  ((crc >>> 15) ||| (crc <<< 17)) + 0xa282ead8

/-- Every way decoding a stream can reject its input. -/
inductive FrameError where
  /-- The stream does not start with a stream identifier chunk (§1). -/
  | missingStreamIdentifier
  /-- The input ended inside the four header bytes of a chunk. -/
  | headerTruncated
  /-- The data of a chunk ran past the end of the input. -/
  | chunkPastEnd
  /-- A stream identifier chunk with a length or contents other than those of §4.1. -/
  | badStreamIdentifier
  /-- A data chunk too short to hold its four checksum bytes. -/
  | checksumTruncated
  /-- A data chunk holding more than 65536 uncompressed bytes (§4.2, §4.3). -/
  | chunkTooLarge (length : Nat)
  /-- The stored checksum differs from the masked CRC-32C of the uncompressed data (§3). -/
  | checksumMismatch (stored computed : UInt32)
  /-- The data of a compressed chunk is not a valid Snappy block (§4.2). -/
  | block (error : SnappyError)
  /-- A reserved unskippable chunk type, `0x02` to `0x7f` (§4.5). -/
  | reservedUnskippable (type : UInt8)
  deriving Repr, DecidableEq

/-- The uncompressed data of a chunk, if the stored checksum matches it (§3).

The checksum is four bytes, little-endian.
-/
def verifyChecksum (checksum data : List UInt8) : Except FrameError (List UInt8) :=
  let stored := UInt32.ofNat (bytesToUint checksum.toArray.toVector)
  let computed := maskedCrc ⟨data.toArray⟩
  if stored == computed then .ok data else .error (.checksumMismatch stored computed)

/-- The uncompressed bytes that one chunk adds to the output, from its type and data (§4). -/
def decodeChunk (type : UInt8) (body : List UInt8) : Except FrameError (List UInt8) :=
  if type == compressedType then
    if body.length < 4 then
      .error .checksumTruncated
    else
      let block := body.drop 4
      -- The preamble of the block declares the uncompressed length.
      match readPreamble block with
      | .error e => .error (.block e)
      | .ok (declared, _) =>
          if maxChunkLength < declared then
            .error (.chunkTooLarge declared)
          else
            match decompressList block with
            | .error e => .error (.block e)
            | .ok data => verifyChecksum (body.take 4) data
  else if type == uncompressedType then
    if body.length < 4 then
      .error .checksumTruncated
    else
      let data := body.drop 4
      if maxChunkLength < data.length then
        .error (.chunkTooLarge data.length)
      else
        verifyChecksum (body.take 4) data
  -- A stream identifier after the first one is skipped, if it is well formed (§4.1).
  else if type == streamIdentifierType then
    if body == streamIdentifier.drop 4 then .ok [] else .error .badStreamIdentifier
  else if type < 0x80 then
    .error (.reservedUnskippable type)
  -- Reserved skippable chunks (§4.6) and padding (§4.4) are skipped unread.
  else
    .ok []

/-- Decode the chunks of a stream, one after the other.

The fuel bounds the number of chunks.

Each chunk takes at least its four header bytes, so the input length is enough fuel.
-/
def decodeChunks : List UInt8 → Nat → Except FrameError (List UInt8)
  | [], _ => .ok []
  | type :: l0 :: l1 :: l2 :: rest, fuel + 1 =>
      let len := bytesToUint #v[l0, l1, l2]
      if rest.length < len then
        .error .chunkPastEnd
      else
        match decodeChunk type (rest.take len) with
        | .error e => .error e
        | .ok out => (decodeChunks (rest.drop len) fuel).map (out ++ ·)
  -- A header cut short, or out of fuel: the second is unreachable with enough fuel.
  | _, _ => .error .headerTruncated

/-- The bytes a framed stream decodes to, or why it is not a valid stream. -/
def decodeFramesList (bs : List UInt8) : Except FrameError (List UInt8) :=
  -- The first chunk must be a stream identifier (§1).
  -- The chunk loop then checks its length and contents.
  match bs with
  | type :: _ =>
      if type == streamIdentifierType then decodeChunks bs bs.length
      else .error .missingStreamIdentifier
  | [] => .error .missingStreamIdentifier

/-- The bytes a framed stream decodes to, or why it is not a valid stream. -/
def decodeFrames (bs : ByteArray) : Except FrameError ByteArray :=
  (decodeFramesList bs.data.toList).map fun out => ⟨out.toArray⟩

/-- One uncompressed data chunk that holds `data`, at most 65536 bytes (§4.3).

Its length counts the four checksum bytes.
-/
def uncompressedChunk (data : List UInt8) : List UInt8 :=
  uncompressedType :: (uintToBytes 3 (data.length + 4)).toList ++
    (uintToBytes 4 (maskedCrc ⟨data.toArray⟩).toNat).toList ++ data

/-- The data cut into uncompressed chunks of 65536 bytes, the last one shorter.

The fuel bounds the number of chunks, and the data length is enough.
-/
def encodeChunksLiteral : List UInt8 → Nat → List UInt8
  | [], _ => []
  -- Out of fuel: unreachable when the fuel is at least the data length.
  | _ :: _, 0 => []
  | b :: bs, fuel + 1 =>
      uncompressedChunk ((b :: bs).take maxChunkLength) ++
        encodeChunksLiteral ((b :: bs).drop maxChunkLength) fuel

/-- A framed stream that decodes to `data`: the stream identifier, then uncompressed chunks.

It is the inverse that proofs, tests and bindings use, not a compressor.
-/
def encodeFramesLiteral (data : ByteArray) : ByteArray :=
  ⟨(streamIdentifier ++ encodeChunksLiteral data.data.toList data.size).toArray⟩

end EthLib.Networking.Snappy
