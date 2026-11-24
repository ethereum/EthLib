module

public import EthLib.Cryptography.Hash.Crc.Crc32c
public import EthLib.Networking.Snappy.Block

/-!
# `Networking.Snappy.Frame`

The Snappy framing format, from `framing_format.txt` of `google/snappy`:

<https://github.com/google/snappy/blob/7406111ac4ae539ea0db8b7ea2dc76730cd957f4/framing_format.txt>

Consensus-layer peers compress request and response messages with it.
-/

@[expose] public section

namespace EthLib.Networking.Snappy

open EthLib.Base (ByteOrder.ofLE ByteOrder.toLE)
open EthLib.Cryptography.Hash.Crc32c (crc32c)

/-- The ten bytes every stream starts with (§4.1).

They are a chunk of type `0xff` and length 6, holding sNaPpY in ASCII.
-/
def streamIdentifier : List UInt8 := [0xff, 0x06, 0x00, 0x00, 0x73, 0x4e, 0x61, 0x50, 0x70, 0x59]

/-- The type of a stream identifier chunk (§4.1). -/
def streamIdentifierType : UInt8 := 0xff

/-- The type of a compressed data chunk (§4.2). -/
def compressedType : UInt8 := 0x00

/-- The type of an uncompressed data chunk (§4.3). -/
def uncompressedType : UInt8 := 0x01

/-- The most uncompressed bytes one data chunk may hold (§4.2).

§4.3 says an uncompressed chunk should respect it, and the decoder rejects one that does not.
-/
def maxChunkLength : Nat := 65536

/-- The masked CRC-32C that a data chunk stores (§3), at its start. -/
def maskedCrc (data : ByteArray) : UInt32 :=
  -- §3: the CRC-32C of RFC 3720, §12.1.
  let crc := crc32c data
  -- §3: rotate the checksum right by 15 bits, then add the constant 0xa282ead8 modulo 2^32.
  ((crc >>> 15) ||| (crc <<< 17)) + 0xa282ead8

/-- Every way decoding a stream can reject its input.

A peer controls every byte, so decoding is total and names each way a stream can be malformed. -/
inductive FrameError where
  /-- The stream does not start with a stream identifier chunk (§1).

  The field holds the type of the first chunk, or nothing for an empty stream. -/
  | missingStreamIdentifier (type : Option UInt8)
  /-- The input ended inside the four header bytes of a chunk, with `available` bytes left. -/
  | headerTruncated (available : Nat)
  /-- The data of a chunk ran past the end of the input.

  The header declares `length` bytes of data, and only `available` follow it. -/
  | chunkPastEnd (length available : Nat)
  /-- A stream identifier chunk with a length or contents other than those of §4.1.

  The field holds the length of its data. -/
  | badStreamIdentifier (length : Nat)
  /-- A data chunk too short to hold its four checksum bytes, with its data of `length` bytes. -/
  | checksumTruncated (length : Nat)
  /-- A data chunk holding more than 65536 uncompressed bytes (§4.2, §4.3). -/
  | chunkTooLarge (length : Nat)
  /-- The stored checksum differs from the masked CRC-32C of the uncompressed data (§3). -/
  | checksumMismatch (stored computed : UInt32)
  /-- The data of a compressed chunk is not a valid Snappy block (§4.2). -/
  | block (error : SnappyError)
  /-- A reserved unskippable chunk type, `0x02` to `0x7f` (§4.5). -/
  | reservedUnskippable (type : UInt8)
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

The codes start at 101, above every code of a block error, so that the two never meet.

A new constructor takes a new code, so that each code keeps its meaning. -/
def FrameError.code : FrameError → UInt32
  | .missingStreamIdentifier _ => 101
  | .headerTruncated _ => 102
  | .chunkPastEnd .. => 103
  | .badStreamIdentifier _ => 104
  | .checksumTruncated _ => 105
  | .chunkTooLarge _ => 106
  | .checksumMismatch .. => 107
  | .block _ => 108
  | .reservedUnskippable _ => 109

/-- The uncompressed data of a chunk, if the stored checksum matches it (§3). -/
def verifyChecksum (checksum data : List UInt8) : Except FrameError (List UInt8) :=
  -- §3: the checksum is always stored as a four bytes long integer, in little-endian.
  let stored := UInt32.ofNat (ByteOrder.ofLE checksum.toArray.toVector)
  -- §4.2 and §4.3: it is the masked CRC-32C of the uncompressed data.
  let computed := maskedCrc ⟨data.toArray⟩
  if stored == computed then .ok data else .error (.checksumMismatch stored computed)

/-- The uncompressed bytes that one chunk adds to the output, from its type and data (§4). -/
def decodeChunk (type : UInt8) (body : List UInt8) : Except FrameError (List UInt8) :=
  -- §4.2, chunk type 0x00: compressed data.
  if type == compressedType then
    -- §4.2: the four bytes of the masked CRC-32C come first.
    if body.length < 4 then
      .error (.checksumTruncated body.length)
    else
      -- §4.2: then a normal Snappy compressed block.
      let block := body.drop 4
      -- The preamble of the block declares the uncompressed length.
      match readPreamble block with
      | .error e => .error (.block e)
      | .ok (declared, _) =>
          -- §4.2: the uncompressed data in a chunk must be no longer than 65536 bytes.
          --
          -- Not in §4.2: the check reads the declared length, before the block is decompressed.
          if maxChunkLength < declared then
            .error (.chunkTooLarge declared)
          else
            match decompressList block with
            | .error e => .error (.block e)
            -- §4.2: the checksum is that of the uncompressed data.
            | .ok data => verifyChecksum (body.take 4) data
  -- §4.3, chunk type 0x01: uncompressed data.
  else if type == uncompressedType then
    -- §4.3: the data is preceded by its own masked CRC-32C, in four bytes.
    if body.length < 4 then
      .error (.checksumTruncated body.length)
    else
      let data := body.drop 4
      -- §4.3: the chunk should contain no more than 65536 data bytes.
      --
      -- The decoder reads that should as a must.
      --
      -- So the chunk length with the checksum is at most 65540, as §4.3 says.
      if maxChunkLength < data.length then
        .error (.chunkTooLarge data.length)
      else
        verifyChecksum (body.take 4) data
  -- §4.1, chunk type 0xff: the first stream identifier and any later one add no bytes.
  else if type == streamIdentifierType then
    -- §4.1: the chunk is exactly six bytes long and contains sNaPpY in ASCII.
    --
    -- Not in §4.1: a chunk with another length or other contents is rejected.
    if body == streamIdentifier.drop 4 then .ok [] else .error (.badStreamIdentifier body.length)
  -- §4.5, chunk types 0x02 to 0x7f: a decoder should immediately return an error.
  else if type < 0x80 then
    .error (.reservedUnskippable type)
  -- Reserved skippable chunks (§4.6) and padding (§4.4) are skipped unread.
  else
    .ok []

-- Each check of a length against a bound reads only as many elements as the bound.
attribute [local instance high] decideLeLength decideLengthLt

/-- Read the chunk at the front of a stream, and return its decoded bytes and the bytes after it. -/
def readChunk : List UInt8 → Except FrameError (List UInt8 × List UInt8)
  -- §1: a chunk is first a single byte of chunk identifier, then a three-byte length.
  | type :: l0 :: l1 :: l2 :: rest =>
      -- §1: the length is little-endian, from 0 to 16777215, and excludes the four header bytes.
      let len := ByteOrder.ofLE #v[l0, l1, l2]
      -- §1: then the data, of that length.
      if rest.length < len then
        .error (.chunkPastEnd len rest.length)
      else
        -- §4: the type of the chunk says how to read its data.
        (decodeChunk type (rest.take len)).map fun out => (out, rest.drop len)
  -- Not in §1: the input ended inside the four header bytes.
  | bs => .error (.headerTruncated bs.length)

/-- Decode the chunks of a stream, one after the other, with nothing between them (§1).

The fuel bounds the number of chunks.

Each chunk takes at least its four header bytes, so the input length is enough fuel.
-/
def decodeChunks : List UInt8 → Nat → Except FrameError (List UInt8)
  -- §1: the stream ends when the file ends, with no explicit end-of-file marker.
  | [], _ => .ok []
  -- Out of fuel: unreachable with enough fuel, so the field is arbitrary.
  | bs@(_ :: _), 0 => .error (.headerTruncated bs.length)
  | bs@(_ :: _), fuel + 1 => do
      -- §1: chunks lie back-to-back, with no padding in between.
      let (out, rest) ← readChunk bs
      (decodeChunks rest fuel).map (out ++ ·)

/-- The bytes a framed stream decodes to, or why it is not a valid stream. -/
def decodeFramesList (bs : List UInt8) : Except FrameError (List UInt8) :=
  -- The first chunk must be a stream identifier (§1), whose length and contents the loop checks.
  match bs with
  | type :: _ =>
      if type == streamIdentifierType then decodeChunks bs bs.length
      else .error (.missingStreamIdentifier (some type))
  | [] => .error (.missingStreamIdentifier none)

/-- The bytes a framed stream decodes to, or why it is not a valid stream.

The decoder reads the whole stream at once. -/
def decodeFrames (bs : ByteArray) : Except FrameError ByteArray :=
  (decodeFramesList bs.data.toList).map fun out => ⟨out.toArray⟩

/-- Read the chunks of a stream until they hold `need` bytes.

It returns the decoded bytes of the chunks read and the bytes after the last of them.

The fuel bounds the number of chunks. -/
def readChunks (need : Nat) : List UInt8 → Nat →
    Except FrameError (List UInt8 × List UInt8)
  -- The stream can end first, and then the output is shorter.
  | [], _ => .ok ([], [])
  -- Out of fuel: unreachable with enough fuel, so the field is arbitrary.
  | bs@(_ :: _), 0 => .error (.headerTruncated bs.length)
  | bs@(_ :: _), fuel + 1 => do
      -- The reader reads at least one chunk unless the stream is empty, even when `need` is 0.
      let (out, rest) ← readChunk bs
      -- Not in the source: the reader stops at the chunk that completes `need` bytes.
      --
      -- A chunk is read whole, so the output can be longer than `need`.
      if need ≤ out.length then .ok (out, rest)
      else (readChunks (need - out.length) rest fuel).map fun read => (out ++ read.1, read.2)

/-- Read a framed stream until it holds `n` bytes, and return its output with the bytes after.

The stream starts with the stream identifier, which the reader reads even when `n` is 0.

It stops at the chunk that completes `n` bytes, so a caller can reject any byte after it.
-/
def readFrames (n : Nat) (bs : List UInt8) :
    Except FrameError (List UInt8 × List UInt8) :=
  -- §1: the first chunk must always be the stream identifier chunk.
  --
  -- The loop checks its length and contents (§4.1).
  match bs with
  | type :: _ =>
      if type == streamIdentifierType then readChunks n bs bs.length
      else .error (.missingStreamIdentifier (some type))
  | [] => .error (.missingStreamIdentifier none)

/-- One uncompressed data chunk that holds `data`, at most 65536 bytes (§4.3). -/
def uncompressedChunk (data : List UInt8) : List UInt8 :=
  -- §1 and §4.3: the type 0x01, then the length of the chunk data in three bytes, little-endian.
  --
  -- §4.3: that data is the four checksum bytes, then the raw bytes.
  uncompressedType :: (ByteOrder.toLE 3 (data.length + 4)).toList ++
    -- §3: the masked CRC-32C, as a four bytes long integer in little-endian.
    (ByteOrder.toLE 4 (maskedCrc ⟨data.toArray⟩).toNat).toList ++ data

/-- The data cut into pieces of 65536 bytes, the last one shorter, each written by `chunk`.

The fuel bounds the number of chunks, and the data length is enough.
-/
def encodeChunks (chunk : List UInt8 → List UInt8) : List UInt8 → Nat → List UInt8
  | [], _ => []
  -- Out of fuel: unreachable when the fuel is at least the data length.
  | _ :: _, 0 => []
  | b :: bs, fuel + 1 =>
      -- §4.2 and §4.3: a data chunk holds at most 65536 uncompressed bytes.
      chunk ((b :: bs).take maxChunkLength) ++
        encodeChunks chunk ((b :: bs).drop maxChunkLength) fuel

/-- A framed stream that decodes to `data`: the stream identifier, then uncompressed chunks.

It is the inverse that proofs, tests and bindings use, not a compressor.

The encoder writes uncompressed chunks only.
-/
def encodeFramesLiteral (data : ByteArray) : ByteArray :=
  -- §1 and §4.1: the stream identifier chunk first, then the data chunks back-to-back.
  ⟨(streamIdentifier ++ encodeChunks uncompressedChunk data.data.toList data.size).toArray⟩

end EthLib.Networking.Snappy
