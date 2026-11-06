module

public import EthLib.Networking.Snappy.Compress
public import EthLib.Networking.Snappy.Frame

/-!
# `Networking.Snappy.FrameEncode`

A framed stream that compresses, from `framing_format.txt` of `google/snappy`:

<https://github.com/google/snappy/blob/7406111ac4ae539ea0db8b7ea2dc76730cd957f4/framing_format.txt>

The data is cut into chunks of at most 65536 bytes (§4.2).

A compressed data chunk holds the masked CRC-32C of the bytes, then their Snappy block (§4.2).

An uncompressed data chunk holds the same checksum, then the bytes (§4.3).

The encoder writes a compressed chunk only when it is shorter than the uncompressed chunk.

So a chunk of data that does not compress takes eight bytes more than the data.
-/

@[expose] public section

namespace EthLib.Networking.Snappy

open EthLib.Base (uintToBytes)

/-- One compressed data chunk that holds `data`, at most 65536 bytes (§4.2).

Its length counts the four checksum bytes and the block.
-/
def compressedChunk (data : List UInt8) : List UInt8 :=
  let block := (compress ⟨data.toArray⟩).data.toList
  compressedType :: (uintToBytes 3 (block.length + 4)).toList ++
    (uintToBytes 4 (maskedCrc ⟨data.toArray⟩).toNat).toList ++ block

/-- The shorter of the compressed and the uncompressed chunk of `data`, at most 65536 bytes.

The uncompressed chunk wins a tie.
-/
def dataChunk (data : List UInt8) : List UInt8 :=
  if (compressedChunk data).length < (uncompressedChunk data).length then compressedChunk data
  else uncompressedChunk data

/-- A framed stream that decodes to `data`: the stream identifier, then its chunks.

A chunk is compressed when that makes it shorter.
-/
def encodeFrames (data : ByteArray) : ByteArray :=
  ⟨(streamIdentifier ++ encodeChunks dataChunk data.data.toList data.size).toArray⟩

end EthLib.Networking.Snappy
