module

public import EthLib.Base.Exports
public import EthLib.Networking.Snappy.Compress
public import EthLib.Networking.Snappy.Frame

/-!
# `Exports.Snappy`

C-ABI exports for Snappy blocks and frames, callable from the Python C extension.

A rejected input comes back as the code of its error, and a message that ends with the fault.

A block error and a frame error never share a code.
-/

public section

namespace EthLib.Networking.Snappy.Exports

open EthLib.Exports (Result)

/-- Run a fallible step, with the code of its error and a message that names the fault. -/
def runSnappy {ε α : Type} [Repr ε] (code : ε → UInt32) (what : String) (act : Except ε α) :
    Result α :=
  act.mapError fun e => (code e, s!"{what}: {reprStr e}")

/-- The data of a Snappy block. -/
@[export eth_snappy_decompress]
def decompressExport (block : ByteArray) : Result ByteArray :=
  runSnappy SnappyError.code "block rejected" (decompress block)

/-- The block that the compressor writes for the data, of at most 2^32 - 1 bytes. -/
@[export eth_snappy_compress]
def compressExport (data : ByteArray) : Result ByteArray :=
  pure (compress data)

/-- The data of a framed stream. -/
@[export eth_snappy_decode_frames]
def decodeFramesExport (stream : ByteArray) : Result ByteArray :=
  runSnappy FrameError.code "stream rejected" (decodeFrames stream)

/-- The framed stream that holds the data in uncompressed chunks. -/
@[export eth_snappy_encode_frames_literal]
def encodeFramesLiteralExport (data : ByteArray) : Result ByteArray :=
  pure (encodeFramesLiteral data)

/-- The masked CRC-32C that a data chunk stores for the data. -/
@[export eth_snappy_masked_crc]
def maskedCrcExport (data : ByteArray) : Result UInt64 :=
  pure (maskedCrc data).toUInt64

end EthLib.Networking.Snappy.Exports
