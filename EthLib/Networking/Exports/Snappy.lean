module

public import EthLib.Networking.Snappy.Frame

/-!
# `Exports.Snappy`

C-ABI exports for Snappy blocks and frames, callable from the Python C extension.

A rejected input becomes an error that ends with the fault, as Lean writes it.
-/

public section

namespace EthLib.Networking.Snappy.Exports

/-- Run a fallible step down to `IO`, naming the fault. -/
def runSnappy {ε α : Type} [Repr ε] (what : String) (act : Except ε α) : IO α :=
  match act with
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{what}: {reprStr e}")

/-- The data of a Snappy block. -/
@[export eth_snappy_decompress]
def decompressExport (block : ByteArray) : IO ByteArray :=
  runSnappy "block rejected" (decompress block)

/-- The block that holds the data as one literal. -/
@[export eth_snappy_compress_literal]
def compressLiteralExport (data : ByteArray) : IO ByteArray :=
  pure (compressLiteral data)

/-- The data of a framed stream. -/
@[export eth_snappy_decode_frames]
def decodeFramesExport (stream : ByteArray) : IO ByteArray :=
  runSnappy "stream rejected" (decodeFrames stream)

/-- The framed stream that holds the data in uncompressed chunks. -/
@[export eth_snappy_encode_frames_literal]
def encodeFramesLiteralExport (data : ByteArray) : IO ByteArray :=
  pure (encodeFramesLiteral data)

/-- The masked CRC-32C that a data chunk stores for the data. -/
@[export eth_snappy_masked_crc]
def maskedCrcExport (data : ByteArray) : IO UInt64 :=
  pure (maskedCrc data).toUInt64

end EthLib.Networking.Snappy.Exports
