module

public import EthLib.Base.Exports
public import EthLib.Networking.Encoding.Varint

/-!
# `Exports.Varint`

C-ABI exports for the unsigned protobuf varint, callable from the Python C extension.

A rejected input comes back as the code of its error, and a message that ends with the fault.
-/

public section

namespace EthLib.Networking.Encoding.Varint.Exports

open EthLib.Exports (Result)

/-- The varint of a 64-bit value. -/
@[export eth_varint_encode]
def encodeExport (v : UInt64) : Result ByteArray :=
  pure ⟨(encode v).toArray⟩

/-- The 64-bit value that the bytes encode, if they are exactly one minimal varint. -/
@[export eth_varint_decode]
def decodeExport (data : ByteArray) : Result UInt64 :=
  (decode data.data.toList).mapError fun e => (e.code, s!"varint rejected: {reprStr e}")

end EthLib.Networking.Encoding.Varint.Exports
