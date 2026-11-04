module

public import EthLib.Networking.Encoding.Varint

/-!
# `Exports.Varint`

C-ABI exports for the unsigned protobuf varint, callable from the Python C extension.

A rejected input becomes an error that ends with the fault, as Lean writes it.
-/

public section

namespace EthLib.Networking.Encoding.Varint.Exports

/-- The varint of a 64-bit value. -/
@[export eth_varint_encode]
def encodeExport (v : UInt64) : IO ByteArray :=
  pure ⟨(encode v).toArray⟩

/-- The 64-bit value that the bytes encode, if they are exactly one minimal varint. -/
@[export eth_varint_decode]
def decodeExport (data : ByteArray) : IO UInt64 :=
  match decode data.data.toList with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"varint rejected: {reprStr e}")

end EthLib.Networking.Encoding.Varint.Exports
