module

public import EthLib.Base.Exports
public import EthLib.Base.Exports.PyValue
public import EthLib.Networking.Encoding.Uvarint

/-!
# `Exports.Varint`

C-ABI exports for the unsigned protobuf varint and the multiformats unsigned varint.

The Python C extension calls them.

A rejected input comes back as the code of its error, and a message that ends with the fault.

An encoder refuses a value outside the format with code 0.
-/

public section

namespace EthLib.Networking.Encoding.Varint.Exports

open EthLib.Exports (ExportError Result toResult)

/-- A rejected varint reaches Python with its code, and its message is the printed error. -/
instance : ExportError VarintError where
  code := VarintError.code
  message := reprStr

/-- The varint of a 64-bit value. -/
@[export eth_varint_encode]
def encodeExport (v : UInt64) : Result ByteArray :=
  pure ⟨(encode v).toArray⟩

/-- The 64-bit value that the bytes encode, if they are exactly one minimal varint. -/
@[export eth_varint_decode]
def decodeExport (data : ByteArray) : Result UInt64 :=
  toResult "varint rejected" (decode data.data.toList)

end EthLib.Networking.Encoding.Varint.Exports

namespace EthLib.Networking.Encoding.Uvarint.Exports

open EthLib.Exports (ExportError Result PyValue pyExport rejectArgument toResult)

/-- A rejected unsigned varint reaches Python with its code, and the printed error. -/
instance : ExportError UvarintError where
  code := UvarintError.code
  message := reprStr

/-- The unsigned varint of a value below `2^63`. -/
@[export eth_uvarint_encode]
def encodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (value : Nat) => do
    if bound ≤ value then rejectArgument none "value must be below 2^63"
    return (⟨(encode value).toArray⟩ : ByteArray)) args

/-- The value of the unsigned varint at the start of the bytes, and the bytes after it. -/
@[export eth_uvarint_decode]
def decodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (data : ByteArray) => do
    let (value, rest) ← toResult "unsigned varint rejected" (decode data.data.toList)
    return (value, (⟨rest.toArray⟩ : ByteArray))) args

end EthLib.Networking.Encoding.Uvarint.Exports
