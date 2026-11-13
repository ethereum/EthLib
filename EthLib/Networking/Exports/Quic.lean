module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Networking.Quic.Varint

/-!
# Exports: QUIC integers

The encoder rejects a value of `2^62` or more with code 0.

The decoder accepts the longer forms of RFC 9000 §16.
-/

public section

namespace EthLib.Networking.Quic.Exports

open EthLib.Exports (Result PyValue pyExport)

/-- Encode a value below `2^62` with its shortest QUIC representation, RFC 9000 §16. -/
@[export eth_quic_varint_encode]
def encodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (value : Nat) => do
    if h : value < 2 ^ 62 then
      return (⟨(Varint.encode ⟨value, h⟩).toArray⟩ : ByteArray)
    else throw (0, "value must be below 2^62")) args

/-- Read a QUIC integer and return its value and the trailing bytes, RFC 9000 §16. -/
@[export eth_quic_varint_decode]
def decodeExport (args : PyValue) : Result PyValue :=
  pyExport (fun (data : ByteArray) => do
    let (value, rest) ← (Varint.decode data.data.toList).mapError
      fun e => (e.code, s!"QUIC integer rejected: {reprStr e}")
    return (value.val, (⟨rest.toArray⟩ : ByteArray))) args

end EthLib.Networking.Quic.Exports
