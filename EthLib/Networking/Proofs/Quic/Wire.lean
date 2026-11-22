module

public import EthLib.Networking.Quic.Wire
public import EthLib.Networking.Proofs.Quic.Varint
public import EthLib.Networking.Proofs.Encoding.ByteReader
public import EthLib.Base.Proofs.Bytes

/-!
# Proofs: QUIC wire fields

Each reader recovers its field and preserves arbitrary trailing bytes.
-/

@[expose] public section

namespace EthLib.Networking.Quic.Wire

open EthLib.Networking.Encoding.ByteReader (bytes_append uint_encode require_true)

@[simp] theorem byte_cons (head : UInt8) (rest : List UInt8) :
    byte (head :: rest) = .ok (head, rest) := rfl

@[simp] theorem varint_encode (value : Varint) (rest : List UInt8) :
    varint (Varint.encodeList value ++ rest) = .ok (value, rest) := by
  simp [varint, Varint.decodeList_encodeList, Except.mapError]

/-- Reading an opaque fixed-size field preserves its bytes exactly. -/
theorem vector_encode (n : Nat) (value : Vector UInt8 n) (rest : List UInt8) :
    vector n (value.toList ++ rest) = .ok (value, rest) :=
  Encoding.ByteReader.vector_append _ value rest

/-- Reading a length-prefixed string recovers its bytes and the following bytes. -/
theorem blob_encode (data rest : List UInt8) (h : data.length < 2 ^ 62) :
    blob (Varint.encodeList ⟨data.length, h⟩ ++ (data ++ rest)) = .ok (data, rest) := by
  simp only [blob, bind, StateT.bind, Except.bind,
    varint_encode, bytes_append]

/-- Reading a packed field through the list reader preserves its bytes and suffix. -/
@[simp] theorem bytes_byteArray_append (field : ByteArray) (rest : List UInt8) :
    bytes field.size (field.data.toList ++ rest) = .ok (field.data.toList, rest) := by
  show Encoding.ByteReader.bytes (Error.truncated field.size (field.data.toList ++ rest).length)
    field.size (field.data.toList ++ rest) = _
  simpa using bytes_append (Error.truncated field.size (field.data.toList ++ rest).length)
    field.data.toList rest

/-- Reading a packed length-prefixed field preserves its bytes and suffix. -/
theorem blob_byteArray_encode (data : ByteArray) (rest : List UInt8) (h : data.size < 2 ^ 62) :
    blob (Varint.encodeList ⟨data.size, h⟩ ++ (data.data.toList ++ rest)) =
      .ok (data.data.toList, rest) := by
  simpa using blob_encode data.data.toList rest h

end EthLib.Networking.Quic.Wire
