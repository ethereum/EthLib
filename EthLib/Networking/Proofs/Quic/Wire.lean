module

public import EthLib.Networking.Quic.Wire
public import EthLib.Networking.Proofs.Quic.Varint
public import EthLib.Base.Proofs.ByteReader

/-!
# Proofs: QUIC wire fields

Each reader recovers its field and preserves arbitrary trailing bytes.
-/

@[expose] public section

namespace EthLib.Networking.Quic.Wire

open EthLib.Base.ByteReader (bytes_append uint_encode require_true)

@[simp] theorem byte_cons (head : UInt8) (rest : List UInt8) :
    byte (head :: rest) = .ok (head, rest) := rfl

@[simp] theorem varint_encode (value : Varint) (rest : List UInt8) :
    varint (Varint.encode value ++ rest) = .ok (value, rest) := by
  simp [varint, Varint.decode_encode, Except.mapError]

/-- Reading a length-prefixed string recovers its bytes and the following bytes. -/
theorem blob_encode (data rest : List UInt8) (h : data.length < 2 ^ 62) :
    blob (Varint.encode ⟨data.length, h⟩ ++ (data ++ rest)) = .ok (data, rest) := by
  simp only [blob, bind, StateT.bind, Except.bind,
    varint_encode, bytes_append]

end EthLib.Networking.Quic.Wire
