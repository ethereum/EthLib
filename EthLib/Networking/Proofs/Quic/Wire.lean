module

public import EthLib.Networking.Quic.Wire
public import EthLib.Networking.Proofs.Quic.Varint

/-!
# Proofs: QUIC wire fields

Each reader recovers its field and preserves arbitrary trailing bytes.
-/

@[expose] public section

namespace EthLib.Networking.Quic.Wire

@[simp] theorem bytes_append (field rest : List UInt8) :
    bytes field.length (field ++ rest) = .ok (field, rest) := by
  simp [bytes]

@[simp] theorem byte_cons (head : UInt8) (rest : List UInt8) :
    byte (head :: rest) = .ok (head, rest) := rfl

@[simp] theorem varint_encode (value : Varint) (rest : List UInt8) :
    varint (Varint.encode value ++ rest) = .ok (value, rest) := by
  simp [varint, Varint.decode_encode, Except.mapError]

@[simp] theorem uint_encode (n value : Nat) (rest : List UInt8) :
    uint n (Base.natToBytes n value ++ rest) = .ok (value % 256 ^ n, rest) := by
  simp [uint, bytes, Base.natToBytes_length, Base.bytesToNat_natToBytes,
    StateT.bind, StateT.pure, bind, Except.bind, pure, Except.pure]

@[simp] theorem require_true (p : Prop) [Decidable p] (h : p) (e : Error)
    (rest : List UInt8) : require p e rest = .ok ((), rest) := by
  simp [require, h]

/-- Reading a length-prefixed string recovers its bytes and the following bytes. -/
theorem blob_encode (data rest : List UInt8) (h : data.length < 2 ^ 62) :
    blob (Varint.encode ⟨data.length, h⟩ ++ (data ++ rest)) = .ok (data, rest) := by
  simp only [blob, bind, StateT.bind, Except.bind,
    varint_encode, bytes_append]

end EthLib.Networking.Quic.Wire
