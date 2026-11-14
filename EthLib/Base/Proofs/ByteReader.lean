module

public import EthLib.Base.ByteReader
public import EthLib.Base.Proofs.BigEndian

/-!
# Proofs: readers of byte fields

Each reader recovers its field and preserves arbitrary trailing bytes.
-/

@[expose] public section

namespace EthLib.Base.ByteReader

/-- Reading as many bytes as a field holds returns that field and the bytes after it. -/
@[simp] theorem bytes_append {ε : Type} (truncated : ε) (field rest : List UInt8) :
    bytes truncated field.length (field ++ rest) = .ok (field, rest) := by
  simp [bytes]

/-- Reading a written integer returns it modulo the field width, and the bytes after it. -/
@[simp] theorem uint_encode {ε : Type} (truncated : ε) (n value : Nat) (rest : List UInt8) :
    uint truncated n (natToBytes n value ++ rest) = .ok (value % 256 ^ n, rest) := by
  simp [uint, bytes, natToBytes_length, bytesToNat_natToBytes,
    StateT.bind, StateT.pure, bind, Except.bind, pure, Except.pure]

/-- A condition that holds consumes nothing. -/
@[simp] theorem require_true {ε : Type} (condition : Prop) [Decidable condition]
    (holds : condition) (error : ε) (rest : List UInt8) :
    require condition error rest = .ok ((), rest) := by
  simp [require, holds]

end EthLib.Base.ByteReader
