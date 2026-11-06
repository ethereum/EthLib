module

public import EthLib.Serialization.Ssz.Typed.Class
public import EthLib.Serialization.Proofs.Ssz.Codec.Canonicality
public import EthLib.Serialization.Proofs.Ssz.Codec.Totality

/-!
# Proofs: typed SSZ values encode as their untyped values do

A lawful typed value converts to an admissible value of a well-formed SSZ type and back.

The codec theorems of untyped values then carry over to the typed operations.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open SszType

/--
The laws of a typed SSZ value.

The two conversions are inverse on the values the typed side holds.
-/
class LawfulSszType (α : Type) [SszType α] : Prop where
  /-- The SSZ type is well formed. -/
  wellFormed : (desc α).wellFormed = .ok ()
  /-- Every typed value stands for a value that its SSZ type admits. -/
  fits : ∀ a : α, Fits (desc α) (toValue a)
  /-- Reading back an untyped value gives the typed value it came from. -/
  ofValue_toValue : ∀ a : α, ofValue (toValue a) = .ok a
  /-- An untyped value that reads back is the one its typed value stands for. -/
  toValue_of_ofValue : ∀ {value : Value} {a : α}, ofValue value = .ok a → toValue a = value
  /-- The root that the type gives a value is the root of its untyped value. -/
  root_eq : ∀ a : α, root a = Ssz.hashTreeRoot (desc α) (toValue a) := by intro; rfl

namespace SszType

variable {α : Type} [SszType α]

/-- The typed bytes are the untyped bytes of the value. -/
theorem serialize_ok_iff {a : α} {data : ByteArray} :
    serialize a = .ok data ↔ Ssz.serialize (desc α) (toValue a) = .ok data.data := by
  unfold serialize
  cases Ssz.serialize (desc α) (toValue a) <;>
    simp [bind, Except.bind, pure, Except.pure, ByteArray.ext_iff, eq_comm]

variable [LawfulSszType α]

/-- The typed root is the root of the untyped value, cut to one 32-byte node. -/
theorem hashTreeRoot_eq (a : α) :
    hashTreeRoot a = (do toChunk (← Ssz.hashTreeRoot (desc α) (toValue a))) := by
  rw [hashTreeRoot, LawfulSszType.root_eq]

/-- Deserializing the bytes of a value gives that value. -/
theorem deserialize_serialize {a : α} {data : ByteArray} (wrote : serialize a = .ok data) :
    deserialize α data = .ok a := by
  -- The untyped codec reads back the untyped value, which converts back to the typed one.
  have read := roundTrip_of_encoding LawfulSszType.wellFormed (serialize_ok_iff.mp wrote)
  simp [deserialize, read, bind, Except.bind, LawfulSszType.ofValue_toValue]

/-- Bytes that deserialize are the bytes of the value they give, so the decoder is canonical. -/
theorem serialize_deserialize {a : α} {data : ByteArray} (read : deserialize α data = .ok a) :
    serialize a = .ok data := by
  unfold deserialize at read
  cases decoded : Ssz.deserialize (desc α) data.data with
  | error fault => simp [decoded, bind, Except.bind] at read
  | ok value =>
    simp only [decoded, bind, Except.bind] at read
    -- The untyped value re-encodes to the same bytes, and the typed value stands for it.
    have wrote := serialize_of_deserialize (desc α) LawfulSszType.wellFormed _ _ decoded
    rw [← LawfulSszType.toValue_of_ofValue read] at wrote
    exact serialize_ok_iff.mpr wrote

/-- Two values with the same bytes are equal. -/
theorem serialize_injective {a b : α} {data : ByteArray} (left : serialize a = .ok data)
    (right : serialize b = .ok data) : a = b :=
  Except.ok.inj ((deserialize_serialize left).symm.trans (deserialize_serialize right))

/-- A type of a fixed width serializes each value to exactly that many bytes. -/
theorem serialize_size {a : α} {data : ByteArray} {width : Nat}
    (fixed : (desc α).fixedSize = some width) (wrote : serialize a = .ok data) :
    data.size = width :=
  serialize_size_of_encoding LawfulSszType.wellFormed fixed (serialize_ok_iff.mp wrote)

/--
A value serializes, unless a composite part reaches `2^32` bytes.

An offset has four bytes, so a larger part has no offset to point at it.
-/
theorem serialize_ok_or_overflow (a : α) :
    (∃ data, serialize a = .ok data) ∨
    (∃ size, 2 ^ (8 * bytesPerOffset) ≤ size ∧ serialize a = .error (.offsetOverflow size)) := by
  rcases serialize_fits_or_overflow (LawfulSszType.fits a) with
    ⟨bytes, wrote⟩ | ⟨size, large, failed⟩
  · exact .inl ⟨⟨bytes⟩, serialize_ok_iff.mpr wrote⟩
  · exact .inr ⟨size, large, by simp [serialize, failed, bind, Except.bind]⟩

end SszType

end EthLib.Serialization.Ssz
