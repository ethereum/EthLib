module

public import EthLib.Serialization.Proofs.Ssz.Typed.Collections
public import EthLib.Serialization.Proofs.Ssz.Typed.Container

/-!
# Proofs: known answers of typed SSZ values

Each answer is worked out by hand from the SSZ rules, and pins the bytes of one value.

Each one first pins the SSZ type and the untyped value that the typed value stands for.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz.KnownAnswers

/-- A container of two fixed fields, `a: uint16` and `b: uint16`. -/
structure FixedPair where
  /-- The first field. -/
  a : UInt16
  /-- The second field. -/
  b : UInt16

instance : SszType FixedPair :=
  .container ["a", "b"] (fun p => (p.a, p.b)) (fun (a, b) => ⟨a, b⟩)

instance : LawfulSszType FixedPair :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

/-- A container of a fixed field `a: uint16` and a variable field `b: List[uint16, 4]`. -/
structure MixedPair where
  /-- The fixed field. -/
  a : UInt16
  /-- The variable field. -/
  b : SszList UInt16 4

instance : SszType MixedPair :=
  .container ["a", "b"] (fun p => (p.a, p.b)) (fun (a, b) => ⟨a, b⟩)

instance : LawfulSszType MixedPair :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

/-- A `uint16` puts its low byte first. -/
theorem serialize_uint16 : SszType.serialize (0x0102 : UInt16) = .ok ⟨#[0x02, 0x01]⟩ := by
  have shape : SszType.desc UInt16 = .uint 2 := rfl
  have value : SszType.toValue (0x0102 : UInt16) = .uint 0x0102 := rfl
  simp only [SszType.serialize, shape, value, serialize]
  rfl

/-- A `boolean` is one byte, `0x01` for true. -/
theorem serialize_true : SszType.serialize true = .ok ⟨#[0x01]⟩ := by
  have shape : SszType.desc Bool = .bool := rfl
  have value : SszType.toValue true = .bool true := rfl
  simp only [SszType.serialize, shape, value, serialize]
  rfl

/-- A byte other than `0x00` and `0x01` is no `boolean`. -/
theorem deserialize_bool_two : SszType.deserialize Bool ⟨#[0x02]⟩ = .error (.notABit 2) := by
  have shape : SszType.desc Bool = .bool := rfl
  simp only [SszType.deserialize, shape, deserialize]
  rfl

/-- The bits `1, 0, 1` of a `Bitvector[3]` fill one byte from its lowest bit: `0b101`. -/
theorem serialize_bitvector :
    SszType.serialize (⟨#v[true, false, true]⟩ : Bitvector 3) = .ok ⟨#[0x05]⟩ := by
  have shape : SszType.desc (Bitvector 3) = .bitVector 3 := rfl
  have value : SszType.toValue (⟨#v[true, false, true]⟩ : Bitvector 3) =
    .bits #[true, false, true] := rfl
  simp only [SszType.serialize, shape, value, serialize]
  rfl

/-- The bits `1, 0, 1` of a `Bitlist[8]` take a closing bit above them: `0b1101`. -/
theorem serialize_bitlist :
    SszType.serialize (⟨#[true, false, true], by decide⟩ : Bitlist 8) = .ok ⟨#[0x0d]⟩ := by
  have shape : SszType.desc (Bitlist 8) = .bitList 8 := rfl
  have value : SszType.toValue (⟨#[true, false, true], by decide⟩ : Bitlist 8) =
    .bits #[true, false, true] := rfl
  simp only [SszType.serialize, shape, value, serialize]
  rfl

/-- Two fixed fields are written one after the other. -/
theorem serialize_fixedPair :
    SszType.serialize (⟨0x4567, 0x0123⟩ : FixedPair) = .ok ⟨#[0x67, 0x45, 0x23, 0x01]⟩ := by
  have shape : SszType.desc FixedPair = .container ["a", "b"] [.uint 2, .uint 2] := rfl
  have value : SszType.toValue (⟨0x4567, 0x0123⟩ : FixedPair) =
    .seq [.uint 0x4567, .uint 0x0123] := rfl
  simp only [SszType.serialize, shape, value, serialize, serializeStruct, serializeFields]
  rfl

/--
A variable field leaves a four-byte offset among the fixed fields, and its body follows.

The fixed part holds two bytes for `a` and four for the offset, so the body starts at byte 6.
-/
theorem serialize_mixedPair :
    SszType.serialize (⟨1, ⟨#[2, 3], by decide⟩⟩ : MixedPair) =
      .ok ⟨#[0x01, 0x00, 0x06, 0x00, 0x00, 0x00, 0x02, 0x00, 0x03, 0x00]⟩ := by
  have shape : SszType.desc MixedPair = .container ["a", "b"] [.uint 2, .list (.uint 2) 4] := rfl
  have value : SszType.toValue (⟨1, ⟨#[2, 3], by decide⟩⟩ : MixedPair) =
    .seq [.uint 1, .seq [.uint 2, .uint 3]] := rfl
  simp only [SszType.serialize, shape, value, serialize, serializeStruct, serializeFields,
    serializeSequence, serializeEach]
  rfl

end EthLib.Serialization.Ssz.KnownAnswers
