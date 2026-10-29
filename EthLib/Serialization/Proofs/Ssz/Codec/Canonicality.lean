import EthLib.Serialization.Proofs.Ssz.Codec.CanonicalComposite
import EthLib.Serialization.Proofs.Ssz.Codec.CanonicalStruct
import EthLib.Serialization.Proofs.Ssz.Codec.StructOrder

/-! Decoding accepts exactly the canonical encodings of well-formed types. -/

namespace EthLib.Serialization.Ssz

/-- Every accepted encoding of a well-formed declaration is reproduced exactly. -/
theorem serialize_of_deserialize (shape : Desc) :
    shape.wellFormed = .ok () → ∀ data value,
      deserialize shape data = .ok value → serialize shape value = .ok data := by
  -- Induct over the declaration, with a companion induction over its nested field types.
  induction shape using Desc.rec
    (motive_2 := fun fields => ∀ field ∈ fields, field.wellFormed = .ok () → ∀ data value,
      deserialize field data = .ok value → serialize field value = .ok data) with
  | bool => intro _ _ _ read; exact canonical_bool read
  | uint width => intro _ _ _ read; exact canonical_uint read
  | byteVector length => intro _ _ _ read; exact canonical_byteVector read
  | byteList limit => intro _ _ _ read; exact canonical_byteList read
  | bitVector length => intro _ _ _ read; exact canonical_bitVector read
  | bitList limit => intro _ _ _ read; exact canonical_bitList read
  | progressiveBitList => intro _ _ _ read; exact canonical_progressiveBitList read
  | vector element count ih =>
    intro legal data value read
    -- A legal vector has at least one element, so its fixed-width or offset layout fixes the entire byte budget.
    have positive : 0 < count := Nat.pos_of_ne_zero fun zero => by
      simp [Desc.wellFormed, zero, Bind.bind, Except.bind] at legal
    exact canonical_vector positive (ih (wellFormed_vector legal)) read
  | list element limit ih =>
    intro legal data value read
    exact canonical_list (ih (wellFormed_list legal)) read
  | progressiveList element limit ih =>
    intro legal data value read
    exact canonical_progressiveList (ih (wellFormed_progressiveList legal)) read
  | container names fields ih | progressiveContainer active names fields ih =>
    intro legal data value read
    have fieldsLegal : Desc.allWellFormed fields = .ok () := by
      first | exact wellFormed_container legal | exact wellFormed_progressiveContainer legal
    -- Each field re-encodes its own slice, and the offset layout reconstructs the whole input.
    cases struct : deserializeStruct fields data with
    | error fault => simp [deserialize, struct, Bind.bind, Except.bind] at read
    | ok values =>
      simp [deserialize, struct, Bind.bind, Except.bind, pure, Except.pure] at read
      subst value
      obtain ⟨slices, parts, decoded⟩ := deserializeStruct_ok struct
      have encoded := serializeFields_of_deserializeFields fields slices _
        (fun field member => ih field member (allWellFormed_mem fields fieldsLegal field member))
        decoded
      simp [serialize, serializeStruct, encoded, Bind.bind, Except.bind,
        structSlices_assemble_inverse fields data slices parts]
  -- Only the selected option needs reconstruction, using its own canonical encoding.
  | compatibleUnion selectors options ih =>
    intro legal data value read
    exact canonical_union (fun option member =>
      ih option member (allWellFormed_mem options (wellFormed_union legal) option member)) read
  | nil => rename_i field member legal data value read; simp at member
  | cons field fields ihHead ihTail =>
    rename_i held member legal data value read
    -- A nested type is either the first declaration or belongs to the remaining declarations.
    rcases List.mem_cons.mp member with rfl | later
    · exact ihHead legal data value read
    · exact ihTail held later legal data value read

/-- Successful serialization and successful deserialization describe the same relation. -/
theorem serialize_iff_deserialize {shape : Desc} {value : Value} {data : Bytes}
    (legal : shape.wellFormed = .ok ()) :
    serialize shape value = .ok data ↔ deserialize shape data = .ok value := by
  -- The two round-trip directions exclude both lost values and alternative encodings.
  exact ⟨roundTrip_of_encoding legal, serialize_of_deserialize shape legal data value⟩

/-- A well-formed type cannot accept two different byte strings for the same value. -/
theorem deserialize_injective {shape : Desc} {left right : Bytes} {value : Value}
    (legal : shape.wellFormed = .ok ())
    (first : deserialize shape left = .ok value)
    (second : deserialize shape right = .ok value) : left = right := by
  -- Each accepted byte string must equal the serialization of the common decoded value.
  have one := serialize_of_deserialize shape legal left value first
  have two := serialize_of_deserialize shape legal right value second
  -- The encoder has only one result, so the original byte strings must coincide.
  exact Except.ok.inj (one.symm.trans two)

end EthLib.Serialization.Ssz
