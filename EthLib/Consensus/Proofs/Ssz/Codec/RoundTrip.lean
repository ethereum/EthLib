import EthLib.Consensus.Proofs.Ssz.Codec.RoundTripSlices
import EthLib.Consensus.Proofs.Ssz.Codec.StructOrder

/-! Round trips, widths, and encoder injectivity for every well-formed type. -/

namespace EthLib.Consensus.Ssz

/--
A value of a covered shape survives being written and read back.

Stated over the type universe rather than per type, so a shape is covered once and for every value it admits.
-/
theorem recovered {shape : Desc} (covered : Recovers shape) :
    ∀ {value : Value}, Fits shape value → Recovered shape value := by
  induction covered with
  | bool =>
    intro _ admits
    cases admits with
    | bool b =>
      refine ⟨reads_back (roundTrip_bool b), fun _ _ fixed wrote => ?_⟩
      simp only [Desc.fixedSize, Option.some.injEq, serialize, Except.ok.injEq] at fixed wrote
      subst fixed wrote
      simp
  | uint =>
    intro _ admits
    cases admits with
    | uint bound =>
      refine ⟨reads_back (roundTrip_uint bound), fun _ _ fixed wrote => ?_⟩
      simp only [Desc.fixedSize, Option.some.injEq, serialize, bound, ↓reduceIte,
        Except.ok.injEq] at fixed wrote
      subst fixed wrote
      exact uintBytes_size _ _
  | byteVector =>
    intro _ admits
    cases admits with
    | byteVector exact =>
      exact ⟨roundTrip_byteVector exact, fun _ _ fixed wrote => by
        simp [Desc.fixedSize, serialize, exact, throw, throwThe, MonadExceptOf.throw,
          Bind.bind, Except.bind, Pure.pure, Except.pure] at fixed wrote
        split at wrote <;> simp_all⟩
  | byteList =>
    intro _ admits
    cases admits with
    | byteList within => exact ⟨roundTrip_byteList within, by simp [Desc.fixedSize]⟩
  | bitVector =>
    intro _ admits
    cases admits with
    | bitVector exact =>
      refine ⟨reads_back (roundTrip_bitVector exact), fun _ _ fixed wrote => ?_⟩
      simp only [Desc.fixedSize, Option.some.injEq, serialize, exact, BEq.rfl, ↓reduceIte, packBits,
        Except.ok.injEq] at fixed wrote
      subst fixed wrote
      simp
  | bitList =>
    intro _ admits
    cases admits with
    | bitList within => exact ⟨reads_back (roundTrip_bitList within), by simp [Desc.fixedSize]⟩
  | progressiveBitList _ =>
    intro _ admits
    cases admits with
    | progressiveBitList within =>
      exact ⟨reads_back (roundTrip_progressiveBitList within), by simp [Desc.fixedSize]⟩
  | @vectorFixed element length width fixed _ ih =>
    intro _ admits
    cases admits with
    | vector count each =>
      rename_i elements
      have facts : ∀ value ∈ elements, Recovered element value := fun value member =>
        ih (each value member)
      have prepared := recovered_sequence element elements width fixed facts
      refine ⟨?_, ?_⟩
      · intro bytes wrote
        simp only [serialize, count, beq_self_eq_true, ite_eq_left] at wrote
        obtain ⟨parts, lengths, widths, bytesIs, decoded⟩ := prepared bytes wrote
        subst bytesIs
        have counted : parts.length = length := by omega
        have sizeIs : (concatParts parts).size = width * length := by
          rw [concatParts_size width parts widths, counted, Nat.mul_comm]
        have nameable := serializeSequence_size_lt wrote
        rw [sizeIs, ← counted] at nameable
        simp only [deserialize, vectorSlices, fixed, sizeIs,
          ite_eq_right (Nat.not_le.mpr nameable), bne_self_eq_false, ite_eq_right,
          Bool.false_eq_true, not_false_eq_true, ← counted]
        rw [map_extract_concatParts width parts widths]
        simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, decoded]
      · intro size bytes fixedSize wrote
        simp only [serialize, count, beq_self_eq_true, ite_eq_left] at wrote
        obtain ⟨parts, lengths, widths, bytesIs, _⟩ := prepared bytes wrote
        subst bytesIs
        simp only [Desc.fixedSize, fixed, Option.map_some, Option.some.injEq] at fixedSize
        rw [concatParts_size width parts widths, ← fixedSize, show parts.length = length by omega,
          Nat.mul_comm]
  | @listFixed element limit width fixed positive _ ih =>
    intro _ admits
    cases admits with
    | list within each =>
      rename_i elements
      have facts : ∀ value ∈ elements, Recovered element value := fun value member =>
        ih (each value member)
      refine ⟨?_, by simp [Desc.fixedSize]⟩
      intro bytes wrote
      simp only [serialize, ite_eq_left within] at wrote
      obtain ⟨parts, lengths, widths, bytesIs, decoded⟩ :=
        recovered_sequence element elements width fixed facts bytes wrote
      subst bytesIs
      -- Recover the common-width slices before invoking the element round trips.
      have sliced := listSlices_concat_fixed fixed positive parts widths (some limit)
        (by intro cap equal; cases equal; omega) (serializeSequence_size_lt wrote)
      simp only [deserialize, sliced, decoded, Bind.bind, Except.bind]
      rfl
  | @progressiveListFixed element limit width fixed positive _ ih =>
    intro _ admits
    cases admits with
    | progressiveList within each =>
      rename_i elements
      have facts : ∀ value ∈ elements, Recovered element value := fun value member =>
        ih (each value member)
      refine ⟨?_, by simp [Desc.fixedSize]⟩
      intro bytes wrote
      simp only [serialize, boundCheck_of_withinBound limit _ within, Bind.bind,
        Except.bind] at wrote
      obtain ⟨parts, lengths, widths, bytesIs, decoded⟩ :=
        recovered_sequence element elements width fixed facts bytes wrote
      subst bytesIs
      -- Recover the common-width slices before invoking the element round trips.
      have sliced := listSlices_concat_fixed fixed positive parts widths limit
        (by intro cap named; rw [lengths]; simpa [withinBound, named] using within)
        (serializeSequence_size_lt wrote)
      simp only [deserialize, sliced, decoded, Bind.bind, Except.bind]
      rfl
  | @vectorVarying element length varying _ ih =>
    intro _ admits
    cases admits with
    | vector count each =>
      rename_i elements
      have facts : ∀ value ∈ elements, Recovered element value := fun value member =>
        ih (each value member)
      refine ⟨?_, by simp [Desc.fixedSize, varying]⟩
      intro bytes wrote
      simp only [serialize, count, beq_self_eq_true, ite_eq_left] at wrote
      obtain ⟨parts, lengths, bytesIs, nameable, decoded⟩ :=
        recovered_sequence_offset element elements varying facts bytes wrote
      subst bytesIs
      have counted : parts.length = length := by omega
      subst counted
      have sizeIs := offset_encoding_size parts
      have frontIs : (headOf (parts.length * bytesPerOffset) (offsetSlots parts)).size
          = parts.length * bytesPerOffset := by rw [headOf_size, headWidth_offset]
      match parts, lengths, nameable, decoded, sizeIs, frontIs with
      | [], lengths, nameable, decoded, sizeIs, frontIs =>
        -- No elements, so the table is empty and so is the encoding.
        have none : elements = [] := List.eq_nil_of_length_eq_zero lengths.symm
        subst none
        simp [deserialize, vectorSlices, varying, headOf, concatParts, deserializeEach]
        rfl
      | part :: rest, lengths, nameable, decoded, sizeIs, frontIs =>
        simp only [deserialize, vectorSlices, varying, sizeIs,
          ite_eq_right (Nat.not_le.mpr nameable),
          ite_eq_right (show ¬ ((part :: rest).length * bytesPerOffset
            + bodyWidth (offsetSlots (part :: rest))
            < (part :: rest).length * bytesPerOffset) by omega),
          show ¬ ((part :: rest).length == 0) = true by simp,
          readOffsets_headOf (part :: rest) _ _ nameable,
          runningOffsets_head, bne_self_eq_false,
          offsetSpans_runningOffsets, Bool.false_eq_true, ite_false,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
        have extracted := map_extract_offsets (part :: rest)
          (headOf ((part :: rest).length * bytesPerOffset) (offsetSlots (part :: rest)))
        rw [frontIs] at extracted
        rw [extracted]
        simp [decoded]
  | @listVarying element limit varying _ ih =>
    intro _ admits
    cases admits with
    | list within each =>
      rename_i elements
      have facts : ∀ value ∈ elements, Recovered element value := fun value member =>
        ih (each value member)
      refine ⟨?_, by simp [Desc.fixedSize]⟩
      intro bytes wrote
      simp only [serialize, ite_eq_left within] at wrote
      obtain ⟨parts, lengths, bytesIs, nameable, decoded⟩ :=
        recovered_sequence_offset element elements varying facts bytes wrote
      subst bytesIs
      -- Recover the offset-delimited slices before invoking the element round trips.
      have sliced := listSlices_offset_parts varying parts (some limit)
        (by intro cap equal; cases equal; omega) nameable
      simp only [deserialize, sliced, decoded, Bind.bind, Except.bind]
      rfl
  | @progressiveListVarying element limit varying _ ih =>
    intro _ admits
    cases admits with
    | progressiveList within each =>
      rename_i elements
      have facts : ∀ value ∈ elements, Recovered element value := fun value member =>
        ih (each value member)
      refine ⟨?_, by simp [Desc.fixedSize]⟩
      intro bytes wrote
      simp only [serialize, boundCheck_of_withinBound limit _ within, Bind.bind,
        Except.bind] at wrote
      obtain ⟨parts, lengths, bytesIs, nameable, decoded⟩ :=
        recovered_sequence_offset element elements varying facts bytes wrote
      subst bytesIs
      -- Recover the offset-delimited slices before invoking the element round trips.
      have sliced := listSlices_offset_parts varying parts limit
        (by intro cap named; rw [lengths]; simpa [withinBound, named] using within) nameable
      simp only [deserialize, sliced, decoded, Bind.bind, Except.bind]
      rfl
  | @container _ fields _ ih | @progressiveContainer _ _ fields _ ih =>
    intro _ admits
    cases admits
    rename_i values paired each
    have facts : ∀ pair ∈ fields.zip values, Recovered pair.1 pair.2 := fun pair member =>
      ih pair.1 (List.of_mem_zip member).1 (each pair member)
    obtain ⟨reads, widths⟩ := recovered_struct fields values paired facts
    refine ⟨fun bytes wrote => ?_, fun width bytes fixed wrote => widths width bytes
      (by simpa only [Desc.fixedSize] using fixed) (by simpa only [serialize] using wrote)⟩
    obtain ⟨parts, sliced, decoded⟩ := reads bytes (by simpa only [serialize] using wrote)
    simp only [deserialize, deserializeStruct_of sliced decoded, Bind.bind, Except.bind]
    rfl
  | compatibleUnion _ ih =>
    intro _ admits
    cases admits with
    | compatibleUnion bounded named innerFits =>
      -- The option the selector names is one the union declared, so it is covered too.
      exact ⟨roundTrip_compatibleUnion bounded named
        (ih _ (lookupOption_mem _ _ _ _ named) innerFits).1, by simp [Desc.fixedSize]⟩

/-- A value of a covered shape survives being written and read back. -/
theorem roundTrip {shape : Desc} {value : Value} {bytes : Bytes}
    (covered : Recovers shape) (admits : Fits shape value)
    (wrote : serialize shape value = .ok bytes) : deserialize shape bytes = .ok value :=
  (recovered covered admits).1 bytes wrote

/-- A covered shape of a declared width writes exactly that many bytes. -/
theorem serialize_size {shape : Desc} {value : Value} {width : Nat} {bytes : Bytes}
    (covered : Recovers shape) (admits : Fits shape value)
    (fixed : shape.fixedSize = some width) (wrote : serialize shape value = .ok bytes) :
    bytes.size = width := (recovered covered admits).2 width bytes fixed wrote

/--
Writing is injective on covered shapes, so no two values share an encoding.

This is non-malleability, and it costs nothing beyond the round trip.
-/
theorem serialize_injective {shape : Desc} {left right : Value}
    {bytes : Bytes} (covered : Recovers shape)
    (leftFits : Fits shape left) (rightFits : Fits shape right)
    (leftWrote : serialize shape left = .ok bytes)
    (rightWrote : serialize shape right = .ok bytes) : left = right := by
  -- Both values read back out of the one encoding they share.
  have leftBack := roundTrip covered leftFits leftWrote
  have rightBack := roundTrip covered rightFits rightWrote
  exact Except.ok.inj (leftBack.symm.trans rightBack)

/--
Every well-formed type is covered, and takes a byte where it declares a width.

Nothing is left outside the gate, so the round trip holds of every type the specification admits rather than of a list of them.
-/
theorem recovers_of_wellFormed : ∀ (shape : Desc), shape.wellFormed = .ok () →
    Recovers shape ∧ ∀ width, shape.fixedSize = some width → 0 < width := by
  intro shape
  -- Induct on SSZ types, independently of the order in which declarations are checked.
  induction shape using Desc.rec
    (motive_2 := fun fields => Desc.allWellFormed fields = .ok () →
      ∀ field ∈ fields, Recovers field
        ∧ ∀ width, field.fixedSize = some width → 0 < width) with
  | bool =>
    -- A boolean always occupies one byte.
    exact fun _ => ⟨.bool, by intro width fixed; simp [Desc.fixedSize] at fixed; omega⟩
  | uint width =>
    -- Each of the six permitted integer widths is positive.
    exact fun sound => ⟨.uint width, fun _ fixed => by
      rw [Desc.wellFormed] at sound; simp_all [Desc.fixedSize]; omega⟩
  | byteVector length =>
    -- A legal fixed byte string has at least one byte.
    exact fun sound => ⟨.byteVector length, fun _ fixed => by
      rw [Desc.wellFormed] at sound; simp_all [Desc.fixedSize]; omega⟩
  | bitVector length =>
    -- A positive bit count occupies at least one byte after rounding up.
    exact fun sound => ⟨.bitVector length, fun _ fixed => by
      rw [Desc.wellFormed] at sound; simp_all [Desc.fixedSize]; omega⟩
  | byteList limit =>
    -- Variable-size byte strings have no fixed width to prove positive.
    exact fun _ => ⟨.byteList limit, by simp [Desc.fixedSize]⟩
  | bitList limit =>
    -- The delimiter recovers the bit count, including an empty value.
    exact fun _ => ⟨.bitList limit, by simp [Desc.fixedSize]⟩
  | progressiveBitList limit =>
    -- A bound rules on the count alone, leaving the bit encoding as it is.
    exact fun _ => ⟨.progressiveBitList limit, by simp [Desc.fixedSize]⟩
  | vector element length ih =>
    intro sound
    obtain ⟨covered, positive⟩ := ih (wellFormed_vector sound)
    -- Fixed elements multiply their width by the positive element count.
    have nonempty : length ≠ 0 := by
      rintro rfl; simp [Desc.wellFormed, Bind.bind, Except.bind] at sound
    cases fixedIs : element.fixedSize with
    | none => exact ⟨.vectorVarying fixedIs covered, by simp [Desc.fixedSize, fixedIs]⟩
    | some width =>
      refine ⟨.vectorFixed fixedIs covered, fun answer fixed => ?_⟩
      simp only [Desc.fixedSize, fixedIs, Option.map_some, Option.some.injEq] at fixed
      exact fixed ▸ Nat.mul_pos (positive width fixedIs) (by omega)
  | list element limit ih =>
    intro sound
    obtain ⟨covered, positive⟩ := ih (wellFormed_list sound)
    -- A positive fixed width recovers the count by division.
    -- Offsets handle variable widths.
    refine ⟨?_, by simp [Desc.fixedSize]⟩
    cases fixedIs : element.fixedSize with
    | none => exact .listVarying fixedIs covered
    | some width => exact .listFixed fixedIs (positive width fixedIs) covered
  | progressiveList element limit ih =>
    intro sound
    obtain ⟨covered, positive⟩ := ih (wellFormed_progressiveList sound)
    -- The same element encoding works whether or not a bound is declared.
    refine ⟨?_, by simp [Desc.fixedSize]⟩
    cases fixedIs : element.fixedSize with
    | none => exact .progressiveListVarying fixedIs covered
    | some width => exact .progressiveListFixed fixedIs (positive width fixedIs) covered
  | container names fields ih =>
    intro sound
    have facts := ih (wellFormed_container sound)
    -- Each declared field is covered, and a legal container has at least one.
    have nonempty : ¬ fields.isEmpty = true := by
      intro empty
      simp [List.isEmpty_iff.mp empty, Desc.wellFormed, Bind.bind, Except.bind] at sound
    exact ⟨.container (fun field member => (facts field member).1),
      fun width fixed => fieldsFixedSize_pos fields width nonempty
        (fun field member => (facts field member).2) fixed⟩
  | progressiveContainer active names fields ih =>
    intro sound
    have facts := ih (wellFormed_progressiveContainer sound)
    -- Gaps change tree positions but do not contribute serialized fields.
    have nonempty : ¬ fields.isEmpty = true := by
      intro empty
      simp [Desc.wellFormed, empty, Bind.bind, Except.bind] at sound
      repeat' split at sound <;> simp_all
    exact ⟨.progressiveContainer (fun field member => (facts field member).1),
      fun width fixed => fieldsFixedSize_pos fields width nonempty
        (fun field member => (facts field member).2) fixed⟩
  | compatibleUnion selectors options ih =>
    intro sound
    -- Every option is covered, while the union itself is always variable-size.
    have facts := ih (wellFormed_union sound)
    exact ⟨.compatibleUnion (fun option member => (facts option member).1),
      by simp [Desc.fixedSize]⟩
  | nil =>
    -- An empty field list has no members requiring a proof.
    rename_i _ field member
    simp at member
  | cons field fields ih ihRest =>
    rename_i sound target member
    -- A field belongs either to the head or to the remaining declarations.
    rcases List.mem_cons.mp member with here | later
    · subst target
      exact ih (allWellFormed_mem _ sound field List.mem_cons_self)
    · exact ihRest (allWellFormed_tail sound) target later

/--
Writing a value of a real type and reading it back gives that value.

This holds of every type the specification admits, with nothing left to check first.
-/
theorem roundTrip_of_wellFormed {shape : Desc} {value : Value} {bytes : Bytes}
    (sound : shape.wellFormed = .ok ()) (admits : Fits shape value)
    (wrote : serialize shape value = .ok bytes) : deserialize shape bytes = .ok value :=
  roundTrip (recovers_of_wellFormed shape sound).1 admits wrote

/-- A real type of a declared width writes exactly that many bytes. -/
theorem serialize_size_of_wellFormed {shape : Desc} {value : Value} {width : Nat} {bytes : Bytes}
    (sound : shape.wellFormed = .ok ()) (admits : Fits shape value)
    (fixed : shape.fixedSize = some width) (wrote : serialize shape value = .ok bytes) :
    bytes.size = width :=
  serialize_size (recovers_of_wellFormed shape sound).1 admits fixed wrote

/--
No two values of a real type share an encoding.

Decoding a successfully written encoding therefore identifies its original value.
-/
theorem serialize_injective_of_wellFormed {shape : Desc} {left right : Value} {bytes : Bytes}
    (sound : shape.wellFormed = .ok ()) (leftFits : Fits shape left) (rightFits : Fits shape right)
    (leftWrote : serialize shape left = .ok bytes)
    (rightWrote : serialize shape right = .ok bytes) : left = right :=
  serialize_injective (recovers_of_wellFormed shape sound).1 leftFits rightFits leftWrote rightWrote

/-- A real type of a declared width takes room, no type of the specification being empty. -/
theorem fixedSize_pos_of_wellFormed {shape : Desc} {width : Nat}
    (sound : shape.wellFormed = .ok ()) (fixed : shape.fixedSize = some width) : 0 < width :=
  (recovers_of_wellFormed shape sound).2 width fixed

/--
Writing a value of a real type and reading it back gives that value.

Nothing has to hold of the value beyond the encoder having written it at all.
-/
theorem roundTrip_of_encoding {shape : Desc} {value : Value} {bytes : Bytes}
    (sound : shape.wellFormed = .ok ()) (wrote : serialize shape value = .ok bytes) :
    deserialize shape bytes = .ok value :=
  roundTrip_of_wellFormed sound (fits_of_serialize shape value sound ⟨bytes, wrote⟩) wrote

/-- An encoding of a real type is written by one value and no other. -/
theorem serialize_injective_of_encoding {shape : Desc} {left right : Value} {bytes : Bytes}
    (sound : shape.wellFormed = .ok ())
    (leftWrote : serialize shape left = .ok bytes)
    (rightWrote : serialize shape right = .ok bytes) : left = right :=
  -- Successful encodings supply admissibility, so decoding the common bytes identifies both original values.
  serialize_injective_of_wellFormed sound
    (fits_of_serialize shape left sound ⟨bytes, leftWrote⟩)
    (fits_of_serialize shape right sound ⟨bytes, rightWrote⟩) leftWrote rightWrote

/-- Whatever a real type of a declared width writes is exactly that many bytes. -/
theorem serialize_size_of_encoding {shape : Desc} {value : Value} {width : Nat} {bytes : Bytes}
    (sound : shape.wellFormed = .ok ()) (fixed : shape.fixedSize = some width)
    (wrote : serialize shape value = .ok bytes) : bytes.size = width :=
  serialize_size_of_wellFormed sound (fits_of_serialize shape value sound ⟨bytes, wrote⟩)
    fixed wrote

end EthLib.Consensus.Ssz
