import EthLib.Serialization.Proofs.Ssz.Codec.CanonicalBits

/-! Reassembling the byte ranges accepted by composite decoders. -/

namespace EthLib.Serialization.Ssz

/-- Adjacent, ordered byte ranges concatenate without gaps or overlap. -/
theorem extract_join (data : Bytes) {start middle stop : Nat}
    (ordered : start ≤ middle) (onward : middle ≤ stop) :
    data.extract start middle ++ data.extract middle stop = data.extract start stop := by
  -- The two intervals share exactly one boundary, so they merge into one interval.
  rw [Array.extract_append_extract, Nat.min_eq_left ordered, Nat.max_eq_right onward]

/-- Concatenating two lists of parts concatenates their byte representations. -/
theorem concatParts_append (left right : List Bytes) :
    concatParts (left ++ right) = concatParts left ++ concatParts right := by
  -- Byte concatenation associates in the same way as concatenating the lists of parts.
  induction left with
  | nil => simp [concatParts]
  | cons head tail ih => simp [concatParts, ih, Array.append_assoc]

/-- Equal-width slices cover precisely the byte interval occupied by their elements. -/
theorem concat_fixed_slices (data : Bytes) (width count : Nat)
    (bounded : width * count ≤ data.size) :
    concatParts ((List.range count).map fun index =>
      data.extract (index * width) ((index + 1) * width)) = data.extract 0 (count * width) := by
  -- Grow the covered prefix by one complete element-width interval.
  induction count with
  | zero => simp [concatParts]
  | succ count ih =>
    -- Separate the final slice from the already reconstructed prefix.
    rw [List.range_succ, List.map_append, concatParts_append, ih (Nat.le_trans (Nat.mul_le_mul_left width (by omega)) bounded)]
    simp only [List.map_cons, List.map_nil, concatParts, Array.append_empty]
    -- Their common boundary prevents both missing bytes and overlapping bytes.
    exact extract_join data (by omega) (Nat.mul_le_mul_right width (by omega))

/-- Reading an integer inside a slice agrees with reading the same bytes in the source. -/
theorem readUint_extract (data : Bytes) (start stop : Nat) :
    ∀ offset width, offset + width ≤ stop - start → stop ≤ data.size →
      readUint (data.extract start stop) offset width = readUint data (start + offset) width := by
  intro offset width
  induction width generalizing offset with
  | zero => intros; rfl
  | succ width ih =>
    intro room bounded
    -- Both reads take the same first byte and advance by one position.
    have inside : offset < (data.extract start stop).size := by simp; omega
    have source : start + offset < data.size := by omega
    simp only [readUint, Array.getElem?_eq_getElem inside,
      Array.getElem?_eq_getElem source, Option.getD_some, Array.getElem_extract]
    rw [ih (offset + 1) (by omega) bounded]
    congr 2

/-- Writing an integer read from a bounded byte range reconstructs that exact range. -/
theorem uintBytes_readUint_slice (data : Bytes) (start width : Nat)
    (bounded : start + width ≤ data.size) :
    uintBytes width (readUint data start width) = data.extract start (start + width) := by
  -- The bounded interval contains exactly the requested number of bytes.
  have sized : (data.extract start (start + width)).size = width := by simp; omega
  -- Reading relative to the slice and reading at its absolute source position agree.
  have read := readUint_extract data start (start + width) 0 width (by omega) bounded
  simp only [Nat.add_zero] at read
  -- Apply whole-byte reconstruction to that isolated interval.
  have written := uintBytes_readUint (data.extract start (start + width))
  simpa only [sized, read] using written

/-- Offset spans partition the body and recover the offsets from the resulting slice widths. -/
theorem offsetSpans_partition (data : Bytes) :
    ∀ start rest scope spans,
      offsetSpans (start :: rest) scope = .ok spans → scope ≤ data.size →
      let parts := ((start :: rest).zip spans).map fun (at_, width) =>
        data.extract at_ (at_ + width)
      start ≤ scope ∧ runningOffsets start parts = start :: rest ∧
        concatParts parts = data.extract start scope := by
  intro start rest
  -- Each adjacent pair of offsets determines one body interval.
  induction rest generalizing start with
  | nil =>
    intro scope spans read bounded
    simp only [offsetSpans] at read
    split at read
    · cases read
    · cases read
      -- The final interval ends at the scope boundary even when its length is zero.
      have finish : start + (scope - start) = scope := by omega
      simp [finish, runningOffsets, concatParts]
      omega
  | cons next rest ih =>
    intro scope spans read bounded
    simp only [offsetSpans] at read
    split at read
    · cases read
    · cases tail : offsetSpans (next :: rest) scope <;>
        simp only [tail, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq,
          reduceCtorEq] at read
      subst spans
      rename_i widths
      -- The remaining offsets already reconstruct the suffix and its running positions.
      obtain ⟨within, offsets, joined⟩ := ih next scope widths tail bounded
      -- Monotonic offsets make subtraction exact when recovering the next boundary.
      have finish : start + (next - start) = next := by omega
      have sized : (data.extract start next).size = next - start := by simp; omega
      simp only [List.zip_cons_cons, List.map_cons, finish, runningOffsets,
        sized, concatParts]
      rw [offsets, joined]
      -- Joining the first interval to the reconstructed suffix covers the entire body.
      exact ⟨by omega, rfl, extract_join data (by omega) within⟩

/-- The offset header is exactly the little-endian encoding of its running body positions. -/
theorem headOf_offsets (parts : List Bytes) (start : Nat) :
    headOf start (offsetSlots parts) =
      concatParts ((runningOffsets start parts).map (uintBytes bytesPerOffset)) := by
  -- Each variable-sized part contributes one four-byte start position to the header.
  induction parts generalizing start with
  | nil => rfl
  | cons part rest ih =>
    simp [offsetSlots_cons, headOf, runningOffsets, concatParts, ih]

/-- Reading and rewriting a bounded offset table preserves every header byte. -/
theorem readOffsets_bytes (data : Bytes) (count : Nat)
    (bounded : count * bytesPerOffset ≤ data.size) :
    concatParts ((readOffsets data count).map (uintBytes bytesPerOffset)) =
      data.extract 0 (count * bytesPerOffset) := by
  -- View the header as consecutive four-byte integer encodings.
  simp only [readOffsets, List.map_map, Function.comp_def]
  have parts : (List.range count).map (fun index =>
      uintBytes bytesPerOffset (readUint data (index * bytesPerOffset) bytesPerOffset)) =
      (List.range count).map (fun index =>
        data.extract (index * bytesPerOffset) ((index + 1) * bytesPerOffset)) := by
    -- Reconstruct each entry from its original four-byte slice.
    apply List.map_congr_left
    intro index member
    have less : index < count := List.mem_range.mp member
    -- The table-size bound keeps every complete entry inside the input.
    have last : index * bytesPerOffset + bytesPerOffset ≤ data.size := by
      simpa only [Nat.add_mul, Nat.one_mul] using
        Nat.le_trans (Nat.mul_le_mul_right bytesPerOffset (show index + 1 ≤ count by omega)) bounded
    simpa only [Nat.add_mul, Nat.one_mul] using
      uintBytes_readUint_slice data (index * bytesPerOffset) bytesPerOffset last
  -- Those adjacent entries cover the entire header prefix.
  rw [parts, concat_fixed_slices data bytesPerOffset count (by simpa [Nat.mul_comm] using bounded)]

/-- Reconstructed parts are accepted when their combined encoding fits the offset range. -/
theorem assemble_of_parts {inline : List Bool} {parts : List Bytes} {data : Bytes}
    (same : headOf (headWidth (inline.zip parts)) (inline.zip parts) ++
      bodiesOf (inline.zip parts) = data)
    (bounded : data.size < 2 ^ (8 * bytesPerOffset)) : assemble inline parts = .ok data := by
  -- The reconstructed header and body have the same total width as the accepted input.
  have sized := congrArg Array.size same
  simp only [Array.size_append, headOf_size, bodiesOf_size] at sized
  -- That width lies below 2^32, so assembly returns the reconstructed bytes.
  simp [assemble, show ¬headWidth (inline.zip parts) + bodyWidth (inline.zip parts) ≥
    2 ^ (8 * bytesPerOffset) by omega, same, pure, Except.pure]

/-- Fixed-size slices reassemble to the original composite encoding. -/
theorem assemble_fixed_slices (data : Bytes) (width count : Nat)
    (sized : data.size = count * width) (bounded : data.size < 2 ^ (8 * bytesPerOffset)) :
  -- Fixed-size elements occupy consecutive intervals with no offset entries.
    let parts := (List.range count).map fun index =>
      data.extract (index * width) ((index + 1) * width)
    assemble (parts.map fun _ => true) parts = .ok data := by
  let parts := (List.range count).map fun index =>
    data.extract (index * width) ((index + 1) * width)
  -- It remains to show that placing these intervals inline recovers the message.
  apply assemble_of_parts (bounded := bounded)
  change headOf (headWidth (inlineSlots parts)) (inlineSlots parts) ++
    bodiesOf (inlineSlots parts) = data
  -- The inline header contains every element byte and leaves no separate body.
  rw [headOf_inline, bodiesOf_inline, Array.append_empty,
    show concatParts parts = data.extract 0 (count * width) from
      concat_fixed_slices data width count (by simp [sized, Nat.mul_comm]), ← sized, Array.extract_size]

/-- An ordered offset table and its bodies reassemble to their exact original bytes. -/
theorem assemble_offset_slices (data : Bytes) (count : Nat) (spans : List Nat)
    (positive : 0 < count) (room : count * bytesPerOffset ≤ data.size)
    (first : (readOffsets data count)[0]! = count * bytesPerOffset)
    (read : offsetSpans (readOffsets data count) data.size = .ok spans)
    (bounded : data.size < 2 ^ (8 * bytesPerOffset)) :
  -- Pair every start offset with the span ending at the next offset or end of input.
    let parts := ((readOffsets data count).zip spans).map fun (start, width) =>
      data.extract start (start + width)
    assemble (parts.map fun _ => false) parts = .ok data := by
  let parts := ((readOffsets data count).zip spans).map fun (start, width) =>
    data.extract start (start + width)
  -- Every offset contributes exactly one element slice.
  have countIs : parts.length = count := by
    have sized := offsetSpans_length read
    simp [readOffsets] at sized
    simp [parts, readOffsets, sized]
  -- The slices recover both the original start offsets and the complete body suffix.
  have partition : runningOffsets (count * bytesPerOffset) parts = readOffsets data count ∧
      concatParts parts = data.extract (count * bytesPerOffset) data.size := by
    cases offsets : readOffsets data count with
    | nil => have sized := congrArg List.length offsets; simp [readOffsets] at sized; omega
    | cons start rest =>
      rw [offsets] at read first
      have startIs : start = count * bytesPerOffset := by simpa using first
      have partition := offsetSpans_partition data start rest data.size spans read (by omega)
      simpa only [parts, offsets, startIs] using partition.2
  -- Reconstruct the header independently, then join it to the reconstructed body.
  have raw : headOf (headWidth ((parts.map fun _ => false).zip parts))
      ((parts.map fun _ => false).zip parts) ++ bodiesOf ((parts.map fun _ => false).zip parts)
      = data := by
    change headOf (headWidth (offsetSlots parts)) (offsetSlots parts) ++
      bodiesOf (offsetSlots parts) = data
    rw [headWidth_offset, countIs, headOf_offsets, partition.1,
      readOffsets_bytes data count room, bodiesOf_offset, partition.2,
      extract_join data (by omega) room, Array.extract_size]
  -- The original accepted size guarantees that assembling these parts is permitted.
  exact assemble_of_parts raw bounded

/-- Every accepted positive-length vector can be reconstructed from its decoded slices. -/
theorem vectorSlices_assemble {element : Desc} {count : Nat} {data : Bytes}
    {slices : List Bytes} (positive : 0 < count)
    (read : vectorSlices element count data = .ok slices) :
    assemble (slices.map fun _ => element.isFixed) slices = .ok data := by
  -- Fixed-size elements use adjacent intervals, while variable-size elements use an offset table.
  cases fixed : element.fixedSize with
  | some width =>
    simp [vectorSlices, fixed, throw_error, Bind.bind, Except.bind, pure, Except.pure] at read
    repeat' split at read
    all_goals simp_all
    subst slices
    simp only [Desc.isFixed, fixed, Option.isSome_some]
    -- The decoder has established the exact total length and the composite size bound.
    apply assemble_fixed_slices <;> first | omega | simp_all [Nat.mul_comm]
  | none =>
    simp [vectorSlices, fixed, throw_error, Bind.bind, Except.bind, pure, Except.pure,
      Nat.ne_of_gt positive] at read
    repeat' split at read
    all_goals simp_all
    subst slices
    simp only [Desc.isFixed, fixed, Option.isSome_none]
    -- Acceptance supplies the header boundary, monotonic offsets, and the final scope.
    apply assemble_offset_slices <;> first | assumption | omega | simp_all

private theorem readOffsets_first (data : Bytes) (count : Nat) (positive : 0 < count) :
    (readOffsets data count)[0]! = readUint data 0 bytesPerOffset := by
  -- A nonempty table starts with the four-byte integer at the beginning of the input.
  cases count with
  | zero => omega
  | succ count => simp [readOffsets, List.range_succ_eq_map]

/-- Every accepted list can be reconstructed from its decoded slices. -/
theorem listSlices_assemble {element : Desc} {limit : Option Nat} {data : Bytes}
    {slices : List Bytes} (read : listSlices element limit data = .ok slices) :
    assemble (slices.map fun _ => element.isFixed) slices = .ok data := by
  -- Capacity affects admissibility but not reconstruction of accepted element boundaries.
  cases fixed : element.fixedSize <;> cases limit <;>
    simp [listSlices, fixed, throw_error, Bind.bind, Except.bind, pure, Except.pure] at read
  all_goals repeat' split at read
  all_goals simp_all
  -- An empty input reconstructs directly as an empty list encoding.
  all_goals try (subst slices; simp [assemble, headWidth, bodyWidth, headOf, bodiesOf]; rfl)
  all_goals
    subst slices
    simp only [Desc.isFixed, fixed, Option.isSome_none, Option.isSome_some]
    -- Nonempty inputs reconstruct either by equal-width intervals or by the accepted offset table.
    first
    | apply assemble_fixed_slices
      -- The decoder rejects partial fixed-size elements, making count-times-width exact.
      · exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero ‹_›)).symm
      · assumption
    | apply assemble_offset_slices
      all_goals try rw [readOffsets_first data _ (by simp_all only [bytesPerOffset]; omega)]
      all_goals first | assumption | (simp_all only [bytesPerOffset]; omega)

end EthLib.Serialization.Ssz
