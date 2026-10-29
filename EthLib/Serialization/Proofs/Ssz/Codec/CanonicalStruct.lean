import EthLib.Serialization.Proofs.Ssz.Codec.CanonicalTable

/-! Accepted container slices reconstruct their original header and bodies. -/

namespace EthLib.Serialization.Ssz

/-- Whether each slot holds its field in place or points to a body. -/
private def slotFlags : List Slot → List Bool
  | [] => []
  | .inline _ :: rest => true :: slotFlags rest
  | .body _ :: rest => false :: slotFlags rest

/-- The header bytes represented by already-read slots. -/
private def slotEncoding : List Slot → Bytes
  | [] => #[]
  | .inline bytes :: rest => bytes ++ slotEncoding rest
  | .body start :: rest => uintBytes bytesPerOffset start ++ slotEncoding rest

/-- Reading slots preserves their field kinds and every byte of their header interval. -/
private theorem readSlots_preserves (data : Bytes) :
    ∀ fields position slots ending, position ≤ data.size →
      readSlots fields data position = .ok (slots, ending) →
      position ≤ ending ∧ ending ≤ data.size ∧
      slotFlags slots = fields.map Desc.isFixed ∧
      slotEncoding slots = data.extract position ending := by
  intro fields
  -- The cursor advances through the header while preserving each field kind and its original bytes.
  induction fields with
  | nil =>
    intro position slots ending bounded read
    obtain ⟨rfl, rfl⟩ := by simpa [readSlots] using read
    simp [slotFlags, slotEncoding, bounded]
  | cons field fields ih =>
    intro position slots ending bounded read
    cases fixed : field.fixedSize with
    -- A fixed-size field contributes its complete value bytes to the header.
    | some width =>
      simp only [readSlots, fixed] at read
      split at read
      · simp [throw_error, Bind.bind, Except.bind] at read
      · cases tail : readSlots fields data (position + width) <;>
          simp [tail, Bind.bind, Except.bind, pure, Except.pure] at read
        obtain ⟨rfl, rfl⟩ := read
        -- The remaining fields reconstruct the adjacent suffix of the header.
        obtain ⟨onward, finalBound, flags, bytes⟩ := ih _ _ _ (by omega) tail
        refine ⟨by omega, finalBound, by simp [slotFlags, Desc.isFixed, fixed, flags], ?_⟩
        simp only [slotEncoding, bytes]
        exact extract_join data (by omega) onward
    -- A variable-size field contributes only its four-byte body offset.
    | none =>
      simp only [readSlots, fixed] at read
      split at read
      · simp [throw_error, Bind.bind, Except.bind] at read
      · cases tail : readSlots fields data (position + bytesPerOffset) <;>
          simp [tail, Bind.bind, Except.bind, pure, Except.pure] at read
        obtain ⟨rfl, rfl⟩ := read
        obtain ⟨onward, finalBound, flags, bytes⟩ := ih _ _ _ (by omega) tail
        refine ⟨by omega, finalBound, by simp [slotFlags, Desc.isFixed, fixed, flags], ?_⟩
        rw [slotEncoding, uintBytes_readUint_slice data position bytesPerOffset (by omega), bytes]
        exact extract_join data (by omega) onward

/-- A successful span list names the next boundary and leaves a valid tail. -/
private theorem offsetSpans_cons (data : Bytes) (scope start : Nat) (rest spans : List Nat)
    (bounded : scope ≤ data.size) (read : offsetSpans (start :: rest) scope = .ok spans) :
    ∃ width widths, spans = width :: widths ∧
      start ≤ rest.headD scope ∧ rest.headD scope ≤ scope ∧
      start + width = rest.headD scope ∧ offsetSpans rest scope = .ok widths := by
  -- The next offset closes a body, while the total scope closes the final body.
  cases rest with
  | nil =>
    simp only [offsetSpans] at read
    split at read
    · cases read
    · obtain rfl := by simpa using read
      refine ⟨scope - start, [], rfl, ?_, by simp, ?_, rfl⟩ <;> simp <;> omega
  | cons next rest =>
    simp only [offsetSpans] at read
    split at read
    · cases read
    · cases tail : offsetSpans (next :: rest) scope <;>
        simp [tail, Bind.bind, Except.bind, pure, Except.pure] at read
      subst spans
      -- The recursively accepted offsets keep the next boundary inside the message scope.
      have within := (offsetSpans_partition data next rest scope _ tail bounded).1
      refine ⟨next - start, _, rfl, ?_, ?_, ?_, rfl⟩ <;> simp <;> omega

/-- Filling body slots preserves the header and concatenates all bodies without gaps. -/
private theorem takeSlots_reassembles (data : Bytes) (scope : Nat) (bounded : scope ≤ data.size) :
    ∀ slots spans parts,
      offsetSpans (bodyStarts slots) scope = .ok spans →
      takeSlots data slots spans = .ok parts →
      let start := (bodyStarts slots).headD scope
      start ≤ scope ∧
      headOf start ((slotFlags slots).zip parts) = slotEncoding slots ∧
      bodiesOf ((slotFlags slots).zip parts) = data.extract start scope := by
  intro slots
  induction slots with
  | nil =>
    intro spans parts read taken
    obtain rfl := by simpa [takeSlots] using taken
    simp [bodyStarts, slotFlags, slotEncoding, headOf, bodiesOf]
    omega
  | cons slot slots ih =>
    intro spans parts read taken
    cases slot with
    | inline bytes =>
      -- An inline slot consumes no body span and adds its bytes only to the header.
      cases tail : takeSlots data slots spans <;>
        simp [takeSlots, tail, Bind.bind, Except.bind, pure, Except.pure] at taken
      subst parts
      obtain ⟨within, header, bodies⟩ := ih spans _ read tail
      simp only [bodyStarts, slotFlags, slotEncoding, List.zip_cons_cons, headOf, bodiesOf]
      exact ⟨within, congrArg (bytes ++ ·) header, bodies⟩
    | body start =>
      -- A body ends at the next offset, or at the end of the whole message.
      obtain ⟨width, widths, rfl, ordered, nextBound, finish, tailRead⟩ :=
        offsetSpans_cons data scope start (bodyStarts slots) spans bounded read
      cases tail : takeSlots data slots widths <;>
        simp [takeSlots, tail, Bind.bind, Except.bind, pure, Except.pure] at taken
      subst parts
      obtain ⟨-, header, bodies⟩ := ih widths _ tailRead tail
      have sliced : (data.extract start (start + width)).size = width := by
        simp only [Array.size_extract]
        omega
      simp only [bodyStarts, List.headD_cons, slotFlags, List.zip_cons_cons,
        headOf, bodiesOf, slotEncoding]
      rw [sliced, finish, header, bodies]
      exact ⟨by omega, rfl, extract_join data ordered nextBound⟩

/-- Slots with no bodies are already their own field slices. -/
private theorem takeSlots_no_bodies (data : Bytes) :
    ∀ slots, bodyStarts slots = [] → takeSlots data slots [] = .ok (slots.map Slot.held) := by
  intro slots
  -- The absence of body offsets rules out variable slots, leaving only stored inline bytes.
  induction slots with
  | nil => intro _; rfl
  | cons slot slots ih =>
    intro empty
    cases slot with
    | inline bytes =>
      simp [takeSlots, ih empty, Slot.held, Bind.bind, Except.bind, pure, Except.pure]
    | body start => simp [bodyStarts] at empty

/-- Header reconstruction and body coverage make the composite assembler total. -/
private theorem assemble_readSlots (fields : List Desc) (data : Bytes) (slots : List Slot)
    (leading : Nat) (spans : List Nat) (parts : List Bytes)
    (read : readSlots fields data 0 = .ok (slots, leading))
    (readSpans : offsetSpans (bodyStarts slots) data.size = .ok spans)
    (taken : takeSlots data slots spans = .ok parts)
    (first : (bodyStarts slots).headD data.size = leading)
    (bounded : data.size < 2 ^ (8 * bytesPerOffset)) :
    assemble (fields.map Desc.isFixed) parts = .ok data := by
  -- Recover the exact header interval and the fixed-versus-variable field pattern.
  obtain ⟨_, leadingBound, flags, encoded⟩ := readSlots_preserves data fields 0 slots leading
    (by omega) read
  -- Recover the separately stored bodies from the accepted offset spans.
  obtain ⟨_, header, bodies⟩ := takeSlots_reassembles data data.size (by omega)
    slots spans parts readSpans taken
  simp only [first] at header bodies
  -- The reconstructed header occupies exactly the prefix consumed by the slot reader.
  have width : headWidth ((slotFlags slots).zip parts) = leading := by
    have sized := congrArg Array.size header
    rw [headOf_size, encoded] at sized
    simpa [Nat.min_eq_left leadingBound] using sized
  -- The reconstructed header and body cover the input and respect its size bound.
  apply assemble_of_parts (bounded := bounded)
  rw [← flags, width, header, encoded, bodies]
  rw [extract_join data (by omega) leadingBound, Array.extract_size]

/-- Every accepted container slicing reassembles to the exact original encoding. -/
theorem structSlices_assemble_inverse (fields : List Desc) (data : Bytes) (parts : List Bytes)
    (read : structSlices fields data = .ok parts) :
    assemble (fields.map Desc.isFixed) parts = .ok data := by
  -- The decoder checks the same total-width bound as the encoder before reading slots.
  simp only [structSlices, structSlots, structBodies] at read
  split at read
  · simp [throw_error, Bind.bind, Except.bind] at read
  -- The budget is settled before the slots, so what the reader got past says nothing more.
  · cases budget : structBudget fields data.size <;> simp only [budget, Bind.bind, Except.bind] at read
    · simp at read
    rcases slotsRead : readSlots fields data 0 with _ | ⟨slots, leading⟩ <;>
      simp only [slotsRead] at read
    · simp at read
    split at read
    -- Without variable fields, the consumed header must be the entire input.
    · rename_i noBodies
      have absent : bodyStarts slots = [] := by simpa using noBodies
      split at read
      · simp [throw_error] at read
      · rename_i sized
        simp only [pure, Except.pure, Except.ok.injEq] at read
        subst parts
        apply assemble_readSlots fields data slots leading [] (slots.map Slot.held) slotsRead
        · simp [absent, offsetSpans]
        · exact takeSlots_no_bodies data slots absent
        · simp only [absent, List.headD_nil]
          simpa using sized
        · omega
    -- With variable fields, the first offset must begin exactly where the header ends.
    · rename_i hasBodies
      split at read
      · simp [throw_error] at read
      · rename_i begins
        cases spansRead : offsetSpans (bodyStarts slots) data.size <;> simp only [spansRead] at read
        · simp at read
        apply assemble_readSlots fields data slots leading _ parts slotsRead spansRead read
        · cases offsets : bodyStarts slots with
          | nil => simp [offsets] at hasBodies
          | cons start rest => simpa [offsets] using begins
        · omega

end EthLib.Serialization.Ssz
