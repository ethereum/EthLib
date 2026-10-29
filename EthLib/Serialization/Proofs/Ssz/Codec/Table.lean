import EthLib.Serialization.Ssz.Codec.Deserialize

/-! Reading back the offset table a struct or a sequence was laid out with. -/

namespace EthLib.Serialization.Ssz

/-- An integer takes exactly the width it was written at. -/
theorem uintBytes_size (width value : Nat) : (uintBytes width value).size = width := by
  -- The value shrinks by a factor of 256 at every step, so it stays quantified over.
  induction width generalizing value with
  -- No bytes were asked for, and none were written.
  | zero => rfl
  -- One byte was written and the rest is the same claim one width down.
  | succ width ih => simp only [uintBytes, Array.size_append, Array.size_singleton, ih]; omega

/-- Reading past a byte put on the front is reading the rest from one place earlier. -/
theorem readUint_shift (data : Bytes) (byte : UInt8) (start width : Nat) :
    readUint (#[byte] ++ data) (start + 1) width = readUint data start width := by
  -- The read moves along as the width shrinks, so the position stays quantified over.
  induction width generalizing start <;> simp_all [readUint, Array.getElem?_append]

/-- Reading past a run of bytes on the front is reading the rest from where it starts. -/
theorem readUint_append (front back : Bytes) (start width : Nat) :
    readUint (front ++ back) (front.size + start) width = readUint back start width := by
  -- The read moves along as the width shrinks, so the position stays quantified over.
  induction width generalizing start <;>
    simp_all [readUint, Array.getElem?_append_right, Nat.add_assoc]

/--
An integer written and read back at the same width is the integer written.

Stated with bytes allowed to follow, since an offset is read out of a longer encoding.
-/
theorem readUint_uintBytes_prefix (back : Bytes) (width value : Nat)
    (bound : value < 2 ^ (8 * width)) :
    readUint (uintBytes width value ++ back) 0 width = value := by
  induction width generalizing value with
  -- A width of no bytes holds only the value zero.
  | zero =>
    simp [readUint] at bound ⊢
    omega
  | succ width ih =>
    -- One more byte of width is one more factor of 256 of range.
    have step : 2 ^ (8 * (width + 1)) = 2 ^ (8 * width) * 256 := by
      rw [Nat.mul_succ, Nat.pow_add]
    -- So what is left after the low byte still fits the width that is left.
    have tail := ih (value / 256) (by omega)
    -- The first byte is the low byte, and the read continues into what the rest wrote.
    have shifted := readUint_shift (uintBytes width (value / 256) ++ back)
      (UInt8.ofNat (value % 256)) 0 width
    simp only [Nat.zero_add] at shifted
    simp [readUint, uintBytes, Array.append_assoc, shifted, tail, Array.getElem?_append]
    -- A number is its low byte plus 256 times the rest.
    omega

/--
An integer written and read back at the same width is the integer written.

The bound is the type's own.
An integer at or above what its width holds is no value of that type.
-/
theorem readUint_uintBytes (width value : Nat) (bound : value < 2 ^ (8 * width)) :
    readUint (uintBytes width value) 0 width = value := by
  -- This is the round trip with nothing following the integer.
  simpa using readUint_uintBytes_prefix #[] width value bound

/-- The slots a struct's fields and parts stand for. -/
def slotsOf (fields : List Desc) (parts : List Bytes) : List (Bool × Bytes) :=
  (fields.map Desc.isFixed).zip parts

/-- What reading the fixed part is meant to answer with. -/
def expectedSlots (bodyStart : Nat) : List Desc → List Bytes → List Slot
  | [], _ => []
  | _ :: _, [] => []
  | field :: fields, part :: parts =>
    -- Fixed fields retain their bytes, while variable fields record the next free body position.
    if field.isFixed then .inline part :: expectedSlots bodyStart fields parts
    else .body bodyStart :: expectedSlots (bodyStart + part.size) fields parts

/-- One field and its part put one slot on the front of both. -/
theorem slotsOf_cons (field : Desc) (fields : List Desc) (part : Bytes) (parts : List Bytes) :
    slotsOf (field :: fields) (part :: parts)
      = (field.isFixed, part) :: slotsOf fields parts := rfl

/-- An offset written at the front of what follows is read back where it was written. -/
private theorem readUint_offset (front rest : Bytes) {start : Nat}
    (bound : start < 2 ^ (8 * bytesPerOffset)) :
    readUint (front ++ (uintBytes bytesPerOffset start ++ rest)) front.size bytesPerOffset
      = start := by
  -- Skip the front, then read the integer back at its own width.
  simpa using (readUint_append front _ 0 bytesPerOffset).trans
    (readUint_uintBytes_prefix rest _ _ bound)

/--
The fixed part reads back the slots that wrote it.

The front is what already lies behind the read, which is how the induction moves along without the bounds it checks against changing.
-/
theorem readSlots_headOf :
    ∀ (fields : List Desc) (parts : List Bytes) (front bodies : Bytes) (bodyStart : Nat),
      fields.length = parts.length →
      (∀ pair ∈ fields.zip parts, ∀ width, pair.1.fixedSize = some width → pair.2.size = width) →
      bodyStart + bodyWidth (slotsOf fields parts) < 2 ^ (8 * bytesPerOffset) →
      readSlots fields (front ++ (headOf bodyStart (slotsOf fields parts) ++ bodies))
          front.size
        = .ok (expectedSlots bodyStart fields parts,
            front.size + headWidth (slotsOf fields parts)) := by
  intro fields
  induction fields with
  | nil =>
    intro parts front bodies bodyStart _ _ _
    simp [readSlots, slotsOf, expectedSlots, headWidth]
  | cons field fields ih =>
    intro parts front bodies bodyStart paired widths nameable
    cases parts with
    | nil => simp at paired
    | cons part parts =>
      rw [slotsOf_cons] at nameable ⊢
      have narrowed : ∀ pair ∈ fields.zip parts, ∀ w, pair.1.fixedSize = some w →
          pair.2.size = w := fun pair member => widths pair (List.mem_cons_of_mem _ member)
      -- Either the field is written in place, or an offset stands for it.
      cases fixed : field.fixedSize with
      | some width =>
        obtain rfl : part.size = width := widths (field, part) (by simp) width fixed
        simp only [headOf, bodyWidth, headWidth, ite_eq_left, expectedSlots,
          Desc.isFixed, fixed, Option.isSome_some] at nameable ⊢
        -- The rest of the read is the same claim with this field behind it.
        have inner := ih parts (front ++ part) bodies bodyStart
          (by simpa using paired) narrowed nameable
        simp only [Array.size_append, Array.append_assoc] at inner
        -- What was cut out is the whole of this field's own bytes.
        simp [readSlots, fixed, inner, Nat.add_assoc, Bind.bind, Except.bind, pure, Except.pure]
      | none =>
        simp only [headOf, bodyWidth, headWidth, expectedSlots, Desc.isFixed, fixed,
          Option.isSome_none, Bool.false_eq_true, ite_false] at nameable ⊢
        -- The offset stands in for the body, and the body follows the fixed part.
        have inner := ih parts (front ++ uintBytes bytesPerOffset bodyStart) bodies
          (bodyStart + part.size) (by simpa using paired) narrowed (by omega)
        simp only [Array.size_append, Array.append_assoc, uintBytes_size] at inner
        -- The offset written here is the one read back.
        simp [readSlots, fixed, inner, Array.append_assoc, uintBytes_size, Nat.add_assoc,
          readUint_offset _ _ (show bodyStart < _ by omega), Bind.bind, Except.bind, pure,
          Except.pure]

/-- Where each body begins, in the order the table names them. -/
def bodyOffsets (bodyStart : Nat) : List Desc → List Bytes → List Nat
  | [], _ => []
  | _ :: _, [] => []
  | field :: fields, part :: parts =>
    -- Only variable fields advance the body cursor and contribute an offset.
    if field.isFixed then bodyOffsets bodyStart fields parts
    else bodyStart :: bodyOffsets (bodyStart + part.size) fields parts

/-- How wide each body is, in the same order. -/
def bodySizes : List Desc → List Bytes → List Nat
  | [], _ => []
  | _ :: _, [] => []
  | field :: fields, part :: parts =>
    if field.isFixed then bodySizes fields parts else part.size :: bodySizes fields parts

/-- The offsets read out of the slots are the offsets the layout named. -/
theorem bodyStarts_expectedSlots :
    ∀ (fields : List Desc) (parts : List Bytes) (bodyStart : Nat),
      bodyStarts (expectedSlots bodyStart fields parts) = bodyOffsets bodyStart fields parts := by
  -- A field written in place names no offset, and any other names exactly one.
  intro fields parts bodyStart
  fun_induction expectedSlots bodyStart fields parts <;> simp_all [bodyStarts, bodyOffsets]

/-- The first body a layout names begins where the layout says the bodies begin. -/
theorem bodyOffsets_head :
    ∀ (fields : List Desc) (parts : List Bytes) (bodyStart next : Nat) (rest : List Nat),
      bodyOffsets bodyStart fields parts = next :: rest → next = bodyStart := by
  -- A field written in place names nothing, so the first name comes from later.
  intro fields parts bodyStart next rest named
  fun_induction bodyOffsets bodyStart fields parts <;> simp_all

/-- A layout that names no more bodies has no more body bytes, and no more widths. -/
theorem bodySizes_of_no_offsets :
    ∀ (fields : List Desc) (parts : List Bytes) (bodyStart : Nat),
      bodyOffsets bodyStart fields parts = [] →
        bodySizes fields parts = [] ∧ bodyWidth (slotsOf fields parts) = 0 := by
  -- Without any body offsets, every paired field must be stored inline.
  intro fields parts bodyStart named
  fun_induction bodyOffsets bodyStart fields parts <;> simp_all [bodySizes, slotsOf, bodyWidth]

/--
The spans between consecutive offsets are the widths of the bodies.

The last body is closed by the budget, which is where the whole encoding ends.
-/
theorem offsetSpans_bodyOffsets :
    ∀ (fields : List Desc) (parts : List Bytes) (bodyStart : Nat),
      offsetSpans (bodyOffsets bodyStart fields parts)
          (bodyStart + bodyWidth (slotsOf fields parts))
        = .ok (bodySizes fields parts) := by
  intro fields
  induction fields with
  | nil => intro parts _; simp [bodyOffsets, bodySizes, offsetSpans]
  | cons field fields ih =>
    intro parts bodyStart
    cases parts with
    | nil => simp [bodyOffsets, bodySizes, offsetSpans]
    | cons part parts =>
      rw [slotsOf_cons]
      by_cases fixed : field.isFixed
      · -- A field written in place opens no body, so nothing between offsets changes.
        simpa [bodyOffsets, bodySizes, fixed, bodyWidth] using ih parts bodyStart
      · -- This field opens a body, which ends where the next one begins.
        have onward := ih parts (bodyStart + part.size)
        cases later : bodyOffsets (bodyStart + part.size) fields parts with
        | nil =>
          -- Nothing follows, so the budget closes this body.
          obtain ⟨noSizes, noWidth⟩ := bodySizes_of_no_offsets fields parts _ later
          simp [bodyOffsets, bodySizes, fixed, bodyWidth, later, noSizes, noWidth, offsetSpans]
        | cons next others =>
          cases bodyOffsets_head fields parts _ next others later
          simp_all [bodyOffsets, bodySizes, bodyWidth, offsetSpans, Nat.add_assoc,
            Bind.bind, Except.bind, pure, Except.pure]

/--
The parts come back out of the bodies the layout put them in.

The front is the fixed part, so its width is where the first body begins.
-/
theorem takeSlots_expectedSlots :
    ∀ (fields : List Desc) (parts : List Bytes) (front : Bytes),
      fields.length = parts.length →
      takeSlots (front ++ bodiesOf (slotsOf fields parts))
          (expectedSlots front.size fields parts) (bodySizes fields parts)
        = .ok parts := by
  intro fields
  induction fields with
  | nil =>
    intro parts _ paired
    cases parts <;> simp_all [slotsOf, expectedSlots, takeSlots, bodySizes, bodiesOf]
  | cons field fields ih =>
    intro parts front paired
    cases parts with
    | nil => simp at paired
    | cons part parts =>
      -- This field's body is the run the offset opened, and the rest follow it.
      have onward := ih parts (front ++ part) (by simpa using paired)
      by_cases fixed : field.isFixed <;>
        simp_all [expectedSlots, bodySizes, bodiesOf, takeSlots, slotsOf_cons, Bind.bind,
          Except.bind, pure, Except.pure]

/-- The fixed part is as wide as the slots say it is. -/
theorem headOf_size : ∀ (slots : List (Bool × Bytes)) (start : Nat),
    (headOf start slots).size = headWidth slots := by
  -- Sum full payload widths for inline fields and four-byte widths for body references.
  intro slots start
  fun_induction headOf start slots <;> simp_all [headWidth, uintBytes_size]

/-- The bodies are as wide as the slots say they are. -/
theorem bodiesOf_size : ∀ (slots : List (Bool × Bytes)),
    (bodiesOf slots).size = bodyWidth slots := by
  -- Only variable-field payloads contribute bytes after the header.
  intro slots
  fun_induction bodiesOf slots <;> simp_all [bodyWidth]

/-- With no bodies, the slots hold every part in place. -/
theorem map_expectedSlots_of_no_offsets :
    ∀ (fields : List Desc) (parts : List Bytes) (bodyStart : Nat),
      fields.length = parts.length →
      bodyOffsets bodyStart fields parts = [] →
      (expectedSlots bodyStart fields parts).map Slot.held = parts := by
  -- Every surviving slot must hold its field bytes directly.
  intro fields parts bodyStart paired named
  fun_induction expectedSlots bodyStart fields parts <;> simp_all [bodyOffsets, Slot.held]
  exact List.eq_nil_of_length_eq_zero paired.symm

/-- A struct whose fields all have a width is that wide, and opens no body. -/
theorem fieldsFixedSize_headWidth :
    ∀ (fields : List Desc) (parts : List Bytes) (width : Nat),
      fields.length = parts.length →
      (∀ pair ∈ fields.zip parts, ∀ w, pair.1.fixedSize = some w → pair.2.size = w) →
      Desc.fieldsFixedSize fields = some width →
      headWidth (slotsOf fields parts) = width ∧ bodyWidth (slotsOf fields parts) = 0 := by
  intro fields
  induction fields with
  | nil =>
    intro parts width paired _ fixed
    cases parts <;> simp_all [slotsOf, headWidth, bodyWidth, Desc.fieldsFixedSize]
  | cons field fields ih =>
    intro parts width paired widths fixed
    cases parts with
    | nil => simp at paired
    | cons part parts =>
      -- A struct is fixed only when every field is, so this one is too.
      simp only [Desc.fieldsFixedSize] at fixed
      split at fixed <;> simp only [Option.some.injEq, reduceCtorEq] at fixed
      rename_i fieldWidth remaining fieldIs restIs
      have onward := ih parts remaining (by simpa using paired)
        (fun pair member => widths pair (List.mem_cons_of_mem _ member)) restIs
      simp_all [slotsOf_cons, headWidth, bodyWidth, Desc.isFixed,
        widths (field, part) (by simp) fieldWidth fieldIs]

/-- The fixed part the slots write is as wide as the declaration says it is. -/
theorem leadingWidth_headWidth :
    ∀ (fields : List Desc) (parts : List Bytes),
      fields.length = parts.length →
      (∀ pair ∈ fields.zip parts, ∀ w, pair.1.fixedSize = some w → pair.2.size = w) →
      headWidth (slotsOf fields parts) = Desc.leadingWidth fields := by
  intro fields
  induction fields with
  | nil => intro parts _ _; simp [slotsOf, headWidth, Desc.leadingWidth]
  | cons field fields ih =>
    intro parts paired widths
    cases parts with
    | nil => simp at paired
    | cons part parts =>
      -- A fixed field writes its own bytes, and a variable one writes a four-byte offset.
      have rest := ih parts (by simpa using paired)
        (fun pair member w fixed => widths pair (by simp [member]) w fixed)
      cases fixed : field.fixedSize <;>
        simp_all [slotsOf_cons, headWidth, Desc.isFixed, Desc.leadingWidth]

/-- The budget an encoder wrote is one the decoder settles before it reads a field. -/
theorem structBudget_of_written :
    ∀ (fields : List Desc) (parts : List Bytes),
      fields.length = parts.length →
      (∀ pair ∈ fields.zip parts, ∀ w, pair.1.fixedSize = some w → pair.2.size = w) →
      structBudget fields
        (headWidth (slotsOf fields parts) + bodyWidth (slotsOf fields parts)) = .ok () := by
  intro fields parts paired widths
  simp only [structBudget]
  cases fixed : Desc.fieldsFixedSize fields with
  -- A variable struct only needs the budget to cover the fixed part, which it does exactly.
  | none => simp [leadingWidth_headWidth fields parts paired widths]
  -- A fixed struct writes no bodies, so what was written is the declared width.
  | some width =>
    obtain ⟨front, empty⟩ := fieldsFixedSize_headWidth fields parts width paired widths fixed
    simp [front, empty]

/--
A struct's parts are cut back out of the encoding they were laid into.

This is the offset table read back: what the encoder wrote, the decoder finds.
-/
theorem structSlices_assemble :
    ∀ (fields : List Desc) (parts : List Bytes),
      fields.length = parts.length →
      (∀ pair ∈ fields.zip parts, ∀ width, pair.1.fixedSize = some width → pair.2.size = width) →
      headWidth (slotsOf fields parts) + bodyWidth (slotsOf fields parts)
        < 2 ^ (8 * bytesPerOffset) →
      assemble (fields.map Desc.isFixed) parts >>= structSlices fields = .ok parts := by
  intro fields parts paired widths nameable
  have shape : (fields.map Desc.isFixed).zip parts = slotsOf fields parts := rfl
  -- The encoder writes the fixed part and then the bodies, and refuses neither.
  simp only [assemble, shape]
  rw [ite_eq_right (by omega)]
  show structSlices fields (headOf (headWidth (slotsOf fields parts)) (slotsOf fields parts)
    ++ bodiesOf (slotsOf fields parts)) = .ok parts
  -- The fixed part reads back the slots that wrote it.
  have read := readSlots_headOf fields parts #[] (bodiesOf (slotsOf fields parts))
    (headWidth (slotsOf fields parts)) paired widths (by omega)
  simp only [Array.size_empty, Array.empty_append, Nat.zero_add] at read
  have widthIs : (headOf (headWidth (slotsOf fields parts)) (slotsOf fields parts)
      ++ bodiesOf (slotsOf fields parts)).size
      = headWidth (slotsOf fields parts) + bodyWidth (slotsOf fields parts) := by
    simp [headOf_size, bodiesOf_size]
  have settled := structBudget_of_written fields parts paired widths
  simp only [structSlices, structSlots, structBodies, read, bodyStarts_expectedSlots, widthIs,
    settled, ite_eq_right (Nat.not_le.mpr nameable), Bind.bind, Except.bind]
  -- Either the layout opened no body at all, or the first one starts where the slots end.
  cases named : bodyOffsets (headWidth (slotsOf fields parts)) fields parts with
  | nil =>
    obtain ⟨_, noWidth⟩ := bodySizes_of_no_offsets fields parts _ named
    simp [noWidth, map_expectedSlots_of_no_offsets fields parts _ paired named, pure, Except.pure]
  | cons next others =>
    -- The first body begins exactly where the fixed part ends.
    cases bodyOffsets_head fields parts _ next others named
    have spans := offsetSpans_bodyOffsets fields parts (headWidth (slotsOf fields parts))
    rw [named] at spans
    have taken := takeSlots_expectedSlots fields parts
      (headOf (headWidth (slotsOf fields parts)) (slotsOf fields parts)) paired
    rw [headOf_size] at taken
    simp [spans, taken]

/-- An encoding that was written is one whose offsets four bytes can name. -/
theorem assemble_nameable (inline : List Bool) (parts : List Bytes) (bytes : Bytes)
    (wrote : assemble inline parts = .ok bytes) :
    headWidth (inline.zip parts) + bodyWidth (inline.zip parts)
      < 2 ^ (8 * bytesPerOffset) := by
  -- The encoder refuses anything wider, so what it wrote is inside the bound.
  simp only [assemble] at wrote
  split at wrote
  · simp [Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw] at wrote
  · omega

/-- What was written is as wide as the fixed part and the bodies together. -/
theorem assemble_size (inline : List Bool) (parts : List Bytes) (bytes : Bytes)
    (wrote : assemble inline parts = .ok bytes) :
    bytes.size = headWidth (inline.zip parts) + bodyWidth (inline.zip parts) := by
  -- Successful assembly has already established that its total width is representable.
  have nameable := assemble_nameable inline parts bytes wrote
  simp only [assemble, ite_eq_right (show ¬ headWidth (inline.zip parts)
    + bodyWidth (inline.zip parts) ≥ 2 ^ (8 * bytesPerOffset) by omega),
    Pure.pure, Except.pure] at wrote
  -- Identify the returned bytes as the header followed by the bodies, then add their widths.
  rw [← Except.ok.inj wrote]
  simp [headOf_size, bodiesOf_size]

/-- Parts laid end to end, which is what a sequence of fixed elements encodes to. -/
def concatParts : List Bytes → Bytes
  | [] => #[]
  | part :: rest => part ++ concatParts rest

/-- Extracting past a run on the front is extracting from what follows it. -/
theorem extract_append_shift (front back : Bytes) (start stop : Nat) :
    (front ++ back).extract (front.size + start) (front.size + stop)
      = back.extract start stop := by
  -- Subtracting the common prefix translates both extraction boundaries into the suffix.
  simp

/-- Every element of a sequence of fixed elements sits in its own window. -/
theorem extract_concatParts (width : Nat) :
    ∀ (parts : List Bytes), (∀ part ∈ parts, part.size = width) →
      ∀ index, index < parts.length →
        (concatParts parts).extract (index * width) ((index + 1) * width) = parts[index]! := by
  intro parts
  induction parts with
  | nil => intro _ _ inside; simp at inside
  | cons part rest ih =>
    intro widths index inside
    obtain rfl : part.size = width := widths part (by simp)
    match index with
    -- The first element begins where the whole run does.
    | 0 => simp [concatParts]
    | index + 1 =>
      -- Every later one lies past the first, at the same offset one element in.
      have onward := ih (fun p member => widths p (List.mem_cons_of_mem _ member)) index
        (by simpa using inside)
      rw [concatParts, Nat.succ_mul, Nat.succ_mul, Nat.add_comm _ part.size,
        Nat.add_comm _ part.size, extract_append_shift]
      simpa using onward

/-- Slots for a sequence of fixed elements, which are all written in place. -/
abbrev inlineSlots (parts : List Bytes) : List (Bool × Bytes) :=
  (parts.map fun _ => true).zip parts

/-- Every such element sits in the fixed part, one after another. -/
theorem headOf_inline : ∀ (parts : List Bytes) (start : Nat),
    headOf start (inlineSlots parts) = concatParts parts := by
  -- Every payload is included in the header in its original order.
  intro parts
  induction parts <;> simp_all [inlineSlots, headOf, concatParts]

/-- The bodies of such a sequence are empty. -/
theorem bodiesOf_inline : ∀ (parts : List Bytes), bodiesOf (inlineSlots parts) = #[] := by
  -- Skipping every inline payload leaves an empty body byte string.
  intro parts
  induction parts <;> simp_all [inlineSlots, bodiesOf]

/-- A sequence of fixed elements encodes to its elements laid end to end. -/
theorem assemble_inline (parts : List Bytes) (bytes : Bytes)
    (wrote : assemble (parts.map fun _ => true) parts = .ok bytes) :
    bytes = concatParts parts := by
  -- Successful assembly passes the composite size bound even when no offsets are stored.
  have nameable := assemble_nameable (parts.map fun _ => true) parts bytes wrote
  simp only [assemble, ite_eq_right (show ¬ headWidth ((parts.map fun _ => true).zip parts)
    + bodyWidth ((parts.map fun _ => true).zip parts) ≥ 2 ^ (8 * bytesPerOffset) by omega),
    Pure.pure, Except.pure] at wrote
  rw [← Except.ok.inj wrote]
  show headOf _ (inlineSlots parts) ++ bodiesOf (inlineSlots parts) = _
  -- The header is the concatenated payload and the separate body is empty.
  rw [headOf_inline, bodiesOf_inline]
  simp

/-- A run of equal-width elements is as wide as their count says. -/
theorem concatParts_size (width : Nat) : ∀ (parts : List Bytes),
    (∀ part ∈ parts, part.size = width) →
      (concatParts parts).size = parts.length * width := by
  -- Each appended element adds exactly one common element width.
  intro parts widths
  induction parts <;> simp_all [concatParts, Nat.succ_mul]
  omega

/-- Cutting a run of equal-width elements into windows gives the elements back. -/
theorem map_extract_concatParts (width : Nat) (parts : List Bytes)
    (widths : ∀ part ∈ parts, part.size = width) :
    (List.range parts.length).map
        (fun index => (concatParts parts).extract (index * width) ((index + 1) * width))
      = parts := by
  -- Recover one interval per element and compare each recovered interval with its original payload.
  apply List.ext_getElem
  · simp
  · intro index inRange inParts
    simp only [List.getElem_map, List.getElem_range]
    rw [extract_concatParts width parts widths index inParts]
    simp [getElem!_pos, inParts]

/-- Slots for a sequence of variable elements, each reached through an offset. -/
abbrev offsetSlots (parts : List Bytes) : List (Bool × Bytes) :=
  (parts.map fun _ => false).zip parts

/-- One element puts one offset slot on the front of both. -/
theorem offsetSlots_cons (part : Bytes) (rest : List Bytes) :
    offsetSlots (part :: rest) = (false, part) :: offsetSlots rest := rfl

/-- Where each body of such a sequence begins. -/
def runningOffsets (start : Nat) : List Bytes → List Nat
  | [] => []
  -- A body starts at the current cursor, and its byte length determines the next cursor.
  | part :: rest => start :: runningOffsets (start + part.size) rest

/-- The table is four bytes per element, and nothing else. -/
theorem headWidth_offset : ∀ (parts : List Bytes),
    headWidth (offsetSlots parts) = parts.length * bytesPerOffset := by
  -- Each variable-size element contributes exactly four header bytes, independently of payload length.
  intro parts
  induction parts <;> simp_all [offsetSlots_cons, headWidth, Nat.succ_mul]
  omega

/-- The bodies of such a sequence are its elements laid end to end. -/
theorem bodiesOf_offset : ∀ (parts : List Bytes),
    bodiesOf (offsetSlots parts) = concatParts parts := by
  -- Every variable-size payload belongs to the body region in element order.
  intro parts
  induction parts <;> simp_all [offsetSlots_cons, bodiesOf, concatParts]

/-- Each offset in the table names where its own body begins. -/
theorem readUint_headOf_offset : ∀ (parts : List Bytes) (start : Nat) (front bodies : Bytes)
    (index : Nat),
    index < parts.length →
    start + bodyWidth (offsetSlots parts) < 2 ^ (8 * bytesPerOffset) →
    readUint (front ++ (headOf start (offsetSlots parts) ++ bodies))
        (front.size + index * bytesPerOffset) bytesPerOffset
      = (runningOffsets start parts)[index]! := by
  intro parts
  induction parts with
  | nil => intro _ _ _ index inside _; simp at inside
  | cons part rest ih =>
    intro start front bodies index inside nameable
    simp only [offsetSlots_cons, headOf, bodyWidth] at nameable ⊢
    match index with
    | 0 =>
      -- The first offset sits at the front of the table.
      simpa [runningOffsets, Array.append_assoc] using
        readUint_offset front _ (show start < _ by omega)
    | index + 1 =>
      -- Every later one lies four bytes further along, which is the next element's.
      have onward := ih (start + part.size) (front ++ uintBytes bytesPerOffset start) bodies
        index (by simpa using inside) (by omega)
      simp only [Array.size_append, Array.append_assoc, uintBytes_size] at onward
      simpa [runningOffsets, Array.append_assoc, Nat.succ_mul, Nat.add_assoc, Nat.add_comm]
        using onward

/-- One offset per element. -/
theorem runningOffsets_length : ∀ (parts : List Bytes) (start : Nat),
    (runningOffsets start parts).length = parts.length := by
  -- Advancing the byte cursor does not change the one-offset-per-element correspondence.
  intro parts start
  fun_induction runningOffsets start parts <;> simp_all

/-- The table reads back the offsets the layout named. -/
theorem readOffsets_headOf (parts : List Bytes) (start : Nat) (bodies : Bytes)
    (nameable : start + bodyWidth (offsetSlots parts) < 2 ^ (8 * bytesPerOffset)) :
    readOffsets (headOf start (offsetSlots parts) ++ bodies) parts.length
      = runningOffsets start parts := by
  -- Both tables have one entry per body, so compare their offsets position by position.
  apply List.ext_getElem
  · simp [readOffsets, runningOffsets_length]
  · intro index inRead _
    simp only [readOffsets, List.getElem_map, List.getElem_range]
    have inParts : index < parts.length := by simpa [readOffsets] using inRead
    -- Read the selected four-byte header entry using the bounded integer round-trip theorem.
    have read := readUint_headOf_offset parts start #[] bodies index inParts nameable
    simp only [Array.size_empty, Array.empty_append, Nat.zero_add] at read
    rw [read]
    simp [getElem!_pos, runningOffsets_length, inParts]

/-- The spans between those offsets are the widths of the elements. -/
theorem offsetSpans_runningOffsets : ∀ (parts : List Bytes) (start : Nat),
    offsetSpans (runningOffsets start parts) (start + bodyWidth (offsetSlots parts))
      = .ok (parts.map Array.size) := by
  intro parts
  induction parts with
  | nil => intro _; simp [runningOffsets, offsetSpans]
  | cons part rest ih =>
    intro start
    -- Either this is the last element, closed by the budget, or the next one closes it.
    have onward := ih (start + part.size)
    cases rest <;> simp_all [runningOffsets, offsetSpans, offsetSlots_cons, bodyWidth,
      Nat.add_assoc, Bind.bind, Except.bind, pure, Except.pure]

/-- Each body is cut back out of where its offset put it. -/
theorem map_extract_offsets : ∀ (parts : List Bytes) (front : Bytes),
    ((runningOffsets front.size parts).zip (parts.map Array.size)).map
        (fun pair => (front ++ concatParts parts).extract pair.1 (pair.1 + pair.2))
      = parts := by
  intro parts
  -- Remove the first recovered body, then treat its bytes as part of the prefix for the suffix.
  induction parts with
  | nil => intro _; simp [runningOffsets]
  | cons part rest ih =>
    intro front
    have onward := ih (front ++ part)
    simp_all [runningOffsets, concatParts, Array.append_assoc]

/-- A sequence of variable elements encodes to its table and then its bodies. -/
theorem assemble_offset (parts : List Bytes) (bytes : Bytes)
    (wrote : assemble (parts.map fun _ => false) parts = .ok bytes) :
    bytes = headOf (parts.length * bytesPerOffset) (offsetSlots parts) ++ concatParts parts := by
  -- Successful assembly guarantees that the entire table and payload fit the offset range.
  have nameable := assemble_nameable (parts.map fun _ => false) parts bytes wrote
  simp only [assemble, ite_eq_right (show ¬ headWidth ((parts.map fun _ => false).zip parts)
    + bodyWidth ((parts.map fun _ => false).zip parts) ≥ 2 ^ (8 * bytesPerOffset) by omega),
    Pure.pure, Except.pure] at wrote
  rw [← Except.ok.inj wrote]
  show headOf (headWidth (offsetSlots parts)) (offsetSlots parts)
    ++ bodiesOf (offsetSlots parts) = _
  -- Replace the measured header by four bytes per element and the bodies by their concatenation.
  rw [headWidth_offset, bodiesOf_offset]

/-- The whole encoding is the table and the bodies together. -/
theorem offset_encoding_size (parts : List Bytes) :
    (headOf (parts.length * bytesPerOffset) (offsetSlots parts) ++ concatParts parts).size
      = parts.length * bytesPerOffset + bodyWidth (offsetSlots parts) := by
  -- Count the four-byte entries separately from the total payload bytes.
  rw [Array.size_append, headOf_size, headWidth_offset, ← bodiesOf_size, bodiesOf_offset]

/-- The first offset names where the bodies begin. -/
theorem runningOffsets_head (start : Nat) (part : Bytes) (rest : List Bytes) :
    (runningOffsets start (part :: rest))[0]! = start := by
  -- The first body begins at the initial cursor before any payload length is added.
  simp [runningOffsets, getElem!_pos]

/-- A struct of fields that each take a byte takes one itself. -/
theorem fieldsFixedSize_pos : ∀ (fields : List Desc) (width : Nat),
    ¬ fields.isEmpty = true →
    (∀ field ∈ fields, ∀ w, field.fixedSize = some w → 0 < w) →
    Desc.fieldsFixedSize fields = some width → 0 < width := by
  intro fields width notEmpty widths fixed
  cases fields with
  | nil => simp at notEmpty
  | cons field rest =>
    -- The first field alone already takes a byte, whatever the rest take.
    simp only [Desc.fieldsFixedSize] at fixed
    split at fixed <;> simp_all
    omega

end EthLib.Serialization.Ssz
