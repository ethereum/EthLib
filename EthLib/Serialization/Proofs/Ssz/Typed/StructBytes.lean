module

public import EthLib.Serialization.Ssz.Typed.Container
public import EthLib.Serialization.Proofs.Ssz.Codec.DecodeFits
public import EthLib.Serialization.Proofs.Ssz.Typed.Class

/-!
# Proofs: a struct cut and joined as byte arrays

A typed container cuts its bytes and joins its fields' bytes as byte arrays.

Each step agrees with the step of the untyped codec, refusals included.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/--
The bytes of each field of a struct, in order.

A slot written in place gives its own bytes, and a slot behind an offset takes the next body.
-/
def fillSlots : List ByteSlot → List ByteArray → List Bytes
  | [], _ => []
  | .inline bytes :: slots, bodies => bytes.data :: fillSlots slots bodies
  | .body _ :: slots, body :: bodies => body.data :: fillSlots slots bodies
  | .body _ :: slots, [] => fillSlots slots []

/-- The slots read from a byte array are the slots read from its bytes. -/
theorem readByteSlots_eq (fields : List Desc) (data : ByteArray) (position : Nat) :
    (fun read => (read.1.map ByteSlot.toSlot, read.2)) <$> readByteSlots fields data position =
      readSlots fields data.data position := by
  induction fields generalizing position with
  | nil => rfl
  | cons field fields ih =>
    rw [readByteSlots, readSlots]
    rcases hf : field.fixedSize with _ | width
    · by_cases h : position + bytesPerOffset > data.size
      · have h2 : position + bytesPerOffset > data.data.size := h
        simp only [h, h2, ite_true]
        rfl
      · have h2 : ¬ position + bytesPerOffset > data.data.size := h
        simp only [h, h2, ite_false]
        have := ih (position + bytesPerOffset)
        cases hr : readByteSlots fields data (position + bytesPerOffset) <;>
          rw [hr] at this <;> simp [← this, ByteSlot.toSlot, readUintBytes_eq]
    · by_cases h : position + width > data.size
      · have h2 : position + width > data.data.size := h
        simp only [h, h2, ite_true]
        rfl
      · have h2 : ¬ position + width > data.data.size := h
        simp only [h, h2, ite_false]
        have := ih (position + width)
        cases hr : readByteSlots fields data (position + width) <;>
          rw [hr] at this <;> simp [← this, ByteSlot.toSlot]

/-- A struct's slots, read from a byte array, are those read from its bytes. -/
theorem byteStructSlots_eq (fields : List Desc) (data : ByteArray) :
    (fun read => (read.1.map ByteSlot.toSlot, read.2)) <$> byteStructSlots fields data =
      structSlots fields data.data := by
  unfold byteStructSlots structSlots
  have hs : data.size = data.data.size := rfl
  rw [hs]
  by_cases h : data.data.size ≥ 2 ^ (8 * bytesPerOffset)
  · simp only [h, ite_true]
    rfl
  · simp only [h, ite_false]
    cases structBudget fields data.data.size with
    | error e => rfl
    | ok u => exact readByteSlots_eq fields data 0

private theorem readByteSlots_length {fields : List Desc} {data : ByteArray} {position : Nat}
    {slots : List ByteSlot} {leading : Nat}
    (read : readByteSlots fields data position = .ok (slots, leading)) :
    slots.length = fields.length := by
  induction fields generalizing position slots leading with
  | nil =>
    rw [readByteSlots] at read
    cases read
    rfl
  | cons field fields ih =>
    rw [readByteSlots] at read
    rcases hf : field.fixedSize with _ | width
    · rw [hf] at read
      by_cases h : position + bytesPerOffset > data.size
      · simp only [h, ite_true] at read
        cases read
      · simp only [h, ite_false] at read
        cases hr : readByteSlots fields data (position + bytesPerOffset) with
        | error e => simp [hr, Functor.map, Except.map] at read
        | ok r =>
          simp [hr] at read
          obtain ⟨rfl, -⟩ := read
          simp [ih hr]
    · rw [hf] at read
      by_cases h : position + width > data.size
      · simp only [h, ite_true] at read
        cases read
      · simp only [h, ite_false] at read
        cases hr : readByteSlots fields data (position + width) with
        | error e => simp [hr, Functor.map, Except.map] at read
        | ok r =>
          simp [hr] at read
          obtain ⟨rfl, -⟩ := read
          simp [ih hr]

/-- A struct has one slot for each field. -/
theorem byteStructSlots_length {fields : List Desc} {data : ByteArray} {slots : List ByteSlot}
    {leading : Nat} (read : byteStructSlots fields data = .ok (slots, leading)) :
    slots.length = fields.length := by
  unfold byteStructSlots at read
  by_cases h : data.size ≥ 2 ^ (8 * bytesPerOffset)
  · simp only [h, ite_true] at read
    cases read
  · simp only [h, ite_false] at read
    cases hb : structBudget fields data.size with
    | error e => simp [hb, Bind.bind, Except.bind] at read
    | ok u => simp [hb] at read; exact readByteSlots_length read

/-- The bodies begin where the untyped slots say they begin. -/
theorem byteBodyStarts_eq (slots : List ByteSlot) :
    byteBodyStarts slots = bodyStarts (slots.map ByteSlot.toSlot) := by
  induction slots with
  | nil => rfl
  | cons slot slots ih => cases slot <;> simp [byteBodyStarts, bodyStarts, ByteSlot.toSlot, ih]

/-- A struct has one body for each slot behind an offset. -/
theorem byteBodies_length {data : ByteArray} {slots : List ByteSlot} {leading : Nat}
    {bodies : List ByteArray} (cut : byteBodies data slots leading = .ok bodies) :
    bodies.length = (byteBodyStarts slots).length := by
  unfold byteBodies at cut
  by_cases hn : (byteBodyStarts slots).isEmpty = true
  · simp only [hn, ite_true] at cut
    by_cases hd : (data.size != leading) = true
    · simp only [hd, ite_true] at cut
      cases cut
    · simp only [hd] at cut
      cases cut
      simp at hn
      simp [hn]
  · simp only [hn] at cut
    by_cases hf : ((byteBodyStarts slots).headD 0 != leading) = true
    · simp only [hf, ite_true] at cut
      cases cut
    · simp only [hf] at cut
      cases hs : offsetSpans (byteBodyStarts slots) data.size with
      | error e =>
        rw [hs] at cut
        cases cut
      | ok spans =>
        rw [hs] at cut
        cases cut
        simp [offsetSpans_length hs]

/-- Taking each slot's body from its span is filling the slots with the sliced bodies. -/
private theorem takeSlots_eq (data : ByteArray) (slots : List ByteSlot) (spans : List Nat)
    (h : spans.length = (byteBodyStarts slots).length) :
    takeSlots data.data (slots.map ByteSlot.toSlot) spans =
      .ok (fillSlots slots (List.zipWith (fun start span => data.extract start (start + span))
        (byteBodyStarts slots) spans)) := by
  induction slots generalizing spans with
  | nil => rfl
  | cons slot slots ih =>
    cases slot with
    | inline bytes =>
      simp only [byteBodyStarts] at h ⊢
      simp [takeSlots, ByteSlot.toSlot, fillSlots, ih spans h, Functor.map, Except.map]
    | body start =>
      cases spans with
      | nil => simp [byteBodyStarts] at h
      | cons span spans =>
        simp only [byteBodyStarts, List.length_cons, Nat.add_right_cancel_iff] at h
        simp [takeSlots, ByteSlot.toSlot, byteBodyStarts, List.zipWith_cons_cons, ih spans h,
          Functor.map, Except.map, fillSlots]

private theorem fillSlots_nil (slots : List ByteSlot) (h : byteBodyStarts slots = []) :
    fillSlots slots [] = (slots.map ByteSlot.toSlot).map Slot.held := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
    cases slot with
    | inline bytes => simp_all [byteBodyStarts, fillSlots, ByteSlot.toSlot, Slot.held]
    | body start => simp [byteBodyStarts] at h

/-- The bytes of the fields, cut from a byte array, are those cut by the untyped codec. -/
theorem structBodies_eq (data : ByteArray) (slots : List ByteSlot) (leading : Nat) :
    structBodies data.data (slots.map ByteSlot.toSlot) leading =
      fillSlots slots <$> byteBodies data slots leading := by
  unfold structBodies byteBodies
  rw [← byteBodyStarts_eq]
  by_cases hn : (byteBodyStarts slots).isEmpty = true
  · simp only [hn, ite_true]
    by_cases hd : (data.size != leading) = true
    · have hd2 : (data.data.size != leading) = true := hd
      simp only [hd, hd2, ite_true]
      rfl
    · have hd2 : ¬ (data.data.size != leading) = true := hd
      simp only [hd, hd2, Bool.false_eq_true, ite_false]
      rw [← fillSlots_nil slots (by simpa using hn)]
      rfl
  · simp only [hn]
    by_cases hf : ((byteBodyStarts slots).headD 0 != leading) = true
    · simp only [hf, ite_true]
      rfl
    · simp only [hf]
      have hr : offsetSpans (byteBodyStarts slots) data.data.size =
          offsetSpans (byteBodyStarts slots) data.size := rfl
      rw [hr]
      cases hs : offsetSpans (byteBodyStarts slots) data.size with
      | error e => rfl
      | ok spans =>
        simp only [bind, Except.bind, Functor.map, Except.map]
        exact takeSlots_eq data slots spans (by rw [offsetSpans_length hs])

private abbrev mapParts (slots : List (Bool × Bytes)) : List (Bool × ByteArray) :=
  slots.map fun slot => (slot.1, ByteArray.mk slot.2)

private theorem zipWith_map (inline : List Bool) (parts : List Bytes) :
    List.zipWith Prod.mk inline (parts.map ByteArray.mk) =
      mapParts (List.zipWith Prod.mk inline parts) := by
  induction inline generalizing parts with
  | nil => rfl
  | cons b inline ih =>
    cases parts with
    | nil => rfl
    | cons part parts => simp [mapParts, List.zipWith] at ih ⊢; exact ih parts

private theorem headWidthFrom_map (slots : List (Bool × Bytes)) (width : Nat) :
    byteHeadWidthFrom (mapParts slots) width = headWidthFrom slots width := by
  induction slots generalizing width with
  | nil => rfl
  | cons slot slots ih => simp [mapParts, byteHeadWidthFrom, headWidthFrom] at ih ⊢; exact ih _

private theorem bodyWidthFrom_map (slots : List (Bool × Bytes)) (width : Nat) :
    byteBodyWidthFrom (mapParts slots) width = bodyWidthFrom slots width := by
  induction slots generalizing width with
  | nil => rfl
  | cons slot slots ih =>
    obtain ⟨b, part⟩ := slot
    cases b <;> simp [mapParts, byteBodyWidthFrom, bodyWidthFrom] at ih ⊢ <;> exact ih _

private theorem mk_append (a b : Bytes) :
    (ByteArray.mk a ++ ByteArray.mk b) = ByteArray.mk (a ++ b) :=
  ByteArray.ext (by simp)

private theorem size_mk (a : Bytes) : (ByteArray.mk a).size = a.size := rfl

private theorem byteHeadOfFrom_map (start : Nat) (slots : List (Bool × Bytes)) (out : Bytes) :
    byteHeadOfFrom start (mapParts slots) ⟨out⟩ = ⟨headOfFrom start slots out⟩ := by
  induction slots generalizing start out with
  | nil => rfl
  | cons slot slots ih =>
    obtain ⟨b, part⟩ := slot
    cases b <;> simp [mapParts, byteHeadOfFrom, headOfFrom, mk_append, size_mk] at ih ⊢ <;>
      exact ih _ _

private theorem byteBodiesOfFrom_map (slots : List (Bool × Bytes)) (out : Bytes) :
    byteBodiesOfFrom (mapParts slots) ⟨out⟩ = ⟨bodiesOfFrom slots out⟩ := by
  induction slots generalizing out with
  | nil => rfl
  | cons slot slots ih =>
    obtain ⟨b, part⟩ := slot
    cases b <;> simp [mapParts, byteBodiesOfFrom, bodiesOfFrom, mk_append] at ih ⊢ <;> exact ih _

/-- Parts joined as byte arrays are the parts joined by the untyped codec. -/
theorem assembleBytes_eq (inline : List Bool) (parts : List Bytes) :
    assembleBytes inline (parts.map ByteArray.mk) = ByteArray.mk <$> assemble inline parts := by
  unfold assembleBytes assemble
  simp only [zipWith_map, headWidthFrom_map, bodyWidthFrom_map, headWidth, bodyWidth]
  by_cases h : headWidthFrom (List.zipWith Prod.mk inline parts) 0 +
      bodyWidthFrom (List.zipWith Prod.mk inline parts) 0 ≥ 2 ^ (8 * bytesPerOffset)
  · simp only [h, ite_true]
    rfl
  · simp only [h, ite_false]
    have e : ByteArray.emptyWithCapacity
        (headWidthFrom (List.zipWith Prod.mk inline parts) 0 +
          bodyWidthFrom (List.zipWith Prod.mk inline parts) 0) = ⟨#[]⟩ := rfl
    rw [e, byteHeadOfFrom_map, byteBodiesOfFrom_map, bodiesOfFrom_eq (out := _)]
    rfl

end EthLib.Serialization.Ssz
