module

public import EthLib.Serialization.Ssz.Codec.Deserialize
public import EthLib.Serialization.Proofs.Ssz.Codec.Admits

/-!
# Proofs: the fields of a struct, cut from its bytes

A struct has one slot per field and one body per offset.

Its fields' bytes can also be cut slot by slot, each body taken from its span.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/--
The parts of a struct in field order, each body taken from the span its offset opened.

It cuts the same bytes as the fields filled from the bodies, and some proofs read a struct this way.
-/
def takeSlots (data : Bytes) : List Slot → List Nat → Except Err (List Bytes)
  | [], _ => .ok []
  -- An inline field consumes no body span because its payload is already present.
  | .inline bytes :: rest, spans => do return bytes :: (← takeSlots data rest spans)
  -- A variable field consumes exactly one validated span and extracts those payload bytes.
  | .body start :: rest, span :: spans => do
      return data.extract start (start + span) :: (← takeSlots data rest spans)
  -- A body with no span left means a table shorter than the fields that read it.
  | .body _ :: _, [] => .error .badDeclaration

/-- A successful offset table gives one span per body. -/
theorem offsetSpans_length {offsets spans : List Nat} {scope : Nat}
    (read : offsetSpans offsets scope = .ok spans) : spans.length = offsets.length := by
  -- Each accepted start offset contributes one span, including a zero-length span.
  induction offsets generalizing spans with
  | nil => rw [offsetSpans_nil] at read; cases read; rfl
  | cons start rest ih =>
    cases rest with
    | nil =>
      rw [offsetSpans_single] at read
      split at read <;> cases read
      rfl
    | cons next rest =>
      rw [offsetSpans_cons_cons] at read
      split at read
      · cases read
      · -- A rejected suffix cannot occur inside a successfully decoded table.
        obtain ⟨more, tail, ⟨⟩⟩ := checksPassed read
        -- Prepending the current span increases both counts by one.
        simp [ih tail]

private theorem readSlots_length {fields : List Desc} {data : Bytes} {position : Nat}
    {slots : List Slot} {leading : Nat}
    (read : readSlots fields data position = .ok (slots, leading)) :
    slots.length = fields.length := by
  induction fields generalizing position slots leading with
  | nil =>
    rw [readSlots] at read
    cases read
    rfl
  | cons field fields ih =>
    rw [readSlots] at read
    rcases hf : field.fixedSize with _ | width
    · rw [hf] at read
      by_cases h : position + bytesPerOffset > data.size
      · simp only [h, ite_true] at read
        cases read
      · simp only [h, ite_false] at read
        cases hr : readSlots fields data (position + bytesPerOffset) with
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
        cases hr : readSlots fields data (position + width) with
        | error e => simp [hr, Functor.map, Except.map] at read
        | ok r =>
          simp [hr] at read
          obtain ⟨rfl, -⟩ := read
          simp [ih hr]

/-- A struct has one slot for each field. -/
theorem structSlots_length {fields : List Desc} {data : Bytes} {slots : List Slot}
    {leading : Nat} (read : structSlots fields data = .ok (slots, leading)) :
    slots.length = fields.length := by
  unfold structSlots at read
  by_cases h : data.size ≥ 2 ^ (8 * bytesPerOffset)
  · simp only [h, ite_true] at read
    cases read
  · simp only [h, ite_false] at read
    cases hb : structBudget fields data.size with
    | error e => simp [hb, Bind.bind, Except.bind] at read
    | ok u => simp [hb] at read; exact readSlots_length read

/-- A struct has one body for each slot behind an offset. -/
theorem offsetBodies_length {data : Bytes} {slots : List Slot} {leading : Nat}
    {bodies : List Bytes} (cut : offsetBodies data slots leading = .ok bodies) :
    bodies.length = (bodyStarts slots).length := by
  unfold offsetBodies at cut
  by_cases hn : (bodyStarts slots).isEmpty = true
  · simp only [hn, ite_true] at cut
    by_cases hd : (data.size != leading) = true
    · simp only [hd, ite_true] at cut
      cases cut
    · simp only [hd] at cut
      cases cut
      simp at hn
      simp [hn]
  · simp only [hn] at cut
    by_cases hf : ((bodyStarts slots).headD 0 != leading) = true
    · simp only [hf, ite_true] at cut
      cases cut
    · simp only [hf] at cut
      cases hs : offsetSpans (bodyStarts slots) data.size with
      | error e =>
        rw [hs] at cut
        cases cut
      | ok spans =>
        rw [hs] at cut
        cases cut
        simp [offsetSpans_length hs]

/-- Taking each slot's body from its span is filling the slots with the sliced bodies. -/
private theorem takeSlots_eq (data : Bytes) (slots : List Slot) (spans : List Nat)
    (h : spans.length = (bodyStarts slots).length) :
    takeSlots data slots spans =
      .ok (fillSlots slots (List.zipWith (fun start span => data.extract start (start + span))
        (bodyStarts slots) spans)) := by
  induction slots generalizing spans with
  | nil => rfl
  | cons slot slots ih =>
    cases slot with
    | inline bytes =>
      simp only [bodyStarts] at h ⊢
      simp [takeSlots, fillSlots, ih spans h, Functor.map, Except.map]
    | body start =>
      cases spans with
      | nil => simp [bodyStarts] at h
      | cons span spans =>
        simp only [bodyStarts, List.length_cons, Nat.add_right_cancel_iff] at h
        simp [takeSlots, bodyStarts, List.zipWith_cons_cons, ih spans h,
          Functor.map, Except.map, fillSlots]

private theorem fillSlots_nil (slots : List Slot) (h : bodyStarts slots = []) :
    fillSlots slots [] = slots.map Slot.held := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
    cases slot with
    | inline bytes => simp_all [bodyStarts, fillSlots, Slot.held]
    | body start => simp [bodyStarts] at h

/-- The bytes of the fields are the fields cut slot by slot, once the offsets are checked. -/
theorem structBodies_eq_takeSlots (data : Bytes) (slots : List Slot) (leading : Nat) :
    structBodies data slots leading = (do
      let offsets := bodyStarts slots
      if offsets.isEmpty then
        if data.size != leading then throw (.scope leading data.size)
        return slots.map Slot.held
      if offsets.headD 0 != leading then throw (.firstOffset leading (offsets.headD 0))
      let spans ← offsetSpans offsets data.size
      takeSlots data slots spans) := by
  rw [structBodies]
  symm
  unfold offsetBodies
  by_cases hn : (bodyStarts slots).isEmpty = true
  · simp only [hn, ite_true]
    by_cases hd : (data.size != leading) = true
    · simp only [hd, ite_true]
      rfl
    · simp only [hd, Bool.false_eq_true, ite_false]
      rw [← fillSlots_nil slots (by simpa using hn)]
      rfl
  · simp only [hn]
    by_cases hf : ((bodyStarts slots).headD 0 != leading) = true
    · simp only [hf, ite_true]
      rfl
    · simp only [hf]
      cases hs : offsetSpans (bodyStarts slots) data.size with
      | error e => rfl
      | ok spans =>
        simp only [bind, Except.bind, Functor.map, Except.map]
        exact takeSlots_eq data slots spans (by rw [offsetSpans_length hs])


end EthLib.Serialization.Ssz
