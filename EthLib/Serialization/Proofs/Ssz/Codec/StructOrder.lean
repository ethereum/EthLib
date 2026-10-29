import EthLib.Serialization.Ssz.Codec.Deserialize
import EthLib.Serialization.Proofs.Ssz.Codec.Admits

/-! Reading a struct's fixed part first changes which refusal is met, never what is accepted. -/

namespace EthLib.Serialization.Ssz

/-- Every field written in place decodes when every field decodes from the slice it was cut to. -/
private theorem checkInline_of_takeSlots (data : Bytes) :
    ∀ (fields : List Desc) (slots : List Slot) (spans : List Nat) (slices : List Bytes)
      (values : List Value),
      takeSlots data slots spans = .ok slices →
      deserializeFields fields slices = .ok values →
      checkInline fields slots = .ok () := by
  intro fields
  -- Walk the fields, the slots, and the slices they were cut to in step.
  induction fields with
  | nil => intro slots _ _ _ _ _; rw [checkInline]
  | cons field fields ih =>
    intro slots spans slices values taken decoded
    cases slots with
    | nil => rw [checkInline]
    | cons slot slots =>
      cases slot with
      -- An inline slot is cut to its own bytes, which the field decoded already.
      | inline bytes =>
        rw [takeSlots] at taken
        obtain ⟨rest, tail, ⟨⟩⟩ := checksPassed taken
        rw [deserializeFields] at decoded
        obtain ⟨value, head, decoded⟩ := checksPassed decoded
        obtain ⟨others, decoded, -⟩ := checksPassed decoded
        rw [checkInline, head]
        exact ih slots spans rest others tail decoded
      -- A body slot is skipped, and the field it holds is left to the later fields.
      | body start =>
        cases spans with
        | nil => simp [takeSlots] at taken
        | cons span spans =>
          rw [takeSlots] at taken
          obtain ⟨rest, tail, ⟨⟩⟩ := checksPassed taken
          rw [deserializeFields] at decoded
          obtain ⟨_, -, decoded⟩ := checksPassed decoded
          obtain ⟨others, decoded, -⟩ := checksPassed decoded
          rw [checkInline]
          exact ih slots spans rest others tail decoded

/-- An accepted struct holds what its fields decode to, each from its own slice. -/
theorem deserializeStruct_ok {fields : List Desc} {data : Bytes} {values : List Value}
    (read : deserializeStruct fields data = .ok values) :
    ∃ slices, structSlices fields data = .ok slices
      ∧ deserializeFields fields slices = .ok values := by
  rw [deserializeStruct] at read
  obtain ⟨⟨slots, leading⟩, front, read⟩ := checksPassed read
  dsimp only at read
  -- Checking the fixed part ahead of the offsets passes or refuses, and never changes a value.
  have rest : (structBodies data slots leading >>= deserializeFields fields) = .ok values := by
    split at read
    · obtain ⟨_, -, read⟩ := checksPassed read
      exact read
    · exact read
  obtain ⟨slices, bodies, decoded⟩ := checksPassed rest
  exact ⟨slices, by simp [structSlices, front, bodies, Bind.bind, Except.bind], decoded⟩

/-- A struct whose fields each decode from their own slice is accepted, holding those values. -/
theorem deserializeStruct_of {fields : List Desc} {data : Bytes} {slices : List Bytes}
    {values : List Value}
    (sliced : structSlices fields data = .ok slices)
    (decoded : deserializeFields fields slices = .ok values) :
    deserializeStruct fields data = .ok values := by
  simp only [structSlices] at sliced
  obtain ⟨⟨slots, leading⟩, front, bodies⟩ := checksPassed sliced
  -- With offsets, every inline field was cut out as is, so the early check passes.
  have inline : (bodyStarts slots).isEmpty = false → checkInline fields slots = .ok () := by
    intro hasBodies
    simp only [structBodies, hasBodies, Bool.false_eq_true, ite_false] at bodies
    split at bodies
    · simp [throw_error, Bind.bind, Except.bind] at bodies
    · obtain ⟨spans, -, taken⟩ := checksPassed bodies
      exact checkInline_of_takeSlots data fields slots spans slices values taken decoded
  rw [deserializeStruct]
  simp only [front, Bind.bind, Except.bind]
  cases empty : (bodyStarts slots).isEmpty
  · simp [inline empty, bodies, decoded]
  · simp [bodies, decoded]

end EthLib.Serialization.Ssz
