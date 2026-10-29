import EthLib.Serialization.Proofs.Ssz.Codec.Fits

/-! Admissible values encode successfully unless a composite exceeds the offset budget. -/

namespace EthLib.Serialization.Ssz

private def OnlyOverflow {α : Type} (result : Except Err α) : Prop :=
  ∀ fault, result = .error fault → ∃ size,
    fault = .offsetOverflow size ∧ 2 ^ (8 * bytesPerOffset) ≤ size

private theorem overflow_bind {α β : Type} {first : Except Err α}
    {next : α → Except Err β} (head : OnlyOverflow first)
    (tail : ∀ value, first = .ok value → OnlyOverflow (next value)) :
    OnlyOverflow (first >>= next) := by
  -- A chain either propagates its first failure or returns the continuation's result.
  cases step : first with
  | error fault => simpa [OnlyOverflow, step, Bind.bind, Except.bind] using head
  | ok value => simpa [Bind.bind, Except.bind] using tail value step

private theorem overflow_assemble (inline : List Bool) (parts : List Bytes) :
    OnlyOverflow (assemble inline parts) := by
  -- The only assembly failure is a total byte count outside the four-byte offset range.
  intro fault failed
  simp only [assemble] at failed
  split at failed
  · -- A failing assembly records exactly the offending header-plus-body size.
    exact ⟨_, (Except.error.inj failed).symm, ‹_›⟩
  -- Below 2^32 bytes, assembly returns bytes, contradicting the alleged failure.
  · cases failed

private theorem overflow_each {element : Desc} : ∀ values,
    (∀ value ∈ values, OnlyOverflow (serialize element value)) →
    OnlyOverflow (serializeEach element values) := by
  intro values
  -- A sequence inherits its possible failures from the encodings of its elements.
  induction values with
  | nil => intro _ fault failed; simp [serializeEach] at failed
  | cons value rest ih =>
    intro each
    rw [serializeEach]
    -- First account for a failure in the current element.
    apply overflow_bind (each value List.mem_cons_self)
    intro head _
    -- The remaining elements satisfy the same restriction by induction.
    apply overflow_bind (ih (fun item member => each item (List.mem_cons_of_mem _ member)))
    -- Combining successful element encodings introduces no new failure.
    intro tail _ fault failed
    cases failed

private theorem overflow_sequence {element : Desc} {values : List Value}
    (each : ∀ value ∈ values, OnlyOverflow (serialize element value)) :
    OnlyOverflow (serializeSequence element values) := by
  -- Element failures propagate.
  -- Assembly adds only its own offset-range check.
  rw [serializeSequence]
  exact overflow_bind (overflow_each values each) fun parts _ => overflow_assemble _ parts

private theorem overflow_fields : ∀ fields values,
    fields.length = values.length →
    (∀ pair ∈ fields.zip values, OnlyOverflow (serialize pair.1 pair.2)) →
    OnlyOverflow (serializeFields fields values) := by
  intro fields
  -- Field declarations and values advance together, preserving their equal counts.
  induction fields with
  | nil =>
    intro values paired _ fault failed
    -- No declarations means no values, so there is nothing left that could fail.
    simp [List.eq_nil_of_length_eq_zero paired.symm, serializeFields] at failed
  | cons field fields ih =>
    intro values paired each
    cases values with
    | nil => simp at paired
    | cons value values =>
      rw [serializeFields]
      -- A field can fail only through the overflow already established for its own encoding.
      apply overflow_bind (each (field, value) List.mem_cons_self)
      intro head _
      -- The remaining paired fields inherit the same property.
      apply overflow_bind (ih values (by simpa using paired)
        (fun pair member => each pair (List.mem_cons_of_mem _ member)))
      -- Returning the completed list of field encodings cannot introduce an error.
      intro tail _ fault failed
      cases failed

private theorem overflow_struct {fields : List Desc} {values : List Value}
    (paired : fields.length = values.length)
    (each : ∀ pair ∈ fields.zip values, OnlyOverflow (serialize pair.1 pair.2)) :
    OnlyOverflow (serializeStruct fields values) := by
  -- A container first encodes its fields, then assembles their fixed entries and offset table.
  rw [serializeStruct]
  -- Once every field succeeds, only the total composite size can prevent assembly.
  exact overflow_bind (overflow_fields fields values paired each) fun parts _ =>
    overflow_assemble _ parts

private theorem overflow_of_fits {shape : Desc} {value : Value} (fits : Fits shape value) :
    OnlyOverflow (serialize shape value) := by
  -- Admissibility already supplies scalar ranges, collection bounds, and matching field counts.
  induction fits with
  | bool => intro fault failed; simp [serialize] at failed
  | uint bound => intro fault failed; simp [serialize, bound] at failed
  -- A byte array can fail only the size bound it shares with every sequence.
  | byteVector sized | byteList sized =>
    intro fault failed
    simp only [serialize, sized, bne_self_eq_false, Bool.false_eq_true, ite_false] at failed
    repeat' split at failed
    -- The count checks pass on an admissible value, leaving the size bound or success.
    all_goals first
      | omega
      | exact ⟨_, (Except.error.inj failed).symm, by omega⟩
      | cases failed
  | bitVector sized => intro fault failed; simp [serialize, sized] at failed
  | bitList within => intro fault failed; simp [serialize, within] at failed
  | @progressiveBitList limit _ within =>
    intro fault failed
    simp [serialize, boundCheck_of_withinBound limit _ within, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at failed
  -- Composite values inherit element failures and the final assembly size restriction.
  | vector sized _ ih =>
    simpa only [serialize, sized, beq_self_eq_true, ite_eq_left] using overflow_sequence ih
  | list within _ ih =>
    simpa only [serialize, ite_eq_left within] using overflow_sequence ih
  | @progressiveList _ limit _ within _ ih =>
    simpa only [serialize, boundCheck_of_withinBound limit _ within, Bind.bind, Except.bind]
      using overflow_sequence ih
  | container paired _ ih => simpa only [serialize] using overflow_struct paired ih
  | progressiveContainer paired _ ih => simpa only [serialize] using overflow_struct paired ih
  | compatibleUnion ranged named _ ih =>
    simp only [serialize, named, checkSelector_of_range ranged, Bind.bind, Except.bind]
    -- A union propagates its selected payload failure.
    apply overflow_bind ih
    -- Adding the selector byte to a successful payload creates no offset table.
    intro body _ fault failed
    cases failed

/-- A valid value either encodes or identifies an overflowing composite size. -/
theorem serialize_fits_or_overflow {shape : Desc} {value : Value} (fits : Fits shape value) :
    (∃ bytes, serialize shape value = .ok bytes) ∨
    (∃ size, 2 ^ (8 * bytesPerOffset) ≤ size ∧
      serialize shape value = .error (.offsetOverflow size)) := by
  -- Total evaluation has two outcomes, and admissibility excludes every other error.
  cases result : serialize shape value with
  | ok bytes => exact .inl ⟨bytes, rfl⟩
  | error fault =>
    obtain ⟨size, rfl, large⟩ := overflow_of_fits fits fault result
    exact .inr ⟨size, large, rfl⟩

end EthLib.Serialization.Ssz
