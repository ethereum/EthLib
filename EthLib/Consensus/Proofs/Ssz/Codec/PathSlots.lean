import EthLib.Consensus.Proofs.Ssz.Codec.Layout

/-! Progressive field ordinals and materialized layout positions preserve the same values. -/

namespace EthLib.Consensus.Ssz

/-- Selecting a field ordinal locates that same field in the layout, skipping every gap. -/
theorem placeSlots_position {active : List Bool} {fields : List (Desc × Value)}
    {slots : List (Option (Desc × Value))}
    (placed : placeSlots active fields = .ok slots) (ordinal : Nat) (field : Desc × Value)
    (selected : fields[ordinal]? = some field) :
    ∃ position, activePosition active ordinal = some position ∧
      slots[position]? = some (some field) := by
  -- A gap shifts the position, while an occupied slot also consumes one field ordinal.
  fun_induction placeSlots active fields generalizing slots ordinal with
  | case1 => simp at selected
  -- An inactive position shifts the final tree index without consuming the field ordinal.
  | case2 active fields ih =>
    cases tail : placeSlots active fields <;>
      simp [tail, Bind.bind, Except.bind, pure, Except.pure] at placed
    obtain ⟨position, found, same⟩ := ih tail ordinal selected
    exact ⟨position + 1, by simp [activePosition, found], by simpa [← placed] using same⟩
  -- An active position consumes one field and one tree position together.
  | case3 active first fields ih =>
    cases tail : placeSlots active fields <;>
      simp [tail, Bind.bind, Except.bind, pure, Except.pure] at placed
    subst slots
    cases ordinal with
    -- The requested first field is the occupied position currently being visited.
    | zero => simp_all [activePosition]
    -- A later field is found in the suffix and shifted past this occupied position.
    | succ ordinal =>
      obtain ⟨position, found, same⟩ := ih tail ordinal (by simpa using selected)
      exact ⟨position + 1, by simp [activePosition, found], by simpa using same⟩
  | case4 => simp at placed

/-- A successful progressive field path reads the paired type and value at its active position. -/
theorem layoutSlots_position {active : List Bool} {fields : List Desc} {values : List Value}
    {slots : List (Option (Desc × Value))}
    (placed : layoutSlots active fields values = .ok slots)
    (ordinal : Nat) (child : Desc) (inner : Value)
    (selectedType : fields[ordinal]? = some child) (selectedValue : values[ordinal]? = some inner) :
    ∃ position, layoutPosition active ordinal = .ok position ∧
      slots[position]? = some (some (child, inner)) := by
  -- Pairing declarations and values preserves the ordinal before gaps are inserted.
  simp only [layoutSlots] at placed
  split at placed <;> try contradiction
  split at placed <;> try contradiction
  obtain ⟨position, found, same⟩ := placeSlots_position placed ordinal (child, inner)
    (List.getElem?_zip_eq_some.mpr ⟨selectedType, selectedValue⟩)
  exact ⟨position, by simp [layoutPosition, found], same⟩

end EthLib.Consensus.Ssz
