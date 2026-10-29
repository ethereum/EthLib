import EthLib.Consensus.Proofs.Ssz.Codec.Admits
import EthLib.Consensus.Proofs.Ssz.Type.DefaultLaws

/-! The executable value checker reflects declarative admissibility. -/

namespace EthLib.Consensus.Ssz

/-- A homogeneous sequence passes exactly when each element passes its own check. -/
theorem Value.allFit_eq_true (element : Desc) (values : List Value) :
    Value.allFit element values = true ↔ ∀ value ∈ values, Value.fits element value = true := by
  -- Each step checks the first element and then the remaining sequence.
  induction values with
  | nil => simp [Value.allFit]
  | cons value rest ih => simp [Value.allFit, ih]

/-- Field checking requires equal counts and a successful check for every paired field. -/
theorem Value.fieldsFit_eq_true (fields : List Desc) (values : List Value) :
    Value.fieldsFit fields values = true ↔ fields.length = values.length ∧
      ∀ pair ∈ fields.zip values, Value.fits pair.1 pair.2 = true := by
  -- Both lists must end together, so pairing cannot silently discard a field or value.
  induction fields generalizing values with
  | nil => cases values <;> simp [Value.fieldsFit]
  | cons field fields ih =>
    cases values <;> simp [Value.fieldsFit, ih, and_left_comm]

/-- Union checking follows exactly the option selected by the shared selector lookup. -/
theorem Value.optionFits_eq_true (selectors : List Nat) (options : List Desc)
    (selector : Nat) (data : Value) :
    Value.optionFits selectors options selector data = true ↔
      ∃ option, lookupOption selectors options selector = .ok option ∧ Value.fits option data = true := by
  -- An unmatched selector advances through both declaration lists together.
  -- The first matching selector determines the payload type.
  induction selectors generalizing options with
  | nil => cases options <;> simp [Value.optionFits, lookupOption]
  | cons chosen selectors ih =>
    cases options <;> by_cases matched : chosen = selector <;>
      simp [Value.optionFits, lookupOption, matched, ih]

/-- Every declaratively admitted value passes the executable checker. -/
theorem Fits.checked {shape : Desc} {value : Value} (fitted : Fits shape value) :
    Value.fits shape value = true := by
  -- Induction follows the admitted value, including each nested field and element.
  induction fitted <;> simp_all [Value.fits, Value.allFit_eq_true, Value.fieldsFit_eq_true,
    Value.optionFits_eq_true]

/-- For a real declaration, a successful executable check establishes admissibility. -/
theorem fits_of_checked (shape : Desc) (value : Value) (sound : shape.wellFormed = .ok ())
    (checked : Value.fits shape value = true) : Fits shape value := by
  -- Validity descends with the declaration, supplying each selected union option's bounds.
  induction shape using Desc.rec
    (motive_2 := fun fields => ∀ field ∈ fields, ∀ value,
      field.wellFormed = .ok () → Value.fits field value = true → Fits field value)
    generalizing value with
  | bool | uint | byteVector | byteList | bitVector | bitList | progressiveBitList =>
    cases value <;> simp [Value.fits] at checked
    first | exact .bool _ | constructor; exact checked
  -- Fixed and bounded sequences combine a count condition with every child’s admissibility.
  | vector _ _ ih | list _ _ ih | progressiveList _ _ ih =>
    cases value <;> simp [Value.fits, Value.allFit_eq_true] at checked
    constructor
    · exact checked.1
    · intro held member
      refine ih held ?_ (checked.2 held member)
      first
        | exact wellFormed_vector sound
        | exact wellFormed_list sound
        | exact wellFormed_progressiveList sound
  -- A paired field is both declared and successfully checked at the same ordinal.
  | container _ fields ih | progressiveContainer _ _ fields ih =>
    cases value <;> simp [Value.fits, Value.fieldsFit_eq_true] at checked
    constructor
    · exact checked.1
    · intro pair member
      have field := (List.of_mem_zip member).1
      refine ih pair.1 field pair.2 (allWellFormed_mem fields ?_ pair.1 field)
        (checked.2 pair.1 pair.2 member)
      first | exact wellFormed_container sound | exact wellFormed_progressiveContainer sound
  -- A valid declaration bounds the selected tag and validates its chosen option type.
  | compatibleUnion selectors options ih =>
    cases value <;> simp [Value.fits, Value.optionFits_eq_true] at checked
    obtain ⟨option, named, inner⟩ := checked
    -- Successful selector lookup places the chosen type among the validated options.
    have member := lookupOption_mem selectors options _ option named
    exact .compatibleUnion
      (wellFormed_union_selectors sound _ (lookupOption_selector selectors options _ option named))
      named (ih option member _ (allWellFormed_mem options (wellFormed_union sound) option member) inner)
  | nil => intros; contradiction
  -- Membership selects either the current field's proof or the remaining field-list proof.
  | cons _ _ ihHead ihTail =>
    rename_i held member value sound checked
    exact List.forall_mem_cons.mpr ⟨ihHead, ihTail⟩ held member value sound checked

/--
On well-formed declarations, executable checking is equivalent to declarative admissibility.

Declaration validity supplies the selector bound required by the union's one-byte encoding.
-/
theorem Value.fits_eq_true {shape : Desc} {value : Value} (sound : shape.wellFormed = .ok ()) :
    Value.fits shape value = true ↔ Fits shape value :=
  ⟨fits_of_checked shape value sound, Fits.checked⟩

/-- Every successfully constructed default passes the executable value checker. -/
theorem default_checked {shape : Desc} {value : Value} (made : shape.default = .ok value) :
    Value.fits shape value = true :=
  (default_fits shape value made).checked

end EthLib.Consensus.Ssz
