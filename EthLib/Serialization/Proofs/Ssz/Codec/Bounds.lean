module

public import EthLib.Serialization.Ssz.Type.Bounds
public import EthLib.Serialization.Proofs.Ssz.Codec.Size
public import EthLib.Base.Proofs.List

/-!
# `Serialization.Proofs.Ssz.Codec.Bounds`

The size of every encoding lies within the bounds of its type, which need not be attained.

A value that fits a type whose largest encoding stays below `2^32` bytes always encodes.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- The bytes of a field are its own, then its offset. -/
theorem fieldSize_eq (shape : Desc) (size : Nat) :
    fieldSize shape size = size + offsetWidth shape := rfl

/-- The bounds of a size: at least `low`, and at most `high` where there is one. -/
def WithinBounds (low : Nat) (high : Option Nat) (size : Nat) : Prop :=
  low ≤ size ∧ ∀ bound, high = some bound → size ≤ bound

/-- The fields of a struct, each within the bounds of its type, are within the struct's bounds. -/
theorem fields_withinBounds {g : Desc → Value → Nat} :
    ∀ {fields : List Desc} {values : List Value}, fields.length = values.length →
      (∀ pair ∈ fields.zip values,
        WithinBounds pair.1.minSize pair.1.maxSize (g pair.1 pair.2)) →
      WithinBounds (Desc.fieldsMinSize fields) (Desc.fieldsMaxSize fields)
        ((fields.zip values).map fun (field, value) => fieldSize field (g field value)).sum
  | [], [], _, _ => by simp [WithinBounds, Desc.fieldsMinSize, Desc.fieldsMaxSize]
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | field :: fields, value :: values, h, each => by
    have hHead := each (field, value) List.mem_cons_self
    have hTail := fields_withinBounds (g := g) (Nat.succ.inj h) fun pair hp =>
      each pair (List.mem_cons_of_mem _ hp)
    obtain ⟨lowHead, highHead⟩ := hHead
    obtain ⟨lowTail, highTail⟩ := hTail
    dsimp only at lowHead highHead
    refine ⟨?_, ?_⟩
    · simp only [Desc.fieldsMinSize, List.zip_cons_cons, List.map_cons, List.sum_cons,
        fieldSize_eq]
      simp only [fieldSize_eq] at lowTail
      omega
    · intro bound hb
      simp only [Desc.fieldsMaxSize, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at hb
      obtain ⟨size, hs, remaining, hr, rfl⟩ := hb
      have head := highHead size hs
      have tail := highTail remaining hr
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, fieldSize_eq] at tail ⊢
      omega

/-- An option of a union has at least the fewest bytes of the options. -/
theorem optionsMinSize_le {option : Desc} :
    ∀ {options : List Desc}, option ∈ options → Desc.optionsMinSize options ≤ option.minSize
  | [], h => by cases h
  | [o], h => by
    rw [List.mem_singleton] at h
    subst h
    simp [Desc.optionsMinSize]
  | o :: o' :: rest, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp only [Desc.optionsMinSize]
      omega
    · have := optionsMinSize_le h
      simp only [Desc.optionsMinSize] at this ⊢
      omega

/-- An option of a union has at most the most bytes of the options. -/
theorem le_optionsMaxSize {option : Desc} :
    ∀ {options : List Desc} {bound : Nat}, option ∈ options →
      Desc.optionsMaxSize options = some bound → ∃ size, option.maxSize = some size ∧ size ≤ bound
  | [], _, h, _ => by cases h
  | o :: rest, bound, h, hb => by
    simp only [Desc.optionsMaxSize, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hb
    obtain ⟨size, hs, remaining, hr, rfl⟩ := hb
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨size, hs, Nat.le_max_left _ _⟩
    · obtain ⟨s, hs', hle⟩ := le_optionsMaxSize h hr
      exact ⟨s, hs', Nat.le_trans hle (Nat.le_max_right _ _)⟩

/-! ## Static types -/

/-- A type with a fixed size takes no offset. -/
theorem offsetWidth_of_fixedSize {shape : Desc} {width : Nat} (h : shape.fixedSize = some width) :
    offsetWidth shape = 0 := by
  simp [offsetWidth, Desc.isFixed, h]

/-- A static type has both bounds equal to its fixed size. -/
theorem bounds_of_fixedSize (shape : Desc) :
    ∀ {width : Nat}, shape.fixedSize = some width →
      shape.minSize = width ∧ shape.maxSize = some width := by
  induction shape using Desc.rec
    (motive_2 := fun fields => ∀ {width : Nat}, Desc.fieldsFixedSize fields = some width →
      Desc.fieldsMinSize fields = width ∧ Desc.fieldsMaxSize fields = some width) with
  | bool => intro width h; simp_all [Desc.fixedSize, Desc.minSize, Desc.maxSize]
  | uint w => intro width h; simp_all [Desc.fixedSize, Desc.minSize, Desc.maxSize]
  | byteVector n => intro width h; simp_all [Desc.fixedSize, Desc.minSize, Desc.maxSize]
  | bitVector n => intro width h; simp_all [Desc.fixedSize, Desc.minSize, Desc.maxSize]
  | byteList _ | bitList _ | progressiveBitList _ | list _ _ | progressiveList _ _
  | compatibleUnion _ _ => intro width h; simp [Desc.fixedSize] at h
  | vector element length ih =>
    intro width h
    simp only [Desc.fixedSize, Option.map_eq_some_iff] at h
    obtain ⟨e, he, rfl⟩ := h
    obtain ⟨hmin, hmax⟩ := ih he
    simp only [Desc.minSize, Desc.maxSize, hmin, hmax, offsetWidth_of_fixedSize he,
      Option.map_some, Nat.add_zero, Nat.mul_comm length e, and_self]
  | container names fields ih =>
    intro width h
    exact ih h
  | progressiveContainer active names fields ih =>
    intro width h
    exact ih h
  | nil =>
    rename_i width h
    simp_all [Desc.fieldsFixedSize, Desc.fieldsMinSize, Desc.fieldsMaxSize]
  | cons field fields ihHead ihTail =>
    rename_i width h
    simp only [Desc.fieldsFixedSize] at h
    split at h
    · rename_i w rest hw hrest
      cases h
      obtain ⟨hmin, hmax⟩ := ihHead hw
      obtain ⟨hmin', hmax'⟩ := ihTail hrest
      simp only [Desc.fieldsMinSize, Desc.fieldsMaxSize, hmin, hmax, hmin', hmax',
        offsetWidth_of_fixedSize hw, Nat.add_zero, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, and_self]
    · cases h

/-! ## Encodings -/

/-- A value that fits its type, with a structural size witness, is within the type's bounds. -/
theorem withinBounds_of_representable {shape : Desc} {value : Value} {size : Nat}
    (represented : Representable shape value size) :
    Fits shape value → WithinBounds shape.minSize shape.maxSize size := by
  induction represented with
  | bool value => exact fun _ => ⟨Nat.le_refl _, by simp [Desc.maxSize]⟩
  | uint width value => exact fun _ => ⟨Nat.le_refl _, by simp [Desc.maxSize]⟩
  | byteVector length data bounded =>
    intro fits
    cases fits with
    | byteVector exact => exact ⟨by simp [Desc.minSize, exact], by simp [Desc.maxSize, exact]⟩
  | byteList limit data bounded =>
    intro fits
    cases fits with
    | byteList within =>
      exact ⟨Nat.zero_le _, by simp only [Desc.maxSize, Option.some.injEq]; omega⟩
  | bitVector length data =>
    intro fits
    cases fits with
    | bitVector exact => exact ⟨by simp [Desc.minSize, exact], by simp [Desc.maxSize, exact]⟩
  | bitList limit data =>
    intro fits
    cases fits with
    | bitList within =>
      refine ⟨by simp only [Desc.minSize]; omega, ?_⟩
      simp only [Desc.maxSize, Option.some.injEq]
      omega
  | progressiveBitList limit data =>
    intro fits
    cases fits with
    | progressiveBitList within =>
      refine ⟨by simp only [Desc.minSize]; omega, ?_⟩
      intro bound hb
      cases limit with
      | none => simp [Desc.maxSize] at hb
      | some l =>
        simp only [Desc.maxSize, Option.map_some, Option.some.injEq] at hb
        simp only [withinBound, decide_eq_true_eq] at within
        omega
  | @vector element length values sizes each bounded ih =>
    intro fits
    cases fits with
    | vector count fitsEach =>
      have bounds v (hv : v ∈ values) := ih v hv (fitsEach v hv)
      simp only [fieldSize_eq]
      refine ⟨?_, ?_⟩
      · have := Base.le_sum_map (f := fun v => sizes v + offsetWidth element)
          (low := element.minSize + offsetWidth element) fun v hv => by
            have := (bounds v hv).1
            omega
        simp only [Desc.minSize]
        rw [← count]
        exact this
      · intro bound hb
        simp only [Desc.maxSize, Option.map_eq_some_iff] at hb
        obtain ⟨m, hm, rfl⟩ := hb
        have := Base.sum_map_le (f := fun v => sizes v + offsetWidth element)
          (high := m + offsetWidth element) fun v hv => by
            have := (bounds v hv).2 m hm
            omega
        rw [← count]
        exact this
  | @list element limit values sizes each bounded ih =>
    intro fits
    cases fits with
    | list within fitsEach =>
      have bounds v (hv : v ∈ values) := ih v hv (fitsEach v hv)
      refine ⟨Nat.zero_le _, ?_⟩
      intro bound hb
      simp only [Desc.maxSize, Option.map_eq_some_iff] at hb
      obtain ⟨m, hm, rfl⟩ := hb
      simp only [fieldSize_eq]
      have := Base.sum_map_le (f := fun v => sizes v + offsetWidth element)
        (high := m + offsetWidth element) fun v hv => by
          have := (bounds v hv).2 m hm
          omega
      exact Nat.le_trans this (Nat.mul_le_mul_right _ within)
  | @progressiveList element limit values sizes each bounded ih =>
    intro fits
    cases fits with
    | progressiveList within fitsEach =>
      have bounds v (hv : v ∈ values) := ih v hv (fitsEach v hv)
      refine ⟨Nat.zero_le _, ?_⟩
      intro bound hb
      cases limit with
      | none => simp [Desc.maxSize] at hb
      | some l =>
        simp only [Desc.maxSize, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.pure_def, Option.some.injEq] at hb
        obtain ⟨_, hl, m, hm, rfl⟩ := hb
        cases hl
        simp only [withinBound, decide_eq_true_eq] at within
        simp only [fieldSize_eq]
        have := Base.sum_map_le (f := fun v => sizes v + offsetWidth element)
          (high := m + offsetWidth element) fun v hv => by
            have := (bounds v hv).2 m hm
            omega
        exact Nat.le_trans this (Nat.mul_le_mul_right _ within)
  | @container names fields values sizes each bounded ih =>
    intro fits
    cases fits with
    | container paired fitsEach =>
      exact fields_withinBounds paired fun pair hp => ih pair hp (fitsEach pair hp)
  | @progressiveContainer active names fields values sizes each bounded ih =>
    intro fits
    cases fits with
    | progressiveContainer paired fitsEach =>
      exact fields_withinBounds paired fun pair hp => ih pair hp (fitsEach pair hp)
  | @compatibleUnion selectors options selector option data size named inner ih =>
    intro fits
    cases fits with
    | compatibleUnion ranged named' fitsInner =>
      rw [named] at named'
      cases named'
      have hmem := lookupOption_mem _ _ _ _ named
      obtain ⟨low, high⟩ := ih fitsInner
      refine ⟨?_, ?_⟩
      · have := optionsMinSize_le hmem
        simp only [Desc.minSize]
        omega
      · intro bound hb
        simp only [Desc.maxSize, Option.map_eq_some_iff] at hb
        obtain ⟨m, hm, rfl⟩ := hb
        obtain ⟨s, hs, hle⟩ := le_optionsMaxSize hmem hm
        have := high s hs
        omega

/-- Every encoding of a value that fits its type has a size within the type's bounds. -/
theorem withinBounds_of_serialize {shape : Desc} {value : Value} {bytes : Bytes}
    (fits : Fits shape value) (wrote : serialize shape value = .ok bytes) :
    shape.minSize ≤ bytes.size ∧ ∀ bound, shape.maxSize = some bound → bytes.size ≤ bound :=
  withinBounds_of_representable (representable_of_serialize shape value bytes wrote) fits

/-- Every encoding under a well-formed type has a size within the type's bounds.

The encoder checks what `Fits` asks, so its success stands in for that hypothesis. -/
theorem withinBounds_of_serialize_of_wellFormed {shape : Desc} {value : Value} {bytes : Bytes}
    (formed : shape.wellFormed = .ok ()) (wrote : serialize shape value = .ok bytes) :
    shape.minSize ≤ bytes.size ∧ ∀ bound, shape.maxSize = some bound → bytes.size ≤ bound :=
  withinBounds_of_serialize (fits_of_serialize shape value formed ⟨bytes, wrote⟩) wrote

/-! ## Encodings that fit the offset range -/

/-- Members of a list that each have some size have them all under one size function. -/
private theorem choose_sizes {α : Type} {P : α → Nat → Prop} {xs : List α}
    (each : ∀ x ∈ xs, ∃ size, P x size) : ∃ sizes : α → Nat, ∀ x ∈ xs, P x (sizes x) := by
  classical
  -- Pick the chosen size where one exists, and zero elsewhere.
  refine ⟨fun x => if h : ∃ size, P x size then h.choose else 0, fun x hx => ?_⟩
  simp only [each x hx, ↓reduceDIte]
  exact (each x hx).choose_spec

/-- Elements within a count, whose most bytes in all stay below `2^32`, have sizes below it.

The sum of their bytes, offsets included, stays below `2^32` too. -/
private theorem sequence_witness {element : Desc} {values : List Value} {high count : Nat}
    (largest : element.maxSize = some high) (fitsEach : ∀ v ∈ values, Fits element v)
    (ih : ∀ v ∈ values, ∀ bound, element.maxSize = some bound → bound < 2 ^ 32 →
      ∃ size, Representable element v size)
    (within : values.length ≤ count) (small : count * (high + offsetWidth element) < 2 ^ 32) :
    ∃ sizes : Value → Nat, (∀ v ∈ values, Representable element v (sizes v)) ∧
      (values.map fun v => fieldSize element (sizes v)).sum < 2 ^ 32 := by
  -- A present element makes the count positive, so the element bound is below the total.
  have each : ∀ v ∈ values, ∃ size, Representable element v size := fun v hv => by
    have positive : 0 < count := Nat.lt_of_lt_of_le (List.length_pos_of_mem hv) within
    have : high ≤ count * (high + offsetWidth element) :=
      Nat.le_trans (Nat.le_add_right _ _) (Nat.le_mul_of_pos_left _ positive)
    exact ih v hv high largest (by omega)
  obtain ⟨sizes, represented⟩ := choose_sizes each
  refine ⟨sizes, represented, ?_⟩
  -- Each element has at most the element bound, so the sum has at most the total.
  have := Base.sum_map_le (f := fun v => fieldSize element (sizes v))
    (high := high + offsetWidth element) fun v hv => by
      have := (withinBounds_of_representable (represented v hv) (fitsEach v hv)).2 high largest
      simp only [fieldSize_eq]
      omega
  have := Nat.mul_le_mul_right (high + offsetWidth element) within
  omega

/-- A field of a struct has at most the most bytes of the fields. -/
private theorem le_fieldsMaxSize {field : Desc} :
    ∀ {fields : List Desc} {bound : Nat}, field ∈ fields →
      Desc.fieldsMaxSize fields = some bound → ∃ size, field.maxSize = some size ∧ size ≤ bound
  | [], _, h, _ => by cases h
  | f :: rest, bound, h, hb => by
    simp only [Desc.fieldsMaxSize, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hb
    obtain ⟨size, hs, remaining, hr, rfl⟩ := hb
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨size, hs, by omega⟩
    · obtain ⟨s, hs', hle⟩ := le_fieldsMaxSize h hr
      exact ⟨s, hs', by omega⟩

/-- Fields under a bound below `2^32` have sizes whose sum stays below `2^32`. -/
private theorem fields_witness {fields : List Desc} {values : List Value} {bound : Nat}
    (paired : fields.length = values.length)
    (fitsEach : ∀ pair ∈ fields.zip values, Fits pair.1 pair.2)
    (ih : ∀ pair ∈ fields.zip values, ∀ bound, pair.1.maxSize = some bound → bound < 2 ^ 32 →
      ∃ size, Representable pair.1 pair.2 size)
    (largest : Desc.fieldsMaxSize fields = some bound) (small : bound < 2 ^ 32) :
    ∃ sizes : Desc → Value → Nat,
      (∀ pair ∈ fields.zip values, Representable pair.1 pair.2 (sizes pair.1 pair.2)) ∧
      ((fields.zip values).map fun (field, value) => fieldSize field (sizes field value)).sum
        < 2 ^ 32 := by
  -- Each field's bound is at most the struct's, so the induction hypothesis applies.
  have each : ∀ pair ∈ fields.zip values, ∃ size, Representable pair.1 pair.2 size :=
    fun pair hp => by
      obtain ⟨size, hs, hle⟩ := le_fieldsMaxSize (List.of_mem_zip hp).1 largest
      exact ih pair hp size hs (by omega)
  obtain ⟨sizes, represented⟩ := choose_sizes each
  refine ⟨fun field value => sizes (field, value), represented, ?_⟩
  -- The fields within their bounds sum to at most the struct's bound.
  have := (fields_withinBounds (g := fun field value => sizes (field, value)) paired
    fun pair hp => withinBounds_of_representable (represented pair hp) (fitsEach pair hp)).2
      bound largest
  exact Nat.lt_of_le_of_lt this small

/-- A value that fits a type whose encodings stay below `2^32` bytes has a size witness. -/
theorem representable_of_maxSize {shape : Desc} {value : Value} (fits : Fits shape value)
    {bound : Nat} (largest : shape.maxSize = some bound) (small : bound < 2 ^ 32) :
    ∃ size, Representable shape value size := by
  induction fits generalizing bound with
  | bool b => exact ⟨_, .bool b⟩
  | @uint width n _ => exact ⟨_, .uint width n⟩
  | @byteVector length data exact =>
    simp only [Desc.maxSize, Option.some.injEq] at largest
    exact ⟨_, .byteVector length data (by omega)⟩
  | @byteList limit data within =>
    simp only [Desc.maxSize, Option.some.injEq] at largest
    exact ⟨_, .byteList limit data (by omega)⟩
  | @bitVector length data _ => exact ⟨_, .bitVector length data⟩
  | @bitList limit data _ => exact ⟨_, .bitList limit data⟩
  | @progressiveBitList limit data _ => exact ⟨_, .progressiveBitList limit data⟩
  | vector count fitsEach ih =>
    simp only [Desc.maxSize, Option.map_eq_some_iff] at largest
    obtain ⟨high, hm, rfl⟩ := largest
    obtain ⟨sizes, each, bounded⟩ :=
      sequence_witness hm fitsEach ih (Nat.le_of_eq count) small
    exact ⟨_, .vector each bounded⟩
  | list within fitsEach ih =>
    simp only [Desc.maxSize, Option.map_eq_some_iff] at largest
    obtain ⟨high, hm, rfl⟩ := largest
    obtain ⟨sizes, each, bounded⟩ := sequence_witness hm fitsEach ih within small
    exact ⟨_, .list each bounded⟩
  | @progressiveList element limit elements within fitsEach ih =>
    cases limit with
    | none => simp [Desc.maxSize] at largest
    | some l =>
      simp only [Desc.maxSize, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at largest
      obtain ⟨_, hl, high, hm, rfl⟩ := largest
      cases hl
      simp only [withinBound, decide_eq_true_eq] at within
      obtain ⟨sizes, each, bounded⟩ := sequence_witness hm fitsEach ih within small
      exact ⟨_, .progressiveList each bounded⟩
  | container paired fitsEach ih =>
    obtain ⟨sizes, each, bounded⟩ := fields_witness paired fitsEach ih largest small
    exact ⟨_, .container each bounded⟩
  | progressiveContainer paired fitsEach ih =>
    obtain ⟨sizes, each, bounded⟩ := fields_witness paired fitsEach ih largest small
    exact ⟨_, .progressiveContainer each bounded⟩
  | compatibleUnion ranged named inner ih =>
    -- The named option has at most the union's bound less the selector byte.
    simp only [Desc.maxSize, Option.map_eq_some_iff] at largest
    obtain ⟨high, hm, rfl⟩ := largest
    obtain ⟨size, hs, hle⟩ := le_optionsMaxSize (lookupOption_mem _ _ _ _ named) hm
    obtain ⟨inside, represented⟩ := ih hs (by omega)
    exact ⟨_, .compatibleUnion named represented⟩

/-- A value that fits a type whose encodings stay below `2^32` bytes encodes. -/
theorem serialize_fits_exists_ok_of_maxSize {shape : Desc} {value : Value}
    (fits : Fits shape value) {bound : Nat} (largest : shape.maxSize = some bound)
    (small : bound < 2 ^ 32) :
    ∃ bytes, serialize shape value = .ok bytes := by
  obtain ⟨size, represented⟩ := representable_of_maxSize fits largest small
  obtain ⟨bytes, wrote, -⟩ := represented.serialize fits
  exact ⟨bytes, wrote⟩

end EthLib.Serialization.Ssz
