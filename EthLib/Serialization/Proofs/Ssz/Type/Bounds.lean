module

public import EthLib.Serialization.Ssz.Type.Bounds
public import EthLib.Serialization.Proofs.Ssz.Codec.Size

/-!
# `Serialization.Proofs.Ssz.Type.Bounds`

The size of every encoding lies within the bounds of its type.

- A value that fits its type and encodes has at least `minSize` and at most `maxSize` bytes.
- So does every encoding under a well-formed type.
- A static type has both bounds equal to its fixed size.

The theorems do not say that a bound is attained.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- The bytes of a field are its own, then its offset. -/
theorem fieldSize_eq (shape : Desc) (size : Nat) :
    fieldSize shape size = size + offsetWidth shape := rfl

/-- The bounds of a size: at least `low`, and at most `high` where there is one. -/
def WithinBounds (low : Nat) (high : Option Nat) (size : Nat) : Prop :=
  low ≤ size ∧ ∀ bound, high = some bound → size ≤ bound

/-! ## Sums -/

/-- Each term at least `low` makes the sum at least the count times `low`. -/
theorem le_sum_map {α : Type} {f : α → Nat} {low : Nat} :
    ∀ {xs : List α}, (∀ x ∈ xs, low ≤ f x) → xs.length * low ≤ (xs.map f).sum
  | [], _ => by simp
  | x :: xs, h => by
    have hx := h x List.mem_cons_self
    have := le_sum_map (xs := xs) fun y hy => h y (List.mem_cons_of_mem x hy)
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.succ_mul]
    omega

/-- Each term at most `high` makes the sum at most the count times `high`. -/
theorem sum_map_le {α : Type} {f : α → Nat} {high : Nat} :
    ∀ {xs : List α}, (∀ x ∈ xs, f x ≤ high) → (xs.map f).sum ≤ xs.length * high
  | [], _ => by simp
  | x :: xs, h => by
    have hx := h x List.mem_cons_self
    have := sum_map_le (xs := xs) fun y hy => h y (List.mem_cons_of_mem x hy)
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.succ_mul]
    omega

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
      · have := le_sum_map (f := fun v => sizes v + offsetWidth element)
          (low := element.minSize + offsetWidth element) fun v hv => by
            have := (bounds v hv).1
            omega
        simp only [Desc.minSize]
        rw [← count]
        exact this
      · intro bound hb
        simp only [Desc.maxSize, Option.map_eq_some_iff] at hb
        obtain ⟨m, hm, rfl⟩ := hb
        have := sum_map_le (f := fun v => sizes v + offsetWidth element)
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
      have := sum_map_le (f := fun v => sizes v + offsetWidth element)
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
        have := sum_map_le (f := fun v => sizes v + offsetWidth element)
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

end EthLib.Serialization.Ssz
