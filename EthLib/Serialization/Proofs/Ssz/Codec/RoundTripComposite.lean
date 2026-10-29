import EthLib.Serialization.Proofs.Ssz.Codec.RoundTripScalar

/-! Round-trip laws for sequences, fields, and selected union options. -/

namespace EthLib.Serialization.Ssz

/--
Decoding an option walks to the same one the encoder looked up.

Both walks read the selectors in the same order, so the option found is the option meant.
-/
theorem deserializeOption_of_lookup :
    ∀ (selectors : List Nat) (options : List Desc) (selector : Nat) (option : Desc)
      (body : Bytes) (value : Value),
      minSelector ≤ selector ∧ selector ≤ maxSelector →
      lookupOption selectors options selector = .ok option →
      deserialize option body = .ok value →
      deserializeOption selectors options selector body = .ok (.union selector value) := by
  intro selectors
  induction selectors with
  | nil =>
    -- No selectors name no option, so the lookup could not have answered.
    intro options _ _ _ _ _ found _
    cases options <;> simp [lookupOption] at found
  | cons chosen rest ih =>
    intro options selector option body value ranged found decoded
    cases options with
    | nil => simp [lookupOption] at found
    | cons candidate others =>
      -- Either this selector is the one named, or the walk moves along.
      simp only [lookupOption, deserializeOption] at found ⊢
      split at found <;> simp_all [checkSelector, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A union reads back whatever it wrote, once its option does. -/
theorem roundTrip_compatibleUnion {selectors : List Nat} {options : List Desc}
    {selector : Nat} {option : Desc} {data : Value}
    (bounded : minSelector ≤ selector ∧ selector ≤ maxSelector)
    (named : lookupOption selectors options selector = .ok option)
    (inner : ∀ body, serialize option data = .ok body → deserialize option body = .ok data) :
    ∀ bytes, serialize (.compatibleUnion selectors options) (.union selector data) = .ok bytes →
      deserialize (.compatibleUnion selectors options) bytes
        = .ok (.union selector data) := by
  intro bytes wrote
  cases inside : serialize option data with
  | error _ =>
    -- The option refused, so the union refused, and nothing was written to read back.
    simp [serialize, named, inside, checkSelector_of_range bounded, Bind.bind, Except.bind] at wrote
  | ok body =>
    -- The selector is one byte in front of the option's own encoding.
    simp only [serialize, named, inside, checkSelector_of_range bounded, Bind.bind, Except.bind, Pure.pure, Except.pure,
      Except.ok.injEq] at wrote
    subst wrote
    -- The selector byte is there to be read, and it reads back as the selector.
    have firstIs : (#[UInt8.ofNat selector] ++ body)[0]!.toNat = selector := by
      rw [getElem!_pos _ 0 (by simp; omega), Array.getElem_append_left (by simp)]
      simp [Nat.mod_eq_of_lt (show selector < 256 by have top : maxSelector = 127 := rfl; omega)]
    simp [deserialize]
    rw [firstIs]
    exact deserializeOption_of_lookup selectors options selector option body data bounded named
      (inner body inside)

/-- Encoding a struct's fields gives one part per field. -/
theorem serializeFields_length :
    ∀ (fields : List Desc) (values : List Value) (parts : List Bytes),
      serializeFields fields values = .ok parts → fields.length = parts.length := by
  intro fields
  -- Each successful field encoding contributes one output part in declaration order.
  induction fields with
  | nil => intro values parts wrote; cases values <;> simp_all [serializeFields]
  | cons field fields ih =>
    intro values parts wrote
    cases values with
    | nil => simp [serializeFields] at wrote
    | cons value values =>
      cases head : serialize field value <;> cases tail : serializeFields fields values <;>
        simp [serializeFields, head, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] at wrote
      -- The returned list contains the current part followed by the inductively counted remainder.
      subst wrote
      simp [ih values _ tail]

/-- Every part is as wide as the field it was written for declares. -/
theorem serializeFields_widths :
    ∀ (fields : List Desc) (values : List Value) (parts : List Bytes),
      serializeFields fields values = .ok parts →
      (∀ pair ∈ fields.zip values, ∀ width bytes, pair.1.fixedSize = some width →
        serialize pair.1 pair.2 = .ok bytes → bytes.size = width) →
      ∀ pair ∈ fields.zip parts, ∀ width, pair.1.fixedSize = some width →
        pair.2.size = width := by
  intro fields
  -- Carry the declared fixed width from each field-value pair to its corresponding encoded part.
  induction fields with
  | nil => intro values parts wrote _ pair member; cases values <;> simp_all
  | cons field fields ih =>
    intro values parts wrote widths pair member
    cases values with
    | nil => simp [serializeFields] at wrote
    | cons value values =>
      cases head : serialize field value <;> cases tail : serializeFields fields values <;>
        simp [serializeFields, head, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] at wrote
      subst wrote
      -- Either this is the field just written, or one of those behind it.
      rcases List.mem_cons.mp member with rfl | later
      · exact fun width fixed => widths (field, value) (by simp) width _ fixed head
      · exact ih values _ tail (fun p m => widths p (List.mem_cons_of_mem _ m)) pair later

/-- Decoding a struct's parts gives back the values, once every field reads back. -/
theorem deserializeFields_reads_back :
    ∀ (fields : List Desc) (values : List Value) (parts : List Bytes),
      serializeFields fields values = .ok parts →
      (∀ pair ∈ fields.zip values, ∀ bytes, serialize pair.1 pair.2 = .ok bytes →
        deserialize pair.1 bytes = .ok pair.2) →
      deserializeFields fields parts = .ok values := by
  intro fields
  -- Reconstruct each field value using its own round-trip guarantee.
  induction fields with
  | nil =>
    intro values parts wrote _
    cases values <;> simp_all [serializeFields, deserializeFields]
  | cons field fields ih =>
    intro values parts wrote reads
    cases values with
    | nil => simp [serializeFields] at wrote
    | cons value values =>
      cases head : serialize field value <;> cases tail : serializeFields fields values <;>
        simp [serializeFields, head, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] at wrote
      subst wrote
      -- The first field decodes to its original value and the suffix follows by induction.
      simp only [deserializeFields, reads (field, value) (by simp) _ head,
        ih values _ tail (fun p m => reads p (List.mem_cons_of_mem _ m)), Bind.bind, Except.bind]
      rfl

/--
Structural premises for proving value round trips.

Fixed-width lists need a positive element width so byte length determines their count.
Composite declarations require the corresponding premises for every nested type.
-/
inductive Recovers : Desc → Prop
  /-- A boolean. -/
  | bool : Recovers .bool
  /-- An unsigned integer of any width. -/
  | uint (width : Nat) : Recovers (.uint width)
  /-- A fixed byte string. -/
  | byteVector (length : Nat) : Recovers (.byteVector length)
  /-- A bounded byte string. -/
  | byteList (limit : Nat) : Recovers (.byteList limit)
  /-- A fixed bit sequence. -/
  | bitVector (length : Nat) : Recovers (.bitVector length)
  /-- A bounded bit sequence. -/
  | bitList (limit : Nat) : Recovers (.bitList limit)
  /-- A progressive bit sequence. -/
  | progressiveBitList (limit : Option Nat) : Recovers (.progressiveBitList limit)
  /-- A sequence of fixed elements, once the element is covered. -/
  | vectorFixed {element : Desc} {length width : Nat} (fixed : element.fixedSize = some width)
      (inner : Recovers element) : Recovers (.vector element length)
  /-- A bounded sequence of fixed elements, whose count the data itself gives. -/
  | listFixed {element : Desc} {limit width : Nat} (fixed : element.fixedSize = some width)
      (positive : 0 < width) (inner : Recovers element) : Recovers (.list element limit)
  /-- A progressive sequence of fixed elements, on the same terms. -/
  | progressiveListFixed {element : Desc} {limit : Option Nat} {width : Nat}
      (fixed : element.fixedSize = some width) (positive : 0 < width)
      (inner : Recovers element) : Recovers (.progressiveList element limit)
  /-- A sequence of variable elements, each reached through its offset. -/
  | vectorVarying {element : Desc} {length : Nat} (varying : element.fixedSize = none)
      (inner : Recovers element) : Recovers (.vector element length)
  /-- A bounded sequence of variable elements, whose count the table itself gives. -/
  | listVarying {element : Desc} {limit : Nat} (varying : element.fixedSize = none)
      (inner : Recovers element) : Recovers (.list element limit)
  /-- A progressive sequence of variable elements, on the same terms. -/
  | progressiveListVarying {element : Desc} {limit : Option Nat}
      (varying : element.fixedSize = none)
      (inner : Recovers element) : Recovers (.progressiveList element limit)
  /-- A struct, once every field it declares is covered. -/
  | container {names : List String} {fields : List Desc}
      (inner : ∀ field ∈ fields, Recovers field) : Recovers (.container names fields)
  /-- A struct with a layout, on the same terms. -/
  | progressiveContainer {active : List Bool} {names : List String} {fields : List Desc}
      (inner : ∀ field ∈ fields, Recovers field) :
      Recovers (.progressiveContainer active names fields)
  /-- A union, once every option it declares is covered. -/
  | compatibleUnion {selectors : List Nat} {options : List Desc}
      (inner : ∀ option ∈ options, Recovers option) :
      Recovers (.compatibleUnion selectors options)

/--
What a covered shape guarantees.

The round trip and the declared width are proven together, because a struct needs the width of each field it holds before it can read the next one back.
-/
def Recovered (shape : Desc) (value : Value) : Prop :=
  (∀ bytes, serialize shape value = .ok bytes → deserialize shape bytes = .ok value)
    ∧ ∀ width bytes, shape.fixedSize = some width → serialize shape value = .ok bytes →
        bytes.size = width

/--
Reading back whatever was written follows from the round trip.

An encoder may refuse a value whose encoding no offset could name, and then there is nothing to read back, so this is the form the composite shapes are stated in.
-/
theorem reads_back {shape : Desc} {value : Value}
    (whole : serialize shape value >>= deserialize shape = .ok value) :
    ∀ bytes, serialize shape value = .ok bytes → deserialize shape bytes = .ok value := by
  -- Specialize the composed round trip to the particular successful encoder result.
  intro bytes wrote
  rwa [wrote] at whole

/-- Encoding a sequence gives one part per element. -/
theorem serializeEach_length :
    ∀ (element : Desc) (elements : List Value) (parts : List Bytes),
      serializeEach element elements = .ok parts → parts.length = elements.length := by
  intro element elements
  -- Every successful element encoding adds one part, so sequence length is preserved.
  induction elements with
  | nil => intro parts wrote; simp_all [serializeEach]
  | cons value values ih =>
    intro parts wrote
    cases head : serialize element value <;> cases tail : serializeEach element values <;>
      simp [serializeEach, head, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] at wrote
    subst wrote
    simp [ih _ tail]

/-- Every part is as wide as the element type declares. -/
theorem serializeEach_widths :
    ∀ (element : Desc) (elements : List Value) (parts : List Bytes) (width : Nat),
      element.fixedSize = some width →
      serializeEach element elements = .ok parts →
      (∀ value ∈ elements, ∀ bytes, serialize element value = .ok bytes → bytes.size = width) →
      ∀ part ∈ parts, part.size = width := by
  intro element elements
  -- Transport the common declared width from element encodings to the collected parts.
  induction elements with
  | nil => intro parts _ _ wrote _ part member; simp_all [serializeEach]
  | cons value values ih =>
    intro parts width fixed wrote widths part member
    cases head : serialize element value <;> cases tail : serializeEach element values <;>
      simp [serializeEach, head, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] at wrote
    subst wrote
    -- The selected part is either the first successful encoding or belongs to the remaining parts.
    rcases List.mem_cons.mp member with rfl | later
    · exact widths value (by simp) part head
    · exact ih _ width fixed tail (fun v m => widths v (List.mem_cons_of_mem _ m)) part later

/-- Decoding a sequence's parts gives back the elements, once every one reads back. -/
theorem deserializeEach_reads_back :
    ∀ (element : Desc) (elements : List Value) (parts : List Bytes),
      serializeEach element elements = .ok parts →
      (∀ value ∈ elements, ∀ bytes, serialize element value = .ok bytes →
        deserialize element bytes = .ok value) →
      deserializeEach element parts = .ok elements := by
  intro element elements
  -- Use the per-element round trip in the same order that the encoder collected the parts.
  induction elements with
  | nil => intro parts wrote _; simp_all [serializeEach, deserializeEach]
  | cons value values ih =>
    intro parts wrote reads
    cases head : serialize element value <;> cases tail : serializeEach element values <;>
      simp [serializeEach, head, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] at wrote
    subst wrote
    -- Combine the first recovered value with the recursively recovered sequence.
    simp only [deserializeEach, reads value (by simp) _ head,
      ih _ tail (fun v m => reads v (List.mem_cons_of_mem _ m)), Bind.bind, Except.bind]
    rfl

/--
A struct reads back whatever it wrote, and is as wide as its fields declare.

Both struct shapes encode and decode the same way, so this covers each of them.
-/
theorem recovered_struct (fields : List Desc) (values : List Value)
    (_paired : fields.length = values.length)
    (facts : ∀ pair ∈ fields.zip values, Recovered pair.1 pair.2) :
    (∀ bytes, serializeStruct fields values = .ok bytes →
      ∃ parts, structSlices fields bytes = .ok parts
        ∧ deserializeFields fields parts = .ok values)
    ∧ (∀ width bytes, Desc.fieldsFixedSize fields = some width →
      serializeStruct fields values = .ok bytes → bytes.size = width) := by
  -- Both halves start from the parts the fields encoded to.
  have parts_of : ∀ bytes, serializeStruct fields values = .ok bytes →
      ∃ parts, serializeFields fields values = .ok parts
        ∧ assemble (fields.map Desc.isFixed) parts = .ok bytes := by
    intro bytes wrote
    simp only [serializeStruct] at wrote
    cases encoded : serializeFields fields values <;> rw [encoded] at wrote
    · simp [Bind.bind, Except.bind] at wrote
    · exact ⟨_, rfl, wrote⟩
  refine ⟨?_, ?_⟩
  · intro bytes wrote
    obtain ⟨parts, encoded, assembled⟩ := parts_of bytes wrote
    -- Count preservation and fixed-field widths justify reconstructing the original header boundaries.
    have lengths := serializeFields_length fields values parts encoded
    have partWidths := serializeFields_widths fields values parts encoded
      (fun pair member => (facts pair member).2)
    have sliced := structSlices_assemble fields parts lengths partWidths
      (assemble_nameable (fields.map Desc.isFixed) parts bytes assembled)
    rw [assembled] at sliced
    exact ⟨parts, sliced, deserializeFields_reads_back fields values parts encoded
      (fun pair member => (facts pair member).1)⟩
  · intro width bytes fixed wrote
    obtain ⟨parts, encoded, assembled⟩ := parts_of bytes wrote
    have lengths := serializeFields_length fields values parts encoded
    have partWidths := serializeFields_widths fields values parts encoded
      (fun pair member => (facts pair member).2)
    -- When every field is fixed-size, all bytes belong to the header and the body contributes zero.
    obtain ⟨headIs, bodyIs⟩ :=
      fieldsFixedSize_headWidth fields parts width lengths partWidths fixed
    have shape : (fields.map Desc.isFixed).zip parts = slotsOf fields parts := rfl
    rw [assemble_size _ _ _ assembled, shape, headIs, bodyIs]
    omega

/-- A successfully encoded composite fits the four-byte offset budget. -/
theorem serializeSequence_size_lt {element : Desc} {elements : List Value} {bytes : Bytes}
    (wrote : serializeSequence element elements = .ok bytes) :
    bytes.size < 2 ^ (8 * bytesPerOffset) := by
  -- Sequence assembly checks the combined size after encoding its elements.
  unfold serializeSequence at wrote
  obtain ⟨parts, -, assembled⟩ := checksPassed wrote
  rw [assemble_size _ _ _ assembled]
  exact assemble_nameable _ _ _ assembled

/--
A sequence of fixed elements encodes to its elements laid end to end.

All three sequence shapes encode the same way, so this covers each of them.
-/
theorem recovered_sequence (element : Desc) (elements : List Value) (width : Nat)
    (fixed : element.fixedSize = some width)
    (facts : ∀ value ∈ elements, Recovered element value) :
    ∀ bytes, serializeSequence element elements = .ok bytes →
      ∃ parts, parts.length = elements.length ∧ (∀ part ∈ parts, part.size = width)
        ∧ bytes = concatParts parts ∧ deserializeEach element parts = .ok elements := by
  intro bytes wrote
  simp only [serializeSequence] at wrote
  -- A successful sequence result includes successful encodings of every element.
  cases encoded : serializeEach element elements with
  | error _ => simp [encoded, Bind.bind, Except.bind] at wrote
  | ok parts =>
    -- The element has a width, so every part is written in place.
    simp only [encoded, show element.isFixed = true by simp [Desc.isFixed, fixed]] at wrote
    exact ⟨parts, serializeEach_length element elements parts encoded,
      serializeEach_widths element elements parts width fixed encoded
        (fun value member bytes wrote => (facts value member).2 width bytes fixed wrote),
      assemble_inline parts bytes wrote,
      deserializeEach_reads_back element elements parts encoded
        (fun value member => (facts value member).1)⟩

/--
A sequence of variable elements encodes to its offset table and then its bodies.

All three sequence shapes encode the same way, so this covers each of them.
-/
theorem recovered_sequence_offset (element : Desc) (elements : List Value)
    (varying : element.fixedSize = none)
    (facts : ∀ value ∈ elements, Recovered element value) :
    ∀ bytes, serializeSequence element elements = .ok bytes →
      ∃ parts, parts.length = elements.length
        ∧ bytes = headOf (parts.length * bytesPerOffset) (offsetSlots parts) ++ concatParts parts
        ∧ parts.length * bytesPerOffset + bodyWidth (offsetSlots parts)
            < 2 ^ (8 * bytesPerOffset)
        ∧ deserializeEach element parts = .ok elements := by
  intro bytes wrote
  simp only [serializeSequence] at wrote
  -- Recover the element parts before interpreting their outer offset table.
  cases encoded : serializeEach element elements with
  | error _ => simp [encoded, Bind.bind, Except.bind] at wrote
  | ok parts =>
    -- The element has no width, so every one is reached through an offset.
    simp only [encoded, show element.isFixed = false by simp [Desc.isFixed, varying]] at wrote
    -- The successful assembly bound covers the table and all payloads together.
    have nameable := assemble_nameable (parts.map fun _ => false) parts bytes wrote
    rw [show (parts.map fun _ => false).zip parts = offsetSlots parts from rfl,
      headWidth_offset] at nameable
    exact ⟨parts, serializeEach_length element elements parts encoded,
      assemble_offset parts bytes wrote, nameable,
      deserializeEach_reads_back element elements parts encoded
        (fun value member => (facts value member).1)⟩

end EthLib.Serialization.Ssz
