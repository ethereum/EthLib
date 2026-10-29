import EthLib.Serialization.Proofs.Ssz.Codec.Admits
import EthLib.Serialization.Proofs.Ssz.Codec.Table

/-! Mathematical encoding sizes and the offset bounds needed for successful serialization. -/

namespace EthLib.Serialization.Ssz

/-- A field contributes its bytes, plus a four-byte offset when its size can vary. -/
def fieldSize (shape : Desc) (size : Nat) : Nat :=
  -- Fixed fields live entirely in the header, while variable fields also need a four-byte body pointer.
  size + if shape.isFixed then 0 else bytesPerOffset

/--
A structural witness of encoded byte size, with every assembled sequence or container inside the offset range.

Child sizes are mathematical counts, independent of byte construction or encoder success.
Byte arrays are sequences of bytes, so they meet the same offset ceiling.
-/
inductive Representable : Desc → Value → Nat → Prop where
  /-- A boolean occupies one byte. -/
  | bool (value : Bool) : Representable .bool (.bool value) 1
  /-- An integer occupies its declared byte width. -/
  | uint (width value : Nat) : Representable (.uint width) (.uint value) width
  /-- Fixed byte arrays contribute their payload unchanged, within the offset range. -/
  | byteVector (length : Nat) (data : Bytes) (bounded : data.size < 2 ^ 32) :
      Representable (.byteVector length) (.bytes data) data.size
  /-- Bounded byte arrays contribute their payload unchanged, within the offset range. -/
  | byteList (limit : Nat) (data : Bytes) (bounded : data.size < 2 ^ 32) :
      Representable (.byteList limit) (.bytes data) data.size
  /-- Fixed bitfields round their bit count up to whole bytes. -/
  | bitVector (length : Nat) (data : Array Bool) :
      Representable (.bitVector length) (.bits data) ((data.size + 7) / 8)
  /-- Variable bitfields add a delimiter bit before rounding up. -/
  | bitList (limit : Nat) (data : Array Bool) :
      Representable (.bitList limit) (.bits data) ((data.size + 8) / 8)
  /-- Progressive bitfields use the same delimiter convention. -/
  | progressiveBitList (limit : Option Nat) (data : Array Bool) :
      Representable (.progressiveBitList limit) (.bits data) ((data.size + 8) / 8)
  /-- Each element is representable, and the vector's whole layout fits the offset range. -/
  | vector {element : Desc} {length : Nat} {values : List Value} {sizes : Value → Nat}
      (each : ∀ value ∈ values, Representable element value (sizes value))
      (bounded : (values.map fun value => fieldSize element (sizes value)).sum < 2 ^ 32) :
      Representable (.vector element length) (.seq values)
        (values.map fun value => fieldSize element (sizes value)).sum
  /-- A bounded sequence accounts for offsets only when its elements have variable width. -/
  | list {element : Desc} {limit : Nat} {values : List Value} {sizes : Value → Nat}
      (each : ∀ value ∈ values, Representable element value (sizes value))
      (bounded : (values.map fun value => fieldSize element (sizes value)).sum < 2 ^ 32) :
      Representable (.list element limit) (.seq values)
        (values.map fun value => fieldSize element (sizes value)).sum
  /-- Progressive sequences still encode their composite layout within the offset range. -/
  | progressiveList {element : Desc} {limit : Option Nat} {values : List Value}
      {sizes : Value → Nat}
      (each : ∀ value ∈ values, Representable element value (sizes value))
      (bounded : (values.map fun value => fieldSize element (sizes value)).sum < 2 ^ 32) :
      Representable (.progressiveList element limit) (.seq values)
        (values.map fun value => fieldSize element (sizes value)).sum
  /-- A struct sums the contribution of each field, including each required offset. -/
  | container {names : List String} {fields : List Desc} {values : List Value}
      {sizes : Desc → Value → Nat}
      (each : ∀ pair ∈ fields.zip values, Representable pair.1 pair.2 (sizes pair.1 pair.2))
      (bounded : ((fields.zip values).map fun (field, value) =>
        fieldSize field (sizes field value)).sum < 2 ^ 32) :
      Representable (.container names fields) (.seq values)
        ((fields.zip values).map fun (field, value) => fieldSize field (sizes field value)).sum
  /-- Progressive layout gaps occupy no serialized bytes. -/
  | progressiveContainer {active : List Bool} {names : List String} {fields : List Desc}
      {values : List Value} {sizes : Desc → Value → Nat}
      (each : ∀ pair ∈ fields.zip values, Representable pair.1 pair.2 (sizes pair.1 pair.2))
      (bounded : ((fields.zip values).map fun (field, value) =>
        fieldSize field (sizes field value)).sum < 2 ^ 32) :
      Representable (.progressiveContainer active names fields) (.seq values)
        ((fields.zip values).map fun (field, value) => fieldSize field (sizes field value)).sum
  /-- A union contributes one selector byte before the chosen option. -/
  | compatibleUnion {selectors : List Nat} {options : List Desc} {selector : Nat}
      {option : Desc} {data : Value} {size : Nat}
      (named : lookupOption selectors options selector = .ok option)
      (inner : Representable option data size) :
      Representable (.compatibleUnion selectors options) (.union selector data) (1 + size)

/-- Assembly succeeds at every layout whose measured width fits the four-byte offset range. -/
private theorem assemble_complete (inline : List Bool) (parts : List Bytes) (size : Nat)
    (measured : headWidth (inline.zip parts) + bodyWidth (inline.zip parts) = size)
    (bounded : size < 2 ^ 32) :
    ∃ bytes, assemble inline parts = .ok bytes ∧ bytes.size = size := by
  -- The header and bodies together have exactly the measured size, so the overflow guard passes.
  refine ⟨headOf (headWidth (inline.zip parts)) (inline.zip parts) ++ bodiesOf (inline.zip parts), ?_, ?_⟩
  · simp [assemble, measured, show ¬size ≥ 2 ^ (8 * bytesPerOffset) by simpa [bytesPerOffset] using Nat.not_le.mpr bounded,
      pure, Except.pure]
  · simpa only [Array.size_append, headOf_size, bodiesOf_size] using measured

/-- Measuring homogeneous slots is the sum of their individual field contributions. -/
private theorem sequence_width (element : Desc) (parts : List Bytes) :
    headWidth ((parts.map fun _ => element.isFixed).zip parts) +
      bodyWidth ((parts.map fun _ => element.isFixed).zip parts) =
      (parts.map fun part => fieldSize element part.size).sum := by
  -- Each element adds its payload, plus an offset when its width varies.
  induction parts <;> cases fixed : element.isFixed <;> simp_all [headWidth, bodyWidth, fieldSize] <;> omega

/-- Measuring struct slots is the sum of each paired field's bytes and possible offset. -/
private theorem fields_width (fields : List Desc) (parts : List Bytes) :
    headWidth ((fields.map Desc.isFixed).zip parts) + bodyWidth ((fields.map Desc.isFixed).zip parts) =
      ((fields.zip parts).map fun (field, part) => fieldSize field part.size).sum := by
  -- Pair each declared field kind with the width of its encoded payload.
  induction fields generalizing parts with
  | nil => simp [headWidth, bodyWidth]
  | cons field fields ih =>
    cases parts with
    | nil => simp [headWidth, bodyWidth]
    | cons part parts =>
      have tail := ih parts
      cases fixed : field.isFixed <;> simp [headWidth, bodyWidth, fieldSize, fixed] at tail ⊢ <;> omega

/-- Successful child encodings retain their mathematical size contributions when collected. -/
private theorem collect_each (element : Desc) (sizes : Value → Nat) :
    ∀ values,
      (∀ value ∈ values, ∃ bytes, serialize element value = .ok bytes ∧ bytes.size = sizes value) →
      ∃ parts, serializeEach element values = .ok parts ∧
        (parts.map fun part => fieldSize element part.size).sum =
          (values.map fun value => fieldSize element (sizes value)).sum := by
  intro values each
  -- Collect successful child encodings while retaining the sum of their mathematical sizes.
  induction values with
  | nil => exact ⟨[], by simp [serializeEach], rfl⟩
  | cons value values ih =>
    obtain ⟨head, encoded, headSize⟩ := each value List.mem_cons_self
    obtain ⟨tail, collected, tailSize⟩ := ih fun held member => each held (List.mem_cons_of_mem _ member)
    exact ⟨head :: tail, by simp [serializeEach, encoded, collected, Bind.bind, Except.bind, pure, Except.pure],
      by simp [headSize, tailSize]⟩

/-- An admissible sequence of sized child encodings assembles within its structural bound. -/
private theorem sequence_complete (element : Desc) (values : List Value) (sizes : Value → Nat)
    (each : ∀ value ∈ values, ∃ bytes, serialize element value = .ok bytes ∧ bytes.size = sizes value)
    (bounded : (values.map fun value => fieldSize element (sizes value)).sum < 2 ^ 32) :
    ∃ bytes, serializeSequence element values = .ok bytes ∧
      bytes.size = (values.map fun value => fieldSize element (sizes value)).sum := by
  -- Construct the child byte strings and match their measured widths to the structural count.
  obtain ⟨parts, encoded, measured⟩ := collect_each element sizes values each
  -- The structural bound now guarantees that the complete header and body can be assembled.
  obtain ⟨bytes, assembled, sized⟩ := assemble_complete
    (parts.map fun _ => element.isFixed) parts _ ((sequence_width element parts).trans measured) bounded
  exact ⟨bytes, by simp [serializeSequence, encoded, assembled, Bind.bind, Except.bind], sized⟩

/-- Collecting field encodings preserves the sum of each field's size contribution. -/
private theorem collect_fields (sizes : Desc → Value → Nat) :
    ∀ fields values, fields.length = values.length →
      (∀ pair ∈ fields.zip values, ∃ bytes,
        serialize pair.1 pair.2 = .ok bytes ∧ bytes.size = sizes pair.1 pair.2) →
      ∃ parts, serializeFields fields values = .ok parts ∧
        ((fields.zip parts).map fun (field, part) => fieldSize field part.size).sum =
          ((fields.zip values).map fun (field, value) => fieldSize field (sizes field value)).sum := by
  intro fields
  -- Equal declaration and value counts let the proof advance through both lists together.
  induction fields with
  | nil => intro values paired _; cases values <;> simp_all [serializeFields]
  | cons field fields ih =>
    intro values paired each
    cases values with
    | nil => simp at paired
    | cons value values =>
      -- The current field contributes its encoded width and any required offset.
      obtain ⟨head, encoded, headSize⟩ := each (field, value) List.mem_cons_self
      obtain ⟨tail, collected, tailSize⟩ := ih values (by simpa using paired)
        (fun pair member => each pair (List.mem_cons_of_mem _ member))
      exact ⟨head :: tail, by simp [serializeFields, encoded, collected, Bind.bind, Except.bind, pure, Except.pure],
        by simp [headSize, tailSize]⟩

/-- An admissible struct assembles when its child encodings and its total layout fit their bounds. -/
private theorem struct_complete (fields : List Desc) (values : List Value)
    (sizes : Desc → Value → Nat) (paired : fields.length = values.length)
    (each : ∀ pair ∈ fields.zip values, ∃ bytes,
      serialize pair.1 pair.2 = .ok bytes ∧ bytes.size = sizes pair.1 pair.2)
    (bounded : ((fields.zip values).map fun (field, value) =>
      fieldSize field (sizes field value)).sum < 2 ^ 32) :
    ∃ bytes, serializeStruct fields values = .ok bytes ∧
      bytes.size = ((fields.zip values).map fun (field, value) =>
        fieldSize field (sizes field value)).sum := by
  -- Collect every field payload with the exact sum predicted by the structural witness.
  obtain ⟨parts, encoded, measured⟩ := collect_fields sizes fields values paired each
  -- The shared assembly theorem turns that bounded sum into an actual encoding.
  obtain ⟨bytes, assembled, sized⟩ := assemble_complete
    (fields.map Desc.isFixed) parts _ ((fields_width fields parts).trans measured) bounded
  exact ⟨bytes, by simp [serializeStruct, encoded, assembled, Bind.bind, Except.bind], sized⟩

/-- Collected encodings witness representability and preserve the sum of child sizes. -/
private theorem each_representable (element : Desc) (sizes : Value → Nat)
    (measure : ∀ value bytes, serialize element value = .ok bytes → bytes.size = sizes value)
    (reflect : ∀ value bytes, serialize element value = .ok bytes → Representable element value bytes.size) :
    ∀ values parts, serializeEach element values = .ok parts →
      (∀ value ∈ values, Representable element value (sizes value)) ∧
      (parts.map fun part => fieldSize element part.size).sum =
        (values.map fun value => fieldSize element (sizes value)).sum := by
  intro values
  -- Reflect successful element encodings back into structural size witnesses.
  induction values with
  | nil => intro parts wrote; simp_all [serializeEach]
  | cons value values ih =>
    intro parts wrote
    -- Composite success rules out a failed element encoding.
    cases head : serialize element value <;> cases tail : serializeEach element values <;>
      simp [serializeEach, head, tail, Bind.bind, Except.bind, pure, Except.pure] at wrote
    subst parts
    -- The suffix supplies its child witnesses, and the current element adds its own.
    obtain ⟨children, counted⟩ := ih _ tail
    exact ⟨List.forall_mem_cons.mpr ⟨measure value _ head ▸ reflect value _ head, children⟩,
      by simp [measure value _ head, counted]⟩

/-- A successful sequence encoding supplies bounded mathematical child sizes. -/
private theorem sequence_representable (element : Desc) (values : List Value) (bytes : Bytes)
    (reflect : ∀ value bytes, serialize element value = .ok bytes → Representable element value bytes.size)
    (wrote : serializeSequence element values = .ok bytes) :
    ∃ sizes : Value → Nat,
      (∀ value ∈ values, Representable element value (sizes value)) ∧
      bytes.size = (values.map fun value => fieldSize element (sizes value)).sum ∧
      (values.map fun value => fieldSize element (sizes value)).sum < 2 ^ 32 := by
  -- Output sizes provide witnesses here.
  -- The representability relation itself never calls the encoder.
  let sizes := fun value => match serialize element value with
    | .ok part => part.size
    | .error _ => 0
  -- Whenever an element encoded successfully, the chosen size is its actual output length.
  have measure (value : Value) (part : Bytes) (encoded : serialize element value = .ok part) :
      part.size = sizes value := by simp [sizes, encoded]
  cases collected : serializeEach element values with
  | error fault => simp [serializeSequence, collected, Bind.bind, Except.bind] at wrote
  | ok parts =>
    simp only [serializeSequence, collected, Bind.bind, Except.bind] at wrote
    -- Recover structural witnesses for every collected child before accounting for assembly.
    obtain ⟨children, counted⟩ := each_representable element sizes measure reflect values parts collected
    have measured := (sequence_width element parts).trans counted
    refine ⟨sizes, children, (assemble_size _ _ _ wrote).trans measured, ?_⟩
    -- Successful assembly establishes the enclosing composite ceiling of 2^32 bytes.
    have bounded := assemble_nameable _ _ _ wrote
    simpa only [measured, bytesPerOffset] using bounded

/-- Successful field collection supplies representable children and their exact total contribution. -/
private theorem fields_representable (sizes : Desc → Value → Nat)
    (measure : ∀ field value bytes, serialize field value = .ok bytes → bytes.size = sizes field value) :
    ∀ fields values parts,
      (∀ pair ∈ fields.zip values, ∀ bytes,
        serialize pair.1 pair.2 = .ok bytes → Representable pair.1 pair.2 bytes.size) →
      serializeFields fields values = .ok parts →
      (∀ pair ∈ fields.zip values, Representable pair.1 pair.2 (sizes pair.1 pair.2)) ∧
      ((fields.zip parts).map fun (field, part) => fieldSize field part.size).sum =
        ((fields.zip values).map fun (field, value) => fieldSize field (sizes field value)).sum := by
  intro fields
  -- Recover child size witnesses while following each field-value pair.
  induction fields with
  | nil => intro values parts _ wrote; cases values <;> simp_all [serializeFields]
  | cons field fields ih =>
    intro values parts reflect wrote
    cases values with
    | nil => simp [serializeFields] at wrote
    | cons value values =>
      -- Any failed field encoding would contradict the assumed successful collection.
      cases head : serialize field value <;> cases tail : serializeFields fields values <;>
        simp [serializeFields, head, tail, Bind.bind, Except.bind, pure, Except.pure] at wrote
      subst parts
      -- The remaining pairs supply their witnesses, and the current pair adds its own.
      obtain ⟨children, counted⟩ := ih values _
        (fun pair member => reflect pair (List.mem_cons_of_mem _ member)) tail
      exact ⟨List.forall_mem_cons.mpr
          ⟨measure field value _ head ▸ reflect (field, value) List.mem_cons_self _ head, children⟩,
        by simp [measure field value _ head, counted]⟩

/-- A successful struct encoding supplies bounded mathematical sizes for all its fields. -/
private theorem struct_representable (fields : List Desc) (values : List Value) (bytes : Bytes)
    (reflect : ∀ pair ∈ fields.zip values, ∀ bytes,
      serialize pair.1 pair.2 = .ok bytes → Representable pair.1 pair.2 bytes.size)
    (wrote : serializeStruct fields values = .ok bytes) :
    ∃ sizes : Desc → Value → Nat,
      (∀ pair ∈ fields.zip values, Representable pair.1 pair.2 (sizes pair.1 pair.2)) ∧
      bytes.size = ((fields.zip values).map fun (field, value) => fieldSize field (sizes field value)).sum ∧
      ((fields.zip values).map fun (field, value) => fieldSize field (sizes field value)).sum < 2 ^ 32 := by
  -- Use successful output widths as witnesses without making the structural relation depend on execution.
  let sizes := fun field value => match serialize field value with
    | .ok part => part.size
    | .error _ => 0
  -- The chosen width agrees with each successful field encoding.
  have measure (field : Desc) (value : Value) (part : Bytes)
      (encoded : serialize field value = .ok part) : part.size = sizes field value := by
    simp [sizes, encoded]
  cases collected : serializeFields fields values with
  | error fault => simp [serializeStruct, collected, Bind.bind, Except.bind] at wrote
  | ok parts =>
    simp only [serializeStruct, collected, Bind.bind, Except.bind] at wrote
    -- Collect child witnesses and their exact contribution to the container.
    obtain ⟨children, counted⟩ := fields_representable sizes measure fields values parts reflect collected
    have measured := (fields_width fields parts).trans counted
    refine ⟨sizes, children, (assemble_size _ _ _ wrote).trans measured, ?_⟩
    -- The successful outer assembly enforces its own bound in addition to every child bound.
    have bounded := assemble_nameable _ _ _ wrote
    simpa only [measured, bytesPerOffset] using bounded

/-- Admissible values with structural size bounds always encode to exactly the witnessed byte count. -/
theorem Representable.serialize {shape : Desc} {value : Value} {size : Nat}
    (represented : Representable shape value size) :
    Fits shape value → ∃ bytes, serialize shape value = .ok bytes ∧ bytes.size = size := by
  -- Structural induction constructs each child encoding before its enclosing composite.
  induction represented with
  | bool value => exact fun _ => ⟨#[if value then 1 else 0], by simp [Ssz.serialize], rfl⟩
  | uint width value =>
    intro (.uint bound)
    exact ⟨uintBytes width value, by simp [Ssz.serialize, bound], uintBytes_size _ _⟩
  | byteVector length data bounded =>
    intro (.byteVector sized)
    exact ⟨data, by
      simp [Ssz.serialize, sized, bytesPerOffset, Bind.bind, Except.bind, pure, Except.pure]
      omega, rfl⟩
  | byteList limit data bounded =>
    intro (.byteList within)
    exact ⟨data, by
      simp [Ssz.serialize, Nat.not_lt.mpr within, Nat.not_le.mpr bounded, bytesPerOffset, pure,
        Except.pure], rfl⟩
  | bitVector length data =>
    intro (.bitVector sized)
    exact ⟨packBits data ((length + 7) / 8), by simp [Ssz.serialize, sized], by simp [packBits, sized]⟩
  | bitList limit data =>
    intro (.bitList within)
    exact ⟨packBitsDelimited data, by simp [Ssz.serialize, within], by simp [packBitsDelimited, packBits]⟩
  | progressiveBitList limit data =>
    intro (.progressiveBitList within)
    exact ⟨packBitsDelimited data,
      by simp [Ssz.serialize, boundCheck_of_withinBound limit _ within, Bind.bind, Except.bind,
        Pure.pure, Except.pure],
      by simp [packBitsDelimited, packBits]⟩
  -- For sequences, construct each admissible child before applying the witnessed total size bound.
  | vector each bounded ih =>
    intro (.vector counted admissible)
    obtain ⟨bytes, encoded, sized⟩ := sequence_complete _ _ _
      (fun held member => ih held member (admissible held member)) bounded
    exact ⟨bytes, by simp [Ssz.serialize, counted, encoded], sized⟩
  | list each bounded ih =>
    intro (.list within admissible)
    obtain ⟨bytes, encoded, sized⟩ := sequence_complete _ _ _
      (fun held member => ih held member (admissible held member)) bounded
    exact ⟨bytes, by simp [Ssz.serialize, within, encoded], sized⟩
  | @progressiveList _ limit _ _ each bounded ih =>
    intro (.progressiveList within admissible)
    obtain ⟨bytes, encoded, sized⟩ := sequence_complete _ _ _
      (fun held member => ih held member (admissible held member)) bounded
    exact ⟨bytes, by
      simpa only [Ssz.serialize, boundCheck_of_withinBound limit _ within, Bind.bind,
        Except.bind] using encoded, sized⟩
  -- For containers, matched field-value counts ensure that every declared field is encoded.
  | container each bounded ih =>
    intro (.container paired admissible)
    obtain ⟨bytes, encoded, sized⟩ := struct_complete _ _ _ paired
      (fun pair member => ih pair member (admissible pair member)) bounded
    exact ⟨bytes, by simpa only [Ssz.serialize] using encoded, sized⟩
  -- Inactive Merkle positions add no bytes to the serialized container.
  | progressiveContainer each bounded ih =>
    intro (.progressiveContainer paired admissible)
    obtain ⟨bytes, encoded, sized⟩ := struct_complete _ _ _ paired
      (fun pair member => ih pair member (admissible pair member)) bounded
    exact ⟨bytes, by simpa only [Ssz.serialize] using encoded, sized⟩
  | @compatibleUnion selectors options selector option data size named inner ih =>
    intro (.compatibleUnion ranged found admissible)
    -- The size witness and admissibility refer to the same uniquely selected option.
    cases Except.ok.inj (named.symm.trans found)
    obtain ⟨body, encoded, sized⟩ := ih admissible
    exact ⟨#[UInt8.ofNat selector] ++ body,
      by simp [Ssz.serialize, named, encoded, checkSelector_of_range ranged, Bind.bind, Except.bind,
        pure, Except.pure], by simp [sized]⟩

/-- Every successful encoding has a structural size witness, including bounds at all nested sequences and containers. -/
theorem representable_of_serialize (shape : Desc) (value : Value) (bytes : Bytes)
    (wrote : serialize shape value = .ok bytes) : Representable shape value bytes.size := by
  -- Work from successful execution toward a structural witness for every nested declaration.
  induction shape using Desc.rec
    (motive_2 := fun fields => ∀ field ∈ fields, ∀ value bytes,
      serialize field value = .ok bytes → Representable field value bytes.size)
    generalizing value bytes with
  | bool =>
    cases value <;> simp [Ssz.serialize] at wrote
    subst bytes
    exact .bool _
  | uint width =>
    cases value <;> simp [Ssz.serialize] at wrote
    split at wrote <;> cases wrote
    simpa only [uintBytes_size] using Representable.uint width _
  -- A byte array that encodes passed the size bound on its way out.
  | byteVector length | byteList limit =>
    cases value <;> simp [Ssz.serialize, throw, throwThe, MonadExceptOf.throw, Bind.bind,
      Except.bind, pure, Except.pure] at wrote
    repeat' split at wrote
    all_goals cases wrote
    all_goals constructor; simp only [bytesPerOffset] at *; omega
  | bitVector length =>
    cases value <;> simp [Ssz.serialize] at wrote
    split at wrote <;> cases wrote
    rename_i data sized
    simpa [packBits, show data.size = length by simpa using sized] using Representable.bitVector length data
  | bitList limit =>
    cases value <;> simp [Ssz.serialize] at wrote
    split at wrote <;> cases wrote
    simpa [packBitsDelimited, packBits] using Representable.bitList limit _
  | progressiveBitList limit =>
    cases value <;>
      simp [Ssz.serialize, Bind.bind, Except.bind, Pure.pure, Except.pure] at wrote
    split at wrote <;> cases wrote
    simpa [packBitsDelimited, packBits] using Representable.progressiveBitList limit _
  -- For composite sequences, recover child witnesses and the enclosing assembly bound.
  | vector element length ih =>
    cases value <;> simp [Ssz.serialize] at wrote
    split at wrote <;> try cases wrote
    obtain ⟨sizes, children, measured, bounded⟩ := sequence_representable element _ bytes ih wrote
    rw [measured]
    exact .vector children bounded
  | list element limit ih =>
    cases value <;> simp [Ssz.serialize] at wrote
    split at wrote <;> try cases wrote
    obtain ⟨sizes, children, measured, bounded⟩ := sequence_representable element _ bytes ih wrote
    rw [measured]
    exact .list children bounded
  | progressiveList element limit ih =>
    cases value <;> simp [Ssz.serialize, Bind.bind, Except.bind] at wrote
    split at wrote <;> try cases wrote
    obtain ⟨sizes, children, measured, bounded⟩ := sequence_representable element _ bytes ih wrote
    rw [measured]
    exact .progressiveList children bounded
  -- Each successful field encoding supplies a witness under its own declared type.
  | container names fields ih =>
    cases value <;> simp [Ssz.serialize] at wrote
    obtain ⟨sizes, children, measured, bounded⟩ := struct_representable fields _ bytes
      (fun pair member => ih pair.1 (List.of_mem_zip member).1 pair.2) wrote
    rw [measured]
    exact .container children bounded
  -- Progressive containers serialize their declared fields without reserving bytes for inactive tree positions.
  | progressiveContainer active names fields ih =>
    cases value <;> simp [Ssz.serialize] at wrote
    obtain ⟨sizes, children, measured, bounded⟩ := struct_representable fields _ bytes
      (fun pair member => ih pair.1 (List.of_mem_zip member).1 pair.2) wrote
    rw [measured]
    exact .progressiveContainer children bounded
  -- Keep the successful option lookup so the witness refers to the exact selected payload type.
  | compatibleUnion selectors options ih =>
    cases value <;> simp only [Ssz.serialize] at wrote
    all_goals try contradiction
    rename_i selector data
    cases named : lookupOption selectors options selector <;> simp [named, Bind.bind, Except.bind] at wrote
    rename_i option
    cases ranged : checkSelector selector <;> simp [ranged] at wrote
    cases encoded : serialize option data <;> simp [encoded, pure, Except.pure] at wrote
    subst bytes
    -- The selected option belongs to the declaration, so the induction hypothesis applies.
    have member := lookupOption_mem selectors options selector option named
    simpa using Representable.compatibleUnion named (ih option member data _ encoded)
  | nil => intros; contradiction
  | cons field fields ihHead ihTail =>
    rename_i held member value bytes wrote
    exact List.forall_mem_cons.mpr ⟨ihHead, ihTail⟩ held member value bytes wrote

/-- For admissible values, the structural size condition exactly characterizes successful encoding. -/
theorem representable_iff_serializes {shape : Desc} {value : Value} (fitted : Fits shape value) :
    (∃ size, Representable shape value size) ↔ ∃ bytes, serialize shape value = .ok bytes := by
  -- A structural witness builds an encoding, and an actual encoding's width is a witness.
  exact ⟨fun ⟨_, represented⟩ => (represented.serialize fitted).imp fun _ => And.left,
    fun ⟨bytes, wrote⟩ => ⟨bytes.size, representable_of_serialize shape value bytes wrote⟩⟩

end EthLib.Serialization.Ssz
