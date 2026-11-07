module

public import EthLib.Serialization.Ssz.Typed.Container
public import EthLib.Serialization.Proofs.Ssz.Typed.Class
public import EthLib.Serialization.Proofs.Ssz.Codec.RootDomain
public import EthLib.Serialization.Proofs.Ssz.Codec.Summary
public import EthLib.Serialization.Proofs.Ssz.Typed.StructBytes

/-!
# Proofs: typed SSZ containers are lawful

The fields of a container convert one by one, so their laws follow from those of each field.

A structure is then lawful when it converts to and from the tuple of its fields without loss.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open SszType SszFields

/-- The laws of the fields of a container, as those of a typed value hold for one field. -/
class LawfulSszFields (β : Type) [SszFields β] : Prop where
  /-- Every field type is well formed. -/
  allWellFormed : Desc.allWellFormed (descs β) = .ok ()
  /-- Every field stands for a value that its own type admits, one value for each type. -/
  fits : ∀ b : β, (descs β).length = (toValues b).length ∧
    ∀ pair ∈ (descs β).zip (toValues b), Fits pair.1 pair.2
  /-- Reading back untyped fields gives the typed fields they came from. -/
  ofValues_toValues : ∀ b : β, ofValues (toValues b) = .ok b
  /-- Untyped fields that read back are the ones their typed fields stand for. -/
  toValues_of_ofValues : ∀ {values : List Value} {b : β}, ofValues values = .ok b →
    toValues b = values
  /-- The roots of the fields are the roots of their untyped values. -/
  roots_eq : ∀ b : β,
    roots b = ((descs β).zip (toValues b)).mapM fun field => Ssz.hashTreeRoot field.1 field.2
  /-- The fields never refuse untyped values that their types admit, one value for each type. -/
  ofValues_ne_error : ∀ {values : List Value} {fault : Err}, (descs β).length = values.length →
    (∀ pair ∈ (descs β).zip values, Fits pair.1 pair.2) → ofValues (β := β) values ≠ .error fault
  /-- The bytes of the fields are the bytes of their untyped values. -/
  encodes_eq : ∀ b : β,
    encodes b = (fun parts => parts.map ByteArray.mk) <$> serializeFields (descs β) (toValues b)
  /-- Decoding the fields written in place refuses what the untyped check of them refuses. -/
  decodeSlots_check : ∀ slots : List ByteSlot,
    (fun _ => ()) <$> decodeSlots (β := β) slots =
      checkInline (descs β) (slots.map ByteSlot.toSlot)
  /--
  The reader of the other fields gives the typed fields of the untyped decoding of every field.

  This holds with one slot for each field and one body for each slot behind an offset.
  -/
  decodeSlots_read : ∀ {slots : List ByteSlot} {read : List ByteArray → Except Err β}
    (bodies : List ByteArray), decodeSlots slots = .ok read →
    slots.length = (descs β).length → (byteBodyStarts slots).length = bodies.length →
    read bodies = (do ofValues (β := β) (← deserializeFields (descs β) (fillSlots slots bodies)))

/--
Decoding with a lawful type fails as the untyped decoder fails, or gives the typed value.

The untyped value always converts, since it fits its type.
-/
theorem LawfulSszType.decode_cases {α : Type} [SszType α] [LawfulSszType α] (data : ByteArray) :
    (∃ fault, Ssz.deserialize (desc α) data.data = .error fault ∧
      decode (α := α) data = .error fault) ∨
    (∃ value a, Ssz.deserialize (desc α) data.data = .ok value ∧ ofValue (α := α) value = .ok a ∧
      decode (α := α) data = .ok a) := by
  rw [LawfulSszType.decode_eq]
  cases read : Ssz.deserialize (desc α) data.data with
  | error fault => exact .inl ⟨fault, rfl, rfl⟩
  | ok value =>
    cases made : ofValue (α := α) value with
    | error fault =>
      exact absurd made (LawfulSszType.ofValue_ne_error (fits_of_deserialize _ _ _ read))
    | ok a => exact .inr ⟨value, a, rfl, made, by simp [made, bind, Except.bind]⟩

/-- Fields all written in place decode in order, so they fail where their check fails. -/
private theorem deserializeFields_of_checkInline : ∀ (fields : List Desc) (slots : List ByteSlot)
    (bodies : List ByteArray) {fault : Err}, byteBodyStarts slots = [] →
    checkInline fields (slots.map ByteSlot.toSlot) = .error fault →
    deserializeFields fields (fillSlots slots bodies) = .error fault
  | [], _, _, _, _, failed => by simp [checkInline] at failed
  | _ :: _, [], _, _, _, failed => by simp [checkInline] at failed
  | _ :: _, .body _ :: _, _, _, inline, _ => by simp [byteBodyStarts] at inline
  | field :: fields, .inline bytes :: slots, bodies, fault, inline, failed => by
    simp only [List.map_cons, ByteSlot.toSlot, checkInline] at failed
    rw [fillSlots, deserializeFields]
    cases read : Ssz.deserialize field bytes.data with
    | error other => simpa [read, bind, Except.bind] using failed
    | ok value =>
      simp only [read, bind, Except.bind] at failed ⊢
      rw [deserializeFields_of_checkInline fields slots bodies inline failed]

instance (priority := low) {α : Type} [SszType α] [LawfulSszType α] : LawfulSszFields α where
  allWellFormed := by
    simp [descs, Desc.allWellFormed, LawfulSszType.wellFormed (α := α), bind, Except.bind]
  fits a := by simpa [descs, toValues] using LawfulSszType.fits a
  ofValues_toValues a := LawfulSszType.ofValue_toValue a
  toValues_of_ofValues {values a} read := by
    match values, read with
    | [value], read => simp [toValues, LawfulSszType.toValue_of_ofValue read]
    | [], read | _ :: _ :: _, read => cases read
  roots_eq a := by simp [roots, descs, toValues, LawfulSszType.root_eq]
  ofValues_ne_error {values fault} count each := by
    match values, count, each with
    | [value], _, each =>
      exact LawfulSszType.ofValue_ne_error (each (desc α, value) (by simp [descs]))
    | [], count, _ | _ :: _ :: _, count, _ => simp [descs] at count
  encodes_eq a := by
    simp only [encodes, descs, toValues, LawfulSszType.encode_eq, serializeFields_cons,
      serializeFields_nil]
    cases Ssz.serialize (desc α) (toValue a) <;> rfl
  decodeSlots_check slots := by
    match slots with
    | .inline bytes :: _ =>
      rcases LawfulSszType.decode_cases (α := α) bytes with
        ⟨fault, read, dec⟩ | ⟨value, a, read, -, dec⟩ <;>
      simp [decodeSlots, descs, checkInline, ByteSlot.toSlot, read, dec, bind, Except.bind,
        Functor.map, Except.map, pure, Except.pure]
    | .body _ :: _ | [] =>
      simp [decodeSlots, descs, checkInline, ByteSlot.toSlot, Functor.map, Except.map]
  decodeSlots_read {slots read} bodies made count starts := by
    match slots, made, count, starts with
    | [.inline bytes], made, _, starts =>
      obtain rfl : bodies = [] := List.eq_nil_of_length_eq_zero (by simpa [byteBodyStarts] using
        starts.symm)
      rcases LawfulSszType.decode_cases (α := α) bytes with
        ⟨fault, -, dec⟩ | ⟨value, a, good, conv, dec⟩
      · simp [decodeSlots, dec, bind, Except.bind] at made
      · simp only [decodeSlots, dec, bind, Except.bind, pure, Except.pure,
          Except.ok.injEq] at made
        subst made
        simp [descs, fillSlots, deserializeFields, good, ofValues, conv, bind, Except.bind,
          pure, Except.pure]
    | [.body _], made, _, starts =>
      match bodies, starts with
      | [bytes], _ =>
        simp only [decodeSlots, Except.ok.injEq] at made
        subst made
        rcases LawfulSszType.decode_cases (α := α) bytes with
          ⟨fault, read, dec⟩ | ⟨value, a, read, conv, dec⟩
        · simp [descs, fillSlots, deserializeFields, read, dec, bind, Except.bind]
        · simp [descs, fillSlots, deserializeFields, read, dec, ofValues, conv, bind,
            Except.bind, pure, Except.pure]
      | [], starts | _ :: _ :: _, starts => simp [byteBodyStarts] at starts
    | [], _, count, _ | _ :: _ :: _, _, count, _ => simp [descs] at count

instance {α β : Type} [SszType α] [LawfulSszType α] [SszFields β] [LawfulSszFields β] :
    LawfulSszFields (α × β) where
  allWellFormed := by
    simp [descs, Desc.allWellFormed, LawfulSszType.wellFormed (α := α),
      LawfulSszFields.allWellFormed (β := β), bind, Except.bind]
  fits pair := by
    obtain ⟨count, each⟩ := LawfulSszFields.fits pair.2
    refine ⟨by simp [descs, toValues, count], ?_⟩
    simp only [descs, toValues, List.zip_cons_cons, List.mem_cons, forall_eq_or_imp]
    exact ⟨LawfulSszType.fits pair.1, each⟩
  ofValues_toValues pair := by
    simp [toValues, ofValues, LawfulSszType.ofValue_toValue, LawfulSszFields.ofValues_toValues,
      bind, Except.bind, pure, Except.pure]
  toValues_of_ofValues {values pair} read := by
    match values, read with
    | [], read => cases read
    | value :: rest, read =>
      simp only [ofValues, bind, Except.bind] at read
      cases head : ofValue (α := α) value with
      | error fault => simp [head] at read
      | ok first =>
        cases tail : ofValues (β := β) rest with
        | error fault => simp [head, tail] at read
        | ok others =>
          simp only [head, tail, pure, Except.pure, Except.ok.injEq] at read
          subst read
          simp [toValues, LawfulSszType.toValue_of_ofValue head,
            LawfulSszFields.toValues_of_ofValues tail]
  roots_eq pair := by
    simp [roots, descs, toValues, LawfulSszType.root_eq, LawfulSszFields.roots_eq (β := β)]
  ofValues_ne_error {values fault} count each := by
    match values, count, each with
    | [], count, _ => simp [descs] at count
    | value :: rest, count, each =>
      simp only [descs, List.length_cons, List.zip_cons_cons, List.mem_cons,
        forall_eq_or_imp] at count each
      cases head : ofValue (α := α) value with
      | error other => exact absurd head (LawfulSszType.ofValue_ne_error each.1)
      | ok a =>
        cases tail : ofValues (β := β) rest with
        | error other => exact absurd tail (LawfulSszFields.ofValues_ne_error (by omega) each.2)
        | ok b => simp [ofValues, head, tail, bind, Except.bind, pure, Except.pure]
  encodes_eq pair := by
    simp only [encodes, descs, toValues, LawfulSszType.encode_eq, serializeFields_cons,
      LawfulSszFields.encodes_eq (β := β)]
    cases Ssz.serialize (desc α) (toValue pair.1) <;>
      cases serializeFields (descs β) (toValues pair.2) <;> rfl
  decodeSlots_check slots := by
    match slots with
    | .inline bytes :: slots =>
      have rest := LawfulSszFields.decodeSlots_check (β := β) slots
      rcases LawfulSszType.decode_cases (α := α) bytes with
        ⟨fault, read, dec⟩ | ⟨value, a, read, -, dec⟩
      · simp [decodeSlots, descs, checkInline, ByteSlot.toSlot, read, dec, bind, Except.bind,
          Functor.map, Except.map]
      · simp only [decodeSlots, descs, List.map_cons, ByteSlot.toSlot, checkInline, read, dec,
          bind, Except.bind, ← rest]
        cases decodeSlots (β := β) slots <;> rfl
    | .body _ :: slots =>
      simp only [decodeSlots, descs, List.map_cons, ByteSlot.toSlot, checkInline,
        ← LawfulSszFields.decodeSlots_check (β := β) slots, bind, Except.bind]
      cases decodeSlots (β := β) slots <;> rfl
    | [] => simp [decodeSlots, descs, checkInline, Functor.map, Except.map]
  decodeSlots_read {slots read} bodies made count starts := by
    match slots, made, count, starts with
    | .inline bytes :: slots, made, count, starts =>
      rcases LawfulSszType.decode_cases (α := α) bytes with
        ⟨fault, -, dec⟩ | ⟨value, a, read, conv, dec⟩
      · simp [decodeSlots, dec, bind, Except.bind] at made
      cases rest : decodeSlots (β := β) slots with
      | error fault => simp [decodeSlots, dec, rest, bind, Except.bind] at made
      | ok reader =>
        simp only [decodeSlots, dec, rest, bind, Except.bind, pure, Except.pure,
          Except.ok.injEq] at made
        subst made
        have tail := LawfulSszFields.decodeSlots_read bodies rest
          (by simpa [descs] using count) (by simpa [byteBodyStarts] using starts)
        simp only [descs, fillSlots, deserializeFields, read, tail, ofValues, bind,
          Except.bind, pure, Except.pure]
        rcases deserializeFields (descs β) (fillSlots slots bodies) with _ | values
        · rfl
        · cases others : ofValues (β := β) values <;> simp [others, conv]
    | .body _ :: slots, made, count, starts =>
      cases rest : decodeSlots (β := β) slots with
      | error fault => simp [decodeSlots, rest, bind, Except.bind] at made
      | ok reader =>
        simp only [decodeSlots, rest, bind, Except.bind, pure, Except.pure,
          Except.ok.injEq] at made
        subst made
        match bodies, starts with
        | [], starts => simp [byteBodyStarts] at starts
        | bytes :: bodies, starts =>
          have tail := LawfulSszFields.decodeSlots_read bodies rest
            (by simpa [descs] using count) (by simpa [byteBodyStarts] using starts)
          rcases LawfulSszType.decode_cases (α := α) bytes with
            ⟨fault, read, dec⟩ | ⟨value, a, read, conv, dec⟩
          · simp [descs, fillSlots, deserializeFields, read, dec, bind, Except.bind]
          · simp only [descs, fillSlots, deserializeFields, read, dec, tail, ofValues,
              bind, Except.bind, pure, Except.pure]
            rcases deserializeFields (descs β) (fillSlots slots bodies) with _ | values
            · rfl
            · cases others : ofValues (β := β) values <;> simp [others, conv]
    | [], _, count, _ => simp [descs] at count

/-- Fields of well-formed types, each admitting its value, all have roots. -/
theorem fieldRoots_total : ∀ {fields : List (Desc × Value)},
    (∀ field ∈ fields, field.1.wellFormed = .ok () ∧ Fits field.1 field.2) →
    ∃ roots, fields.mapM (fun field => Ssz.hashTreeRoot field.1 field.2) = .ok roots
  | [], _ => ⟨[], rfl⟩
  | field :: fields, sound => by
    obtain ⟨root, rooted, -⟩ := Ssz.hashTreeRoot_total field.1 field.2
      (sound field (by simp)).1 (sound field (by simp)).2
    obtain ⟨roots, rest⟩ := fieldRoots_total fun other member =>
      sound other (List.mem_cons_of_mem _ member)
    exact ⟨root :: roots, by simp [List.mapM_cons, rooted, rest, bind, Except.bind, pure,
      Except.pure]⟩

/-- The fields of lawful types all have roots. -/
theorem LawfulSszFields.roots_total {β : Type} [SszFields β] [LawfulSszFields β] (b : β) :
    ∃ roots, ((descs β).zip (toValues b)).mapM
      (fun field => Ssz.hashTreeRoot field.1 field.2) = .ok roots :=
  fieldRoots_total fun field member =>
    ⟨allWellFormed_mem _ LawfulSszFields.allWellFormed _ (List.of_mem_zip member).1,
      (LawfulSszFields.fits b).2 field member⟩

/-- The bytes of a struct are the untyped bytes of its fields' values. -/
private theorem encodeStruct_eq {β : Type} [SszFields β] [LawfulSszFields β] (b : β) :
    encodeStruct b = (do return ⟨← serializeStruct (descs β) (toValues b)⟩) := by
  simp only [encodeStruct, serializeStruct, LawfulSszFields.encodes_eq]
  cases serializeFields (descs β) (toValues b) with
  | error fault => rfl
  | ok parts =>
    simp only [Functor.map, Except.map, bind, Except.bind, assembleBytes_eq]
    cases assemble ((descs β).map Desc.isFixed) parts <;> rfl

/-- The fields that a struct's bytes encode are the typed fields of their untyped decoding. -/
private theorem decodeStruct_eq {β : Type} [SszFields β] [LawfulSszFields β] (data : ByteArray) :
    decodeStruct (β := β) data =
      (do ofValues (β := β) (← deserializeStruct (descs β) data.data)) := by
  have sliced := byteStructSlots_eq (descs β) data
  rw [decodeStruct, deserializeStruct]
  cases cut : byteStructSlots (descs β) data with
  | error fault =>
    rw [cut] at sliced
    simp [← sliced, Functor.map, Except.map, bind, Except.bind]
  | ok pair =>
    obtain ⟨slots, leading⟩ := pair
    have count := byteStructSlots_length cut
    rw [cut] at sliced
    simp only [Functor.map, Except.map] at sliced
    simp only [← sliced, bind, Except.bind, structBodies_eq, ← byteBodyStarts_eq]
    have check := LawfulSszFields.decodeSlots_check (β := β) slots
    by_cases offsets : (byteBodyStarts slots).isEmpty
    · -- With no bodies the size check runs first, then each field written in place.
      simp only [offsets, ite_true, Bool.not_true]
      cases bodies : byteBodies data slots leading with
      | error fault => rfl
      | ok bodies' =>
        cases reader : decodeSlots (β := β) slots with
        | error fault =>
          rw [reader] at check
          have := deserializeFields_of_checkInline (descs β) slots bodies'
            (List.isEmpty_iff.mp offsets) check.symm
          simp [Functor.map, Except.map, this]
        | ok read =>
          simp only [Functor.map, Except.map]
          rw [LawfulSszFields.decodeSlots_read bodies' reader count (byteBodies_length bodies).symm]
          rfl
    · -- With bodies, the fields written in place run before the offsets are read.
      simp only [offsets, Bool.not_false]
      cases reader : decodeSlots (β := β) slots with
      | error fault =>
        rw [reader] at check
        simp [← check, Functor.map, Except.map]
      | ok read =>
        rw [reader] at check
        simp only [← check, Functor.map, Except.map]
        cases bodies : byteBodies data slots leading with
        | error fault => rfl
        | ok bodies' =>
          simp only
          rw [LawfulSszFields.decodeSlots_read bodies' reader count (byteBodies_length bodies).symm]
          rfl

/--
A container is lawful when its names are well formed and its two conversions undo each other.

The names must be distinct, at least one, and one for each field.
-/
theorem LawfulSszType.container {σ β : Type} [SszFields β] [LawfulSszFields β]
    {names : List String} {fields : σ → β} {build : β → σ}
    (named : names.length = (descs β).length ∧ names ≠ [] ∧ firstDuplicate names = none)
    (left : ∀ s, build (fields s) = s) (right : ∀ b, fields (build b) = b) :
    @LawfulSszType σ (SszType.container names fields build) := by
  letI := SszType.container names fields build
  obtain ⟨count, present, distinct⟩ := named
  have nonempty : descs β ≠ [] := fun empty => present (List.eq_nil_of_length_eq_zero (by
    simp [count, empty]))
  exact {
    wellFormed := by
      simp [desc, Desc.wellFormed, List.isEmpty_iff, nonempty, count, distinct,
        LawfulSszFields.allWellFormed (β := β)]
    fits := fun s => .container (LawfulSszFields.fits (fields s)).1
      (LawfulSszFields.fits (fields s)).2
    ofValue_toValue := fun s => by
      simp [toValue, ofValue, LawfulSszFields.ofValues_toValues, left, Functor.map, Except.map]
    toValue_of_ofValue := fun {value s} made => by
      cases value <;> simp only [ofValue] at made <;> try cases made
      rename_i values
      cases read : ofValues (β := β) values with
      | error fault => simp [read, Functor.map, Except.map] at made
      | ok b =>
        simp only [read, Functor.map, Except.map, Except.ok.injEq] at made
        subst made
        simp [toValue, right, LawfulSszFields.toValues_of_ofValues read]
    root_eq := fun s => by
      -- Every field has a root, and the container of those roots has the container's root.
      obtain ⟨roots, rooted⟩ := LawfulSszFields.roots_total (fields s)
      simp only [root, LawfulSszFields.roots_eq, rooted, bind, Except.bind, summaryRoot]
      exact hashTreeRoot_container_roots (LawfulSszFields.fits (fields s)).1 rooted
    ofValue_ne_error := fun {value fault} fits => by
      change Fits (.container names (descs β)) value at fits
      cases fits with
      | container paired each =>
        cases read : ofValues (β := β) _ with
        | error other => exact absurd read (LawfulSszFields.ofValues_ne_error paired each)
        | ok b => simp [ofValue, read, Functor.map, Except.map]
    encode_eq := fun s => by
      simp only [encode, encodeStruct_eq, desc, toValue, Ssz.serialize]
    decode_eq := fun data => by
      simp only [decode, decodeStruct_eq, desc, Ssz.deserialize]
      cases deserializeStruct (descs β) data.data <;> rfl }

/--
A progressive container is lawful when its layout and names are well formed.

The layout ends on a set bit, has at most 256 bits, and sets one bit for each field.

The names must be distinct, at least one, and one for each field.

The two conversions must undo each other.
-/
theorem LawfulSszType.progressiveContainer {σ β : Type} [SszFields β] [LawfulSszFields β]
    {active : List Bool} {names : List String} {fields : σ → β} {build : β → σ}
    (layout : active.getLast? = some true ∧ active.length ≤ maxActiveFields ∧
      active.count true = (descs β).length)
    (named : names.length = (descs β).length ∧ names ≠ [] ∧ firstDuplicate names = none)
    (left : ∀ s, build (fields s) = s) (right : ∀ b, fields (build b) = b) :
    @LawfulSszType σ (SszType.progressiveContainer active names fields build) := by
  letI := SszType.progressiveContainer active names fields build
  obtain ⟨last, narrow, set⟩ := layout
  obtain ⟨count, present, distinct⟩ := named
  have nonempty : descs β ≠ [] := fun empty => present (List.eq_nil_of_length_eq_zero (by
    simp [count, empty]))
  have occupied : active ≠ [] := by rintro rfl; simp at last
  exact {
    wellFormed := by
      simp [desc, Desc.wellFormed, List.isEmpty_iff, occupied, last, Nat.not_lt.mpr narrow,
        nonempty, ← set, List.count, count, distinct, LawfulSszFields.allWellFormed (β := β)]
    fits := fun s => .progressiveContainer (LawfulSszFields.fits (fields s)).1
      (LawfulSszFields.fits (fields s)).2
    ofValue_toValue := fun s => by
      simp [toValue, ofValue, LawfulSszFields.ofValues_toValues, left, Functor.map, Except.map]
    toValue_of_ofValue := fun {value s} made => by
      cases value <;> simp only [ofValue] at made <;> try cases made
      rename_i values
      cases read : ofValues (β := β) values with
      | error fault => simp [read, Functor.map, Except.map] at made
      | ok b =>
        simp only [read, Functor.map, Except.map, Except.ok.injEq] at made
        subst made
        simp [toValue, right, LawfulSszFields.toValues_of_ofValues read]
    root_eq := fun s => by
      -- Every field has a root, and the container of those roots has the container's root.
      obtain ⟨roots, rooted⟩ := LawfulSszFields.roots_total (fields s)
      simp only [root, LawfulSszFields.roots_eq, rooted, bind, Except.bind, summaryRoot]
      exact hashTreeRoot_progressiveContainer_roots (LawfulSszFields.fits (fields s)).1 rooted
    ofValue_ne_error := fun {value fault} fits => by
      change Fits (.progressiveContainer active names (descs β)) value at fits
      cases fits with
      | progressiveContainer paired each =>
        cases read : ofValues (β := β) _ with
        | error other => exact absurd read (LawfulSszFields.ofValues_ne_error paired each)
        | ok b => simp [ofValue, read, Functor.map, Except.map]
    encode_eq := fun s => by
      simp only [encode, encodeStruct_eq, desc, toValue, Ssz.serialize]
    decode_eq := fun data => by
      simp only [decode, decodeStruct_eq, desc, Ssz.deserialize]
      cases deserializeStruct (descs β) data.data <;> rfl }

end EthLib.Serialization.Ssz
