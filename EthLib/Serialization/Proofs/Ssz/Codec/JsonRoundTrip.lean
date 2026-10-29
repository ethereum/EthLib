import EthLib.Serialization.Proofs.Ssz.Codec.JsonLaws

/-! A JSON document written for a value reads back as that value, at every shape. -/

namespace EthLib.Serialization.Ssz

open Lean

/-- Whether the mapping reads back every value of a shape that it writes. -/
def Rewrites (shape : Desc) : Prop :=
  ∀ (spelling : Spelling) (value : Value) (document : Json),
    Fits shape value → jsonOf shape spelling value = .ok document →
    valueOf shape spelling document = .ok value

/-- One byte on the front of a run gives one value on the front of the elements. -/
theorem byteElements_cons (byte : UInt8) (data : Bytes) :
    byteElements (#[byte] ++ data) = .uint byte.toNat :: byteElements data := by
  simp [byteElements]

/-- A run of one-byte values is recovered from the bytes it wrote. -/
theorem byteElements_byteRun : ∀ (values : List Value) (data : Bytes),
    byteRun values = .ok data → byteElements data = values
  | [], data, wrote => by simp_all [byteRun, byteElements]
  | .uint n :: rest, data, wrote => by
    -- A small value writes one byte, and that byte reads back as the same value.
    cases run : byteRun rest <;> by_cases wide : 256 ≤ n <;>
      simp [byteRun, run, wide, Bind.bind, Except.bind, pure, Except.pure] at wrote
    subst wrote
    rw [byteElements_cons, byteElements_byteRun rest _ run]
    simp
    omega
  | .bool _ :: _, _, wrote | .bytes _ :: _, _, wrote | .bits _ :: _, _, wrote
  | .seq _ :: _, _, wrote | .union _ _ :: _, _, wrote => by simp [byteRun] at wrote

/-- Each entry of a sequence document reads back as the element it was written from. -/
theorem valueOfEntries_jsonOfEach (element : Desc) (spelling : Spelling)
    (back : ∀ (value : Value) (document : Json), Fits element value →
      jsonOf element spelling value = .ok document →
        valueOf element spelling document = .ok value) :
    ∀ (values : List Value) (documents : List Json),
      (∀ value ∈ values, Fits element value) →
      jsonOfEach element spelling values = .ok documents →
      valueOfEntries element spelling documents = .ok values
  | [], documents, _, wrote => by simp_all [jsonOfEach, valueOfEntries]
  | value :: rest, documents, fitted, wrote => by
    rw [jsonOfEach] at wrote
    cases head : jsonOf element spelling value <;> cases tail : jsonOfEach element spelling rest <;>
      simp [head, tail, Bind.bind, Except.bind, pure, Except.pure] at wrote
    subst wrote
    rw [valueOfEntries, back value _ (fitted value (by simp)) head,
      valueOfEntries_jsonOfEach element spelling back rest _
        (fun v member => fitted v (by simp [member])) tail]
    rfl

/-- Two lists that hold an entry at one position hold their pair there once zipped. -/
theorem zip_getElem? {α β : Type} :
    ∀ (left : List α) (right : List β) (offset : Nat) (a : α) (b : β),
      left[offset]? = some a → right[offset]? = some b →
      (left.zip right)[offset]? = some (a, b) := by
  -- Both lists hold an entry there, so the zipped list holds their pair.
  intros
  simp_all [List.getElem?_zip_eq_some]

/-- Distinct names stay distinct once paired with what they hold. -/
theorem zip_pairwise {α β : Type} (right : List β) :
    ∀ (left : List α), left.Nodup → (left.zip right).Pairwise fun x y => x.1 ≠ y.1
  | [], _ => by simp
  | a :: rest, distinct => by
    cases right with
    | nil => simp
    | cons b others =>
      rw [List.nodup_cons] at distinct
      refine List.Pairwise.cons ?_ (zip_pairwise others rest distinct.2)
      intro pair member same
      exact distinct.1 ((show a = pair.1 from same) ▸ (List.of_mem_zip member).1)

/-- A declaration that reported no repeated name has none. -/
theorem nodup_of_firstDuplicate {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (items : List α), firstDuplicate items = none → items.Nodup
  | [], _ => by simp
  | item :: rest, none? => by
    rw [firstDuplicate] at none?
    split at none?
    · contradiction
    · next fresh => exact List.nodup_cons.mpr ⟨by simpa using fresh, nodup_of_firstDuplicate rest none?⟩

/-- The part written under one name is read back under that name. -/
theorem getObjVal?_zip {names : List String} {parts : List Json} (distinct : names.Nodup)
    {offset : Nat} {name : String} {part : Json}
    (named : names[offset]? = some name) (held : parts[offset]? = some part) :
    (Json.mkObj (names.zip parts)).getObjVal? name = .ok part :=
  getObjVal?_mkObj (zip_pairwise parts names distinct)
    (List.mem_of_getElem? (zip_getElem? names parts offset name part named held))

/--
Each field of a struct reads back as the value it was written from.

What the object yields at each position is a hypothesis, so only the recursion over the
fields is proved here.
-/
theorem valueOfFields_jsonOfFields (names : List String) (document : Json) (spelling : Spelling) :
    ∀ (fields : List Desc) (values : List Value) (documents : List Json) (position : Nat),
      (∀ pair ∈ fields.zip values, Rewrites pair.1) →
      (∀ pair ∈ fields.zip values, Fits pair.1 pair.2) →
      jsonOfFields fields spelling position values = .ok documents →
      (∀ (offset : Nat) (part : Json), documents[offset]? = some part →
        document.getObjVal? (names.getD (position + offset) "") = .ok part) →
      valueOfFields fields names spelling position document = .ok values
  | [], [], documents, _, _, _, wrote, _ => by simp_all [jsonOfFields, valueOfFields]
  | [], _ :: _, _, _, _, _, wrote, _ | _ :: _, [], _, _, _, _, wrote, _ => by
    simp [jsonOfFields] at wrote
  | field :: fields, value :: values, documents, position, rewrites, fitted, wrote, reads => by
    rw [jsonOfFields] at wrote
    cases head : jsonOf field (spelling.part position) value <;>
      cases tail : jsonOfFields fields spelling (position + 1) values <;>
      simp [head, tail, Bind.bind, Except.bind, pure, Except.pure] at wrote
    subst wrote
    rename_i first others
    have here : document.getObjVal? (names.getD position "") = .ok first := by
      simpa using reads 0 first (by simp)
    have inner : valueOf field (spelling.part position) first = .ok value :=
      rewrites (field, value) (by simp) (spelling.part position) value first
        (fitted (field, value) (by simp)) head
    have shorter : valueOfFields fields names spelling (position + 1) document = .ok values :=
      valueOfFields_jsonOfFields names document spelling fields values others (position + 1)
        (fun pair member => rewrites pair (by simp [member]))
        (fun pair member => fitted pair (by simp [member])) tail
        (fun offset part held => by
          simpa [Nat.add_assoc, Nat.add_comm 1 offset] using
            reads (offset + 1) part (by simpa using held))
    rw [valueOfFields, here]
    simp only [Except.toOption, Bind.bind, Except.bind, pure, Except.pure, inner, shorter]

/-- The option a selector names is the one the reader walks to. -/
theorem valueOfOption_found (spelling : Spelling) (payload : Json) (option : Desc)
    (value : Value) :
    ∀ (selectors : List Nat) (options : List Desc) (start selector slot : Nat),
      selectors.findIdx? (· == selector) = some slot →
      lookupOption selectors options selector = .ok option →
      valueOf option (spelling.part (start + slot)) payload = .ok value →
      valueOfOption selectors options spelling start selector payload
        = .ok (.union selector value)
  | [], _, _, _, _, found, _, _ => by simp at found
  | _ :: _, [], _, _, _, _, named, _ => by simp [lookupOption] at named
  | chosen :: selectors, first :: options, start, selector, slot, found, named, inner => by
    rw [lookupOption] at named
    by_cases here : chosen == selector
    · rw [ite_eq_left here] at named
      simp only [Except.ok.injEq] at named
      subst named
      have zero : slot = 0 := by
        rw [List.findIdx?_cons, ite_eq_left (by simpa using here)] at found
        simpa using found.symm
      rw [valueOfOption, ite_eq_left here]
      simp only [Bind.bind, Except.bind, pure, Except.pure]
      rw [show start + slot = start from by omega] at inner
      rw [inner]
    · rw [ite_eq_right here] at named
      obtain ⟨earlier, place, split⟩ : ∃ earlier, selectors.findIdx? (· == selector) = some earlier
          ∧ slot = earlier + 1 := by
        rw [List.findIdx?_cons, ite_eq_right (by simpa using here)] at found
        obtain ⟨earlier, place, plus⟩ := Option.map_eq_some_iff.mp found
        exact ⟨earlier, place, by omega⟩
      rw [valueOfOption, ite_eq_right here]
      refine valueOfOption_found spelling payload option value selectors options
        (start + 1) selector earlier place named ?_
      rw [show start + 1 + earlier = start + slot from by omega]
      exact inner

/-- A sequence document reads back as the elements it was written from. -/
theorem valueOfSequence_jsonOfSequence (element : Desc) (spelling : Spelling)
    (back : Rewrites element) (elements : List Value) (document : Json)
    (fitted : ∀ value ∈ elements, Fits element value)
    (wrote : jsonOfSequence element spelling elements = .ok document) :
    valueOfSequence element spelling document = .ok elements := by
  rw [jsonOfSequence] at wrote
  by_cases alias? : spelling.isByte = true
  · rw [ite_eq_left alias?] at wrote
    cases run : byteRun elements <;> simp [run, Bind.bind, Except.bind, pure, Except.pure] at wrote
    subst wrote
    rw [valueOfSequence, ite_eq_left alias?]
    simp [collectionHex, ofHex_toHex, byteElements_byteRun elements _ run,
      Bind.bind, Except.bind, pure, Except.pure]
    simp
  · rw [ite_eq_right alias?] at wrote
    cases each : jsonOfEach element spelling elements <;>
      simp [each, Bind.bind, Except.bind, pure, Except.pure] at wrote
    subst wrote
    rw [valueOfSequence, ite_eq_right alias?]
    simpa using valueOfEntries_jsonOfEach element spelling (fun v d => back spelling v d)
      elements _ fitted each

/-- A struct writes one document per value it holds. -/
theorem jsonOfFields_length (spelling : Spelling) :
    ∀ (fields : List Desc) (values : List Value) (position : Nat) (documents : List Json),
      jsonOfFields fields spelling position values = .ok documents →
      documents.length = values.length
  | [], [], _, documents, wrote => by simp_all [jsonOfFields]
  | [], _ :: _, _, _, wrote | _ :: _, [], _, _, wrote => by simp [jsonOfFields] at wrote
  | field :: fields, value :: values, position, documents, wrote => by
    rw [jsonOfFields] at wrote
    cases head : jsonOf field (spelling.part position) value <;>
      cases tail : jsonOfFields fields spelling (position + 1) values <;>
      simp [head, tail, Bind.bind, Except.bind, pure, Except.pure] at wrote
    simp [← wrote, jsonOfFields_length spelling fields values (position + 1) _ tail]

/-- A written struct carries no name it did not declare. -/
theorem find?_undeclared (names : List String) (documents : List Json) :
    (objectNames (Json.mkObj (names.zip documents))).find?
      (fun name => !names.contains name) = none := by
  rw [List.find?_eq_none]
  intro name member declared
  obtain ⟨pair, member, named⟩ := List.mem_map.mp (objectNames_mkObj member)
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_eq_mem,
    decide_eq_false_iff_not] at declared
  exact declared (named ▸ (List.of_mem_zip member).1)

/-- A struct object reads back as the values it was written from. -/
theorem valueOfFields_object {names : List String} {fields : List Desc} {values : List Value}
    {spelling : Spelling} {documents : List Json}
    (distinct : names.Nodup) (counted : names.length = fields.length)
    (paired : fields.length = values.length)
    (rewrites : ∀ pair ∈ fields.zip values, Rewrites pair.1)
    (fitted : ∀ pair ∈ fields.zip values, Fits pair.1 pair.2)
    (wrote : jsonOfFields fields spelling 0 values = .ok documents) :
    valueOfFields fields names spelling 0 (Json.mkObj (names.zip documents)) = .ok values := by
  refine valueOfFields_jsonOfFields names _ spelling fields values documents 0
    rewrites fitted wrote ?_
  intro offset part held
  have inside : offset < names.length := by
    have := (List.getElem?_eq_some_iff.mp held).1
    have := jsonOfFields_length spelling fields values 0 documents wrote
    omega
  have named : names[offset]? = some (names.getD offset "") := by
    simp [List.getElem?_eq_getElem inside, List.getD]
  simpa using getObjVal?_zip distinct named held

/-- A selector that names an option is found at a position among the selectors. -/
theorem findIdx?_of_lookupOption {selectors : List Nat} {options : List Desc} {selector : Nat}
    {option : Desc} (named : lookupOption selectors options selector = .ok option) :
    ∃ slot, selectors.findIdx? (· == selector) = some slot := by
  cases place : selectors.findIdx? (· == selector) with
  | some slot => exact ⟨slot, rfl⟩
  | none =>
    rw [List.findIdx?_eq_none_iff] at place
    exact absurd (place selector (lookupOption_selector _ _ _ _ named)) (by simp)

/-- A union object reads back as the value it was written from, under its own selector. -/
theorem valueOf_union {selectors : List Nat} {options : List Desc} {spelling : Spelling}
    {selector : Nat} {option : Desc} {data : Value} {payload : Json}
    (named : lookupOption selectors options selector = .ok option) (back : Rewrites option)
    (fitted : Fits option data)
    (wrote : jsonOf option (spelling.part ((selectors.findIdx? (· == selector)).getD 0)) data
      = .ok payload) :
    valueOf (.compatibleUnion selectors options) spelling
        (Json.mkObj [("selector", decimal selector), ("data", payload)])
      = .ok (.union selector data) := by
  obtain ⟨slot, place⟩ := findIdx?_of_lookupOption named
  rw [place] at wrote
  have names : objectNames (Json.mkObj [("selector", decimal selector), ("data", payload)])
      = ["data", "selector"] := by rfl
  have carried : (Json.mkObj [("selector", decimal selector), ("data", payload)]).getObjVal? "data"
      = .ok payload := getObjVal?_mkObj (by simp) (by simp)
  have tagged :
      (Json.mkObj [("selector", decimal selector), ("data", payload)]).getObjVal? "selector"
      = .ok (decimal selector) := getObjVal?_mkObj (by simp) (by simp)
  have inner : valueOf option (spelling.part (0 + slot)) payload = .ok data :=
    back _ data payload fitted (by simpa using wrote)
  rw [Json.mkObj, valueOf]
  simp only [Json.mkObj] at names tagged carried
  simp only [names, List.isEmpty_cons, Bool.false_eq_true, ite_false, tagged, carried,
    Except.toOption, Bind.bind, Except.bind, readNat_decimal]
  exact valueOfOption_found spelling payload option data selectors options 0 selector slot
    place named inner

/-- What the reader checks and reads on a struct object, shared by both struct shapes. -/
theorem valueOf_struct {names : List String} {fields : List Desc} {values : List Value}
    {spelling : Spelling} {documents : List Json}
    (rewrites : ∀ field ∈ fields, Rewrites field)
    (distinct : names.Nodup) (counted : names.length = fields.length)
    (paired : fields.length = values.length)
    (fitted : ∀ pair ∈ fields.zip values, Fits pair.1 pair.2)
    (wrote : jsonOfFields fields spelling 0 values = .ok documents) :
    (objectNames (Json.mkObj (names.zip documents))).find?
        (fun name => !names.contains name) = none
      ∧ valueOfFields fields names spelling 0 (Json.mkObj (names.zip documents)) = .ok values :=
  ⟨find?_undeclared names documents,
    valueOfFields_object distinct counted paired
      (fun pair member => rewrites pair.1 (List.of_mem_zip member).1) fitted wrote⟩

/--
A document the mapping wrote for a value of a real type reads back as that value.

Every shape of the universe is covered, with nothing left to check first.
-/
theorem valueOf_jsonOf : ∀ (shape : Desc), shape.wellFormed = .ok () → Rewrites shape := by
  intro shape
  induction shape using Desc.rec
    (motive_2 := fun fields => Desc.allWellFormed fields = .ok () →
      ∀ field ∈ fields, Rewrites field) with
  | bool =>
    intro _ _ _ _ fitted wrote
    cases fitted
    exact valueOf_jsonOf_bool wrote
  | uint width =>
    intro _ _ _ _ fitted wrote
    cases fitted with
    | uint bound => exact valueOf_jsonOf_uint bound wrote
  | byteVector length =>
    intro _ _ _ _ fitted wrote
    cases fitted with
    | byteVector exact => exact valueOf_jsonOf_byteVector exact wrote
  | byteList limit =>
    intro _ _ _ _ fitted wrote
    cases fitted with
    | byteList within => exact valueOf_jsonOf_byteList within wrote
  | bitVector length =>
    intro sound _ _ _ fitted wrote
    cases fitted with
    | bitVector exact =>
      subst exact
      exact valueOf_jsonOf_bitVector sound (.bitVector rfl) wrote
  | bitList limit =>
    intro sound _ _ _ fitted wrote
    cases fitted with
    | bitList within => exact valueOf_jsonOf_bitList within sound (.bitList within) wrote
  | progressiveBitList limit =>
    intro sound _ _ _ fitted wrote
    cases fitted with
    | progressiveBitList within =>
      exact valueOf_jsonOf_progressiveBitList within sound (.progressiveBitList within) wrote
  | vector element length ih =>
    intro sound spelling _ document fitted wrote
    cases fitted with
    | vector count each =>
      rw [jsonOf, ite_eq_left (by simp [count])] at wrote
      rw [valueOf, valueOfSequence_jsonOfSequence element _ (ih (wellFormed_vector sound)) _
        document each wrote]
      simp [count, Bind.bind, Except.bind]
      rfl
  | list element limit ih =>
    intro sound spelling _ document fitted wrote
    cases fitted with
    | list within each =>
      rw [jsonOf, ite_eq_left within] at wrote
      rw [valueOf, valueOfSequence_jsonOfSequence element _ (ih (wellFormed_list sound)) _
        document each wrote]
      simp [Nat.not_lt.mpr within, Bind.bind, Except.bind]
      rfl
  | progressiveList element limit ih =>
    intro sound spelling _ document fitted wrote
    cases fitted with
    | progressiveList within each =>
      rw [jsonOf] at wrote
      simp only [boundCheck_of_withinBound limit _ within, Bind.bind, Except.bind] at wrote
      rw [valueOf, valueOfSequence_jsonOfSequence element _ (ih (wellFormed_progressiveList sound))
        _ document each wrote]
      cases limit with
      | none => simp [Bind.bind, Except.bind]; rfl
      | some bound =>
        simp only [withinBound, decide_eq_true_eq] at within
        simp [Nat.not_lt.mpr within, Bind.bind, Except.bind]
        rfl
  | container names fields ih =>
    intro sound spelling value document fitted wrote
    cases fitted with
    | @container _ _ values paired each =>
      obtain ⟨counted, once⟩ := wellFormed_container_names sound
      rw [jsonOf] at wrote
      cases parts : jsonOfFields fields spelling 0 values <;>
        simp only [parts, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq,
          reduceCtorEq] at wrote
      subst wrote
      obtain ⟨undeclared, read⟩ := valueOf_struct (ih (wellFormed_container sound))
        (nodup_of_firstDuplicate names once) counted paired each parts
      rw [Json.mkObj, valueOf]
      simp only [Json.mkObj] at undeclared read
      simp only [undeclared, read, Bind.bind, Except.bind]
      rfl
  | progressiveContainer active names fields ih =>
    intro sound spelling value document fitted wrote
    cases fitted with
    | @progressiveContainer _ _ _ values paired each =>
      obtain ⟨counted, once⟩ := wellFormed_progressiveContainer_names sound
      rw [jsonOf] at wrote
      cases parts : jsonOfFields fields spelling 0 values <;>
        simp only [parts, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq,
          reduceCtorEq] at wrote
      subst wrote
      obtain ⟨undeclared, read⟩ := valueOf_struct (ih (wellFormed_progressiveContainer sound))
        (nodup_of_firstDuplicate names once) counted paired each parts
      rw [Json.mkObj, valueOf]
      simp only [Json.mkObj] at undeclared read
      simp only [undeclared, read, Bind.bind, Except.bind]
      rfl
  | compatibleUnion selectors options ih =>
    intro sound spelling value document fitted wrote
    cases fitted with
    | @compatibleUnion _ _ selector option data bounded named inner =>
      rw [jsonOf, named] at wrote
      cases payload : jsonOf option
          (spelling.part ((selectors.findIdx? (· == selector)).getD 0)) data <;>
        simp only [payload, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq,
          reduceCtorEq] at wrote
      subst wrote
      exact valueOf_union named (ih (wellFormed_union sound) _ (lookupOption_mem _ _ _ _ named))
        inner payload
  | nil =>
    rename_i _ field member
    simp at member
  | cons field fields ih ihRest =>
    rename_i sound target member
    rcases List.mem_cons.mp member with here | later
    · subst target
      exact ih (allWellFormed_mem _ sound field List.mem_cons_self)
    · exact ihRest (allWellFormed_tail sound) target later

end EthLib.Serialization.Ssz
