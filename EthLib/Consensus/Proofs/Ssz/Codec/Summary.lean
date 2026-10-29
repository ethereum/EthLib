import EthLib.Consensus.Proofs.Ssz.Codec.NodeWidths
import EthLib.Consensus.Proofs.Ssz.Type.Equality

/-!
Replacing nested values by their roots leaves the outer root unchanged.

The spec calls the result a summary of the original value.
-/

namespace EthLib.Consensus.Ssz

/-- A byte string exactly one node wide packs into that one node. -/
private theorem packBytes_chunk {data : Bytes} (width : data.size = bytesPerChunk) :
    packBytes data = #[data] := by
  have size : (packBytes data).size = 1 := by simp [width, bytesPerChunk]
  apply Array.ext
  · simp [size]
  · intro position inside _
    obtain rfl : position = 0 := by omega
    apply Array.ext
    · simp [packBytes_chunk_size _ _ (by omega : 0 < _), width]
    · intro byte inner _
      rw [packBytes_chunk_size _ _ (by omega)] at inner
      simpa using packBytes_get data 0 byte (by omega) inner (by omega)

/-- A complete node held as a fixed byte array is its own root. -/
theorem hashTreeRoot_chunk {data : Bytes} (width : data.size = bytesPerChunk) :
    hashTreeRoot (.byteVector bytesPerChunk) (.bytes data) = .ok data := by
  have flat : depthFor 1 = 0 := depthFor_pow 0
  simp only [hashTreeRoot, Desc.nesting, hashTreeRootAt, merkleLayout, width, bne_self_eq_false,
    Bool.false_eq_true, ite_false, Bind.bind, Except.bind, pure, Except.pure,
    MerkleLayout.packing, packBytes_chunk width, layoutChunksAt, Leaves.count]
  simp only [merkleizeBoundedUnchecked, flat, subtreeAt, padded, Array.size_singleton,
    Bind.bind, Except.bind, pure, Except.pure]
  rfl

/-- The root one leaf position contributes, a gap counting as a zero node. -/
private def slotRoot : Option (Desc × Value) → Except Err Bytes
  | none => .ok zeroChunk
  | some (shape, value) => hashTreeRoot shape value

/-- Two lists mapped to the same results give the same traversal. -/
private theorem mapM_of_map {α β : Type} {f : α → Except Err Bytes} {g : β → Except Err Bytes} :
    ∀ {left : List α} {right : List β}, left.map f = right.map g → left.mapM f = right.mapM g
  | [], [], _ => rfl
  | [], _ :: _, same | _ :: _, [], same => by simp at same
  | _ :: _, _ :: _, same => by
    simp only [List.map_cons, List.cons.injEq] at same
    simp [List.mapM_cons, same.1, mapM_of_map same.2]

/-- Nested leaves give the same nodes at any budget deep enough for them. -/
private theorem chunks_nested {budget : Nat} {slots : List (Option (Desc × Value))}
    {limit : Option Nat} {mixin : Option Bytes}
    (enough : ∀ shape value, some (shape, value) ∈ slots → shape.nesting ≤ budget) :
    layoutChunksAt budget ⟨.nested slots, limit, mixin⟩
      = (do let chunks ← slots.mapM slotRoot; return chunks.toArray) := by
  simp only [layoutChunksAt, Leaves.count, Option.getD_none, Nat.sub_zero, List.drop_zero,
    List.take_length]
  congr 1
  apply mapM_of_map
  apply List.map_congr_left
  intro slot member
  rcases slot with _ | ⟨shape, value⟩
  · rfl
  · exact hashTreeRootAt_eq_hashTreeRoot _ _ _ (enough _ _ member)

/-- A root spends one level of its budget on the layout at the top. -/
private theorem hashTreeRoot_step {shape : Desc} :
    hashTreeRoot shape = hashTreeRootAt (shape.nesting - 1 + 1) shape := by
  rw [Nat.sub_add_cancel shape.nesting_pos]
  rfl

/-- A layout that fails makes the root fail the same way. -/
private theorem hashTreeRoot_refused {shape : Desc} {value : Value} {fault : Err}
    (failed : merkleLayout shape value = .error fault) :
    hashTreeRoot shape value = .error fault := by
  simp [hashTreeRoot_step, hashTreeRootAt, failed, Bind.bind, Except.bind]

/-- Two nested layouts with the same tree shape and the same leaf roots give the same root. -/
private theorem hashTreeRoot_slots {left right : Desc} {first second : Value}
    {leftSlots rightSlots : List (Option (Desc × Value))}
    {limit : Option Nat} {mixin : Option Bytes}
    (leftLaid : merkleLayout left first = .ok ⟨.nested leftSlots, limit, mixin⟩)
    (rightLaid : merkleLayout right second = .ok ⟨.nested rightSlots, limit, mixin⟩)
    (same : leftSlots.map slotRoot = rightSlots.map slotRoot) :
    hashTreeRoot left first = hashTreeRoot right second := by
  have below {shape value} {slots} {layoutLimit layoutMixin}
      (laid : merkleLayout shape value = .ok ⟨.nested slots, layoutLimit, layoutMixin⟩) :
      layoutChunksAt (shape.nesting - 1) ⟨.nested slots, layoutLimit, layoutMixin⟩
        = (do let chunks ← slots.mapM slotRoot; return chunks.toArray) :=
    chunks_nested fun child inner member => by
      have := merkleLayout_child_nesting _ _ _ laid slots rfl child inner member
      omega
  rw [hashTreeRoot_step, hashTreeRoot_step]
  simp only [hashTreeRootAt, leftLaid, rightLaid, below leftLaid, below rightLaid,
    mapM_of_map same, Bind.bind, Except.bind]

/-- Placing fields with the same roots gives leaf positions with the same roots. -/
private theorem placeSlots_congr :
    ∀ (active : List Bool) {left right : List (Desc × Value)} {slots},
      left.map (fun pair => slotRoot (some pair)) = right.map (fun pair => slotRoot (some pair)) →
      placeSlots active left = .ok slots →
      ∃ others, placeSlots active right = .ok others ∧ slots.map slotRoot = others.map slotRoot
  | [], [], [], _, _, placed => ⟨[], rfl, by simp_all [placeSlots]⟩
  | [], _ :: _, _, _, _, placed => by simp [placeSlots] at placed
  | [], [], _ :: _, _, same, _ => by simp at same
  | false :: active, left, _, _, same, placed => by
    cases rest : placeSlots active left with
    | error => simp [placeSlots, rest, Bind.bind, Except.bind] at placed
    | ok tail =>
      obtain ⟨others, placedRight, roots⟩ := placeSlots_congr active same rest
      simp only [placeSlots, rest, placedRight, Bind.bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at placed ⊢
      simp_all [← placed, slotRoot]
  | true :: active, _ :: left, _ :: _, _, same, placed => by
    simp only [List.map_cons, List.cons.injEq] at same
    cases rest : placeSlots active left with
    | error => simp [placeSlots, rest, Bind.bind, Except.bind] at placed
    | ok tail =>
      obtain ⟨others, placedRight, roots⟩ := placeSlots_congr active same.2 rest
      simp only [placeSlots, rest, placedRight, Bind.bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at placed ⊢
      simp_all [← placed, slotRoot]
  | true :: _, [], _, _, _, placed => by simp [placeSlots] at placed
  | true :: _, _ :: _, [], _, same, _ => by simp at same

/-- Setting one entry of each of two lists sets the one entry of the list they zip to. -/
private theorem zip_set {α β : Type} :
    ∀ (left : List α) (right : List β) (position : Nat) (a : α) (b : β),
      (left.set position a).zip (right.set position b)
        = (left.zip right).set position (a, b)
  | [], _, _, _, _ => by simp
  | _ :: _, [], _, _, _ => by simp
  | _ :: _, _ :: _, 0, _, _ => by simp
  | _ :: leftRest, _ :: rightRest, position + 1, a, b => by
    simp [zip_set leftRest rightRest position a b]

/-- Replacing one entry by another with the same image leaves the image unchanged. -/
private theorem map_set_same {α β : Type} {f : α → β} {entries : List α} {position : Nat}
    {original replacement : α} (held : entries[position]? = some original)
    (agree : f replacement = f original) :
    (entries.set position replacement).map f = entries.map f := by
  apply List.ext_getElem?
  grind

/-- Replacing a field by one with the same root leaves the struct root unchanged. -/
theorem hashTreeRoot_container_congr {names : List String} {fields : List Desc}
    {values : List Value} {position : Nat} {nested replacement : Desc} {held replaced : Value}
    {root : Bytes}
    (paired : fields.length = values.length)
    (declared : fields[position]? = some nested) (carried : values[position]? = some held)
    (rooted : hashTreeRoot nested held = .ok root)
    (same : hashTreeRoot replacement replaced = .ok root) :
    hashTreeRoot (.container names (fields.set position replacement))
        (.seq (values.set position replaced))
      = hashTreeRoot (.container names fields) (.seq values) := by
  apply hashTreeRoot_slots (limit := some fields.length) (mixin := none)
    (leftSlots := ((fields.set position replacement).zip (values.set position replaced)).map some)
    (rightSlots := (fields.zip values).map some)
    (by simp [merkleLayout, paired, MerkleLayout.nesting, pure, Except.pure])
    (by simp [merkleLayout, paired, MerkleLayout.nesting, pure, Except.pure])
  rw [zip_set, List.map_set]
  exact map_set_same (original := some (nested, held))
    (by simp [List.getElem?_zip_eq_some, declared, carried]) (by simp [slotRoot, rooted, same])

/--
A field replaced by its own root gives the same struct root.

A party holding only that root computes the root a party holding the field computes.

A proof about anything inside the field therefore verifies against either value.

Deeper summaries follow by replacing inside the field first, then the field itself.
-/
theorem hashTreeRoot_summary {names : List String} {fields : List Desc} {values : List Value}
    {position : Nat} {nested : Desc} {held : Value} {root : Bytes}
    (paired : fields.length = values.length)
    (declared : fields[position]? = some nested) (carried : values[position]? = some held)
    (rooted : hashTreeRoot nested held = .ok root) :
    hashTreeRoot (.container names (fields.set position (.byteVector bytesPerChunk)))
        (.seq (values.set position (.bytes root)))
      = hashTreeRoot (.container names fields) (.seq values) :=
  hashTreeRoot_container_congr paired declared carried rooted
    (hashTreeRoot_chunk (hashTreeRoot_size _ _ _ rooted))

/-- Placing fields fails only when the layout and the fields disagree. -/
private theorem placeSlots_refused {fault : Err} :
    ∀ {active : List Bool} {fields : List (Desc × Value)},
      placeSlots active fields = .error fault → fault = .badDeclaration
  | [], [], failed => by simp [placeSlots] at failed
  | false :: active, fields, failed | true :: active, _ :: fields, failed => by
    cases rest : placeSlots active fields <;>
      simp_all [placeSlots, Bind.bind, Except.bind, pure, Except.pure]
    exact placeSlots_refused rest
  | [], _ :: _, failed | true :: _, [], failed => by simpa [placeSlots] using failed.symm

/-- Replacing a field of a progressive struct by one with the same root leaves its root unchanged. -/
theorem hashTreeRoot_progressiveContainer_congr {active : List Bool} {names : List String}
    {fields : List Desc} {values : List Value} {position : Nat} {nested replacement : Desc}
    {held replaced : Value} {root : Bytes}
    (paired : fields.length = values.length)
    (declared : fields[position]? = some nested) (carried : values[position]? = some held)
    (rooted : hashTreeRoot nested held = .ok root)
    (same : hashTreeRoot replacement replaced = .ok root) :
    hashTreeRoot (.progressiveContainer active names (fields.set position replacement))
        (.seq (values.set position replaced))
      = hashTreeRoot (.progressiveContainer active names fields) (.seq values) := by
  have roots : ((fields.set position replacement).zip (values.set position replaced)).map
      (fun pair => slotRoot (some pair)) = (fields.zip values).map (fun pair => slotRoot (some pair)) := by
    rw [zip_set]
    exact map_set_same (original := (nested, held))
      (by simp [List.getElem?_zip_eq_some, declared, carried]) (by simp [slotRoot, rooted, same])
  by_cases counted : active.countP id = fields.length
  · cases placed : placeSlots active (fields.zip values) with
    | ok slots =>
      obtain ⟨others, placedLeft, agree⟩ := placeSlots_congr active roots.symm placed
      exact hashTreeRoot_slots (leftSlots := others) (rightSlots := slots) (limit := none)
        (mixin := some (activeFieldsWord active))
        (by simp [merkleLayout, layoutSlots, paired, counted, placedLeft, MerkleLayout.nesting,
          Bind.bind, Except.bind, pure, Except.pure])
        (by simp [merkleLayout, layoutSlots, paired, counted, placed, MerkleLayout.nesting,
          Bind.bind, Except.bind, pure, Except.pure]) agree.symm
    | error fault =>
      cases placedLeft : placeSlots active
          ((fields.set position replacement).zip (values.set position replaced)) with
      | ok others =>
        obtain ⟨_, refused, _⟩ := placeSlots_congr active roots placedLeft
        simp [placed] at refused
      | error other =>
        rw [hashTreeRoot_refused (fault := other), hashTreeRoot_refused (fault := fault),
          placeSlots_refused placed, placeSlots_refused placedLeft]
        all_goals simp [merkleLayout, layoutSlots, paired, counted, placed, placedLeft,
          Bind.bind, Except.bind]
  · rw [hashTreeRoot_refused (fault := .layoutFieldCount (active.countP id) fields.length),
      hashTreeRoot_refused (fault := .layoutFieldCount (active.countP id) fields.length)]
    all_goals simp [merkleLayout, layoutSlots, paired, paired ▸ counted, Bind.bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw]

/-- A selector picks the option at the position of its first declaration. -/
private theorem lookupOption_at {selector : Nat} :
    ∀ {selectors : List Nat} {options : List Desc} {slot : Nat} {option : Desc},
      selectors.length = options.length → selectors.idxOf? selector = some slot →
      options[slot]? = some option → lookupOption selectors options selector = .ok option
  | [], _, _, _, _, indexed, _ => by simp at indexed
  | _ :: _, [], _, _, paired, _, _ => by simp at paired
  | first :: selectors, _ :: options, slot, _, paired, indexed, declared => by
    by_cases matched : first = selector
    · subst matched
      simp only [List.idxOf?_cons, beq_self_eq_true, ite_true, Option.some.injEq] at indexed
      subst indexed
      simp_all [lookupOption]
    · cases slot <;> simp_all [lookupOption, List.idxOf?_cons]
      exact lookupOption_at paired indexed declared

/--
Replacing the payload of a union by one with the same root leaves its root unchanged.

The payload is read against the option its selector names.

So the summary declares the new type in that option's place.
-/
theorem hashTreeRoot_union_congr {selectors : List Nat} {options : List Desc}
    {selector slot : Nat} {nested replacement : Desc} {held replaced : Value} {root : Bytes}
    (paired : selectors.length = options.length)
    (indexed : selectors.idxOf? selector = some slot) (declared : options[slot]? = some nested)
    (rooted : hashTreeRoot nested held = .ok root)
    (same : hashTreeRoot replacement replaced = .ok root) :
    hashTreeRoot (.compatibleUnion selectors (options.set slot replacement))
        (.union selector replaced)
      = hashTreeRoot (.compatibleUnion selectors options) (.union selector held) := by
  have chosen := lookupOption_at paired indexed declared
  have swapped := lookupOption_at (options := options.set slot replacement) (option := replacement) (by simpa using paired) indexed
    (by simp [(List.getElem?_eq_some_iff.mp declared).1])
  cases word : selectorWord selector with
  | ok mixed =>
    exact hashTreeRoot_slots (leftSlots := [some (replacement, replaced)])
      (rightSlots := [some (nested, held)]) (limit := some 1) (mixin := some mixed)
      (by simp [merkleLayout, swapped, word, MerkleLayout.nesting, Bind.bind, Except.bind, pure,
        Except.pure])
      (by simp [merkleLayout, chosen, word, MerkleLayout.nesting, Bind.bind, Except.bind, pure,
        Except.pure])
      (by simp [slotRoot, rooted, same])
  | error fault =>
    rw [hashTreeRoot_refused (fault := fault), hashTreeRoot_refused (fault := fault)]
    all_goals simp [merkleLayout, chosen, swapped, word, Bind.bind, Except.bind]

/-- Elements rooted one by one give leaves with the same roots as those roots held as nodes. -/
private theorem summary_slots {element : Desc} :
    ∀ {values : List Value} {roots : List Bytes}, values.mapM (hashTreeRoot element) = .ok roots →
      ((roots.map Value.bytes).map fun value => some (.byteVector bytesPerChunk, value)).map slotRoot
        = (values.map fun value => some (element, value)).map slotRoot ∧
      (roots.map Value.bytes).length = values.length
  | [], roots, rooted => by
    simp_all [pure, Except.pure]
  | value :: values, roots, rooted => by
    cases first : hashTreeRoot element value with
    | error => simp [first, Bind.bind, Except.bind] at rooted
    | ok root =>
      cases rest : values.mapM (hashTreeRoot element) with
      | error => simp [first, rest, Bind.bind, Except.bind] at rooted
      | ok tail =>
        simp only [List.mapM_cons, first, rest, Bind.bind, Except.bind, pure, Except.pure,
          Except.ok.injEq] at rooted
        subst rooted
        have := summary_slots rest
        simp_all [slotRoot, hashTreeRoot_chunk (hashTreeRoot_size _ _ _ first)]

/-- A vector of composite elements has the root of the vector of their roots. -/
theorem hashTreeRoot_vector_summary {element : Desc} {length : Nat} {values : List Value}
    {roots : List Bytes} (composite : element.isBasic = false)
    (rooted : values.mapM (hashTreeRoot element) = .ok roots) :
    hashTreeRoot (.vector (.byteVector bytesPerChunk) length) (.seq (roots.map Value.bytes))
      = hashTreeRoot (.vector element length) (.seq values) := by
  obtain ⟨same, counted⟩ := summary_slots rooted
  by_cases sized : values.length = length
  · exact hashTreeRoot_slots (limit := some length) (mixin := none)
      (by simp [merkleLayout, sequenceLayout, counted, sized, Desc.isBasic, MerkleLayout.nesting,
        pure, Except.pure])
      (by simp [merkleLayout, sequenceLayout, composite, sized, MerkleLayout.nesting,
        pure, Except.pure]) same
  · rw [hashTreeRoot_refused (fault := .scope length values.length),
      hashTreeRoot_refused (fault := .scope length values.length)]
    all_goals simp [merkleLayout, counted, sized, Bind.bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw]

/-- A list of composite elements has the root of the list of their roots. -/
theorem hashTreeRoot_list_summary {element : Desc} {limit : Nat} {values : List Value}
    {roots : List Bytes} (composite : element.isBasic = false)
    (rooted : values.mapM (hashTreeRoot element) = .ok roots) :
    hashTreeRoot (.list (.byteVector bytesPerChunk) limit) (.seq (roots.map Value.bytes))
      = hashTreeRoot (.list element limit) (.seq values) := by
  obtain ⟨same, counted⟩ := summary_slots rooted
  by_cases fits : values.length ≤ limit
  · exact hashTreeRoot_slots (limit := some limit) (mixin := some (lengthWord values.length))
      (by simp [merkleLayout, sequenceLayout, counted, fits, Desc.isBasic, MerkleLayout.nesting,
        Bind.bind, Except.bind, pure, Except.pure])
      (by simp [merkleLayout, sequenceLayout, composite, fits, MerkleLayout.nesting,
        Bind.bind, Except.bind, pure, Except.pure]) same
  · rw [hashTreeRoot_refused (fault := .overLimit limit values.length),
      hashTreeRoot_refused (fault := .overLimit limit values.length)]
    all_goals simp [merkleLayout, counted, Nat.lt_of_not_le fits, Bind.bind, Except.bind, throw,
      throwThe, MonadExceptOf.throw]

/-- A progressive list of composite elements has the root of the progressive list of their roots. -/
theorem hashTreeRoot_progressiveList_summary {element : Desc} {limit : Option Nat}
    {values : List Value} {roots : List Bytes} (composite : element.isBasic = false)
    (rooted : values.mapM (hashTreeRoot element) = .ok roots) :
    hashTreeRoot (.progressiveList (.byteVector bytesPerChunk) limit) (.seq (roots.map Value.bytes))
      = hashTreeRoot (.progressiveList element limit) (.seq values) := by
  obtain ⟨same, counted⟩ := summary_slots rooted
  cases checked : boundCheck limit values.length with
  | ok _ =>
    exact hashTreeRoot_slots (limit := none) (mixin := some (lengthWord values.length))
      (by simp [merkleLayout, sequenceLayout, counted, checked, Desc.isBasic, MerkleLayout.nesting,
        Bind.bind, Except.bind, pure, Except.pure])
      (by simp [merkleLayout, sequenceLayout, composite, checked, MerkleLayout.nesting,
        Bind.bind, Except.bind, pure, Except.pure])
      same
  | error fault =>
    rw [hashTreeRoot_refused (fault := fault), hashTreeRoot_refused (fault := fault)]
    all_goals simp [merkleLayout, counted, checked, Bind.bind, Except.bind]

end EthLib.Consensus.Ssz
