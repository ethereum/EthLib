import EthLib.Consensus.Proofs.Ssz.Codec.PathSelection
import EthLib.Consensus.Proofs.Ssz.Codec.RootDomain

/-! Admissible composite values support paths through their actual fields and elements. -/

namespace EthLib.Consensus.Ssz

/-- A complete bounded value supplies all of its chunks within the declared capacity. -/
theorem rooted_bounded_chunks {shape : Desc} {value : Value} {layout : MerkleLayout}
    {root : Bytes} {capacity : Nat} (rooted : hashTreeRoot shape value = .ok root)
    (laid : merkleLayout shape value = .ok layout) (bounded : layout.limit = some capacity) :
    ∃ chunks, layoutChunksAt (shape.nesting - 1) layout = .ok chunks ∧ chunks.size ≤ capacity := by
  -- Root success requires materialization and bounded merkleization to have succeeded first.
  -- Successful whole-value rooting supplies the exact leaf array and successful contents computation.
  obtain ⟨actual, chunks, contents, actualLayout, materialized, tree, _⟩ :=
    hashTreeRoot_materializes shape value root rooted
  cases laid.symm.trans actualLayout
  rw [bounded] at tree
  refine ⟨chunks, materialized, Nat.not_lt.mp fun over => ?_⟩
  simp [merkleizeBoundedUnchecked, over, Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw] at tree

/-- Composite sequence elements occupy one whole chunk apiece. -/
theorem Desc.itemLength_composite {element : Desc} (composite : element.isBasic = false) :
    element.itemLength = bytesPerChunk := by
  -- Only booleans and unsigned integers can share a chunk with neighbouring elements.
  cases element <;> simp_all [Desc.isBasic, Desc.itemLength]

/-- A container path continues through the actual value paired with its declared field. -/
theorem PathSelects.containerField {names : List String} {fields : List Desc} {values : List Value}
    (sound : (Desc.container names fields).wellFormed = .ok ())
    (fitted : Fits (.container names fields) (.seq values))
    {ordinal : Nat} {child : Desc} {inner : Value} {rest : List PathStep} {node : Bytes}
    (selectedType : fields[ordinal]? = some child) (selectedValue : values[ordinal]? = some inner)
    (suffix : PathSelects child inner rest node) :
    PathSelects (.container names fields) (.seq values) (.position ordinal :: rest) node := by
  -- Pairing fields and values preserves the ordinal used by both the type and Merkle layout.
  obtain ⟨root, rooted, _⟩ := hashTreeRoot_total _ _ sound fitted
  cases fitted with
  | container paired _ =>
    let layout := MerkleLayout.nesting ((fields.zip values).map some) (some fields.length)
    have laid : merkleLayout (.container names fields) (.seq values) = .ok layout := by
      simp [merkleLayout, paired, layout, Pure.pure, Except.pure]
    -- The materialized children fit the same capacity used by the type-level leaf address.
    obtain ⟨chunks, materialized, fits⟩ := rooted_bounded_chunks rooted laid rfl
    apply PathSelects.nested (ordinal := ordinal) laid materialized rfl rfl fits
      (List.getElem?_eq_some_iff.mp selectedType).1 rfl _ _ suffix
    · simpa only [List.getElem?_map, Option.map_eq_some_iff] using
        ⟨(child, inner), List.getElem?_zip_eq_some.mpr ⟨selectedType, selectedValue⟩, rfl⟩
    · simp [Desc.resolveStep, Desc.chunkPosition, Desc.elementType, Desc.chunkCount,
        selectedType, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A vector of composite values preserves the selected element's entire remaining path. -/
theorem PathSelects.vectorElement {element : Desc} {count : Nat} {values : List Value}
    (sound : (Desc.vector element count).wellFormed = .ok ())
    (fitted : Fits (.vector element count) (.seq values)) (composite : element.isBasic = false)
    {ordinal : Nat} {inner : Value} {rest : List PathStep} {node : Bytes}
    (selected : values[ordinal]? = some inner) (suffix : PathSelects element inner rest node) :
    PathSelects (.vector element count) (.seq values) (.position ordinal :: rest) node := by
  -- Composite elements are roots of their own trees, with one root per declared position.
  obtain ⟨root, rooted, _⟩ := hashTreeRoot_total _ _ sound fitted
  cases fitted with
  | vector paired _ =>
    have inside : ordinal < count := by have := (List.getElem?_eq_some_iff.mp selected).1; omega
    let layout := MerkleLayout.nesting (values.map fun value => some (element, value)) (some count)
    have laid : merkleLayout (.vector element count) (.seq values) = .ok layout := by
      simp [merkleLayout, paired, sequenceLayout, composite, layout, Pure.pure, Except.pure]
    -- The materialized children fit the same capacity used by the type-level leaf address.
    obtain ⟨chunks, materialized, fits⟩ := rooted_bounded_chunks rooted laid rfl
    apply PathSelects.nested (ordinal := ordinal) laid materialized rfl rfl fits inside rfl _ _ suffix
    · simp [List.getElem?_map, selected]
    · rw [resolveStep_vector element count ordinal inside, Desc.itemLength_composite composite]
      -- A composite occupies exactly one 32-byte leaf, so byte-based capacity arithmetic reduces to the element count.
      have nodes : (count * bytesPerChunk + bytesPerChunk - 1) / bytesPerChunk = count := by
        unfold bytesPerChunk; omega
      rw [nodes]
      simp [bytesPerChunk]

/-- A bounded composite list path continues only through an element actually present in the value. -/
theorem PathSelects.listElement {element : Desc} {limit : Nat} {values : List Value}
    (fitted : Fits (.list element limit) (.seq values)) (composite : element.isBasic = false)
    {ordinal : Nat} {inner : Value} {rest : List PathStep} {node : Bytes}
    (selected : values[ordinal]? = some inner) (suffix : PathSelects element inner rest node) :
    PathSelects (.list element limit) (.seq values) (.position ordinal :: rest) node := by
  -- The list's declared capacity may exceed its data, but a child path requires a filled slot.
  cases fitted with
  | list within _ =>
    have inside : ordinal < limit := by have := (List.getElem?_eq_some_iff.mp selected).1; omega
    let layout := MerkleLayout.nesting (values.map fun value => some (element, value))
      (some limit) (lengthWord values.length)
    have laid : merkleLayout (.list element limit) (.seq values) = .ok layout := by
      simp [merkleLayout, Nat.not_lt.mpr within, sequenceLayout, composite, layout,
        Pure.pure, Except.pure]
    apply PathSelects.nestedMixed (ordinal := ordinal) laid rfl rfl inside rfl _ _ suffix
    · simp [List.getElem?_map, selected]
    · rw [resolveStep_list element limit ordinal inside, Desc.itemLength_composite composite]
      -- A composite occupies exactly one 32-byte leaf, so byte-based capacity arithmetic reduces to the element count.
      have nodes : (limit * bytesPerChunk + bytesPerChunk - 1) / bytesPerChunk = limit := by
        unfold bytesPerChunk; omega
      rw [nodes]
      simp [bytesPerChunk, gindexConcat_mixed_leaf inside, Bind.bind, Except.bind,
        Pure.pure, Except.pure]

/-- A progressive composite list path follows the occupied element as the spine grows. -/
theorem PathSelects.progressiveListElement {element : Desc} {limit : Option Nat}
    {values : List Value} (composite : element.isBasic = false)
    (within : withinBound limit values.length = true)
    {ordinal : Nat} {inner : Value} {rest : List PathStep} {node : Bytes}
    (selected : values[ordinal]? = some inner) (suffix : PathSelects element inner rest node) :
    PathSelects (.progressiveList element limit) (.seq values) (.position ordinal :: rest)
      node := by
  -- A bound shapes no spine, while membership supplies the leaf the path must reach.
  let layout := MerkleLayout.nesting (values.map fun value => some (element, value))
    none (lengthWord values.length)
  have laid : merkleLayout (.progressiveList element limit) (.seq values) = .ok layout := by
    simp [merkleLayout, sequenceLayout, composite, layout, boundCheck_of_withinBound limit _ within,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  apply PathSelects.nestedProgressive (ordinal := ordinal) laid rfl rfl rfl _ _ suffix
  · simp [List.getElem?_map, selected]
  · rw [resolveStep_progressiveList, Desc.itemLength_composite composite]
    simp [bytesPerChunk]

/-- A progressive container path follows the chosen field across preceding layout gaps. -/
theorem PathSelects.progressiveField {active : List Bool} {names : List String}
    {fields : List Desc} {values : List Value}
    (sound : (Desc.progressiveContainer active names fields).wellFormed = .ok ())
    (fitted : Fits (.progressiveContainer active names fields) (.seq values))
    {ordinal : Nat} {child : Desc} {inner : Value} {rest : List PathStep} {node : Bytes}
    (selectedType : fields[ordinal]? = some child) (selectedValue : values[ordinal]? = some inner)
    (suffix : PathSelects child inner rest node) :
    PathSelects (.progressiveContainer active names fields) (.seq values)
      (.position ordinal :: rest) node := by
  -- EIP-7495 places the field at its set-bit position before the child path is followed.
  obtain ⟨root, rooted, _⟩ := hashTreeRoot_total _ _ sound fitted
  obtain ⟨layout, chunks, contents, laid, _, _, _⟩ :=
    hashTreeRoot_materializes _ _ root rooted
  cases slots : layoutSlots active fields values <;>
    simp [merkleLayout, slots, Bind.bind, Except.bind, Pure.pure, Except.pure] at laid
  rename_i entries
  -- The field ordinal and the active-position lookup identify the same type-value pair.
  obtain ⟨position, placed, chosen⟩ := layoutSlots_position slots _ _ _ selectedType selectedValue
  exact PathSelects.nestedProgressive
    (layout := MerkleLayout.nesting entries none (activeFieldsWord active))
    (by simp [merkleLayout, slots, Bind.bind, Except.bind, Pure.pure, Except.pure]) rfl rfl rfl
    chosen (resolveStep_progressiveContainer active names fields ordinal position child selectedType placed) suffix

/-- A successful union lookup selects the same first matching declaration as its type path. -/
theorem lookupOption_position (selectors : List Nat) (options : List Desc) (selector : Nat)
    (child : Desc) (chosen : lookupOption selectors options selector = .ok child) :
    ∃ slot, selectors.idxOf? selector = some slot ∧ options[slot]? = some child := by
  -- Both traversals stop at the first matching selector and advance the option ordinal together.
  induction selectors generalizing options with
  | nil => cases options <;> simp [lookupOption] at chosen
  | cons first selectors ih =>
    cases options with
    | nil => simp [lookupOption] at chosen
    | cons option options =>
      -- Both lookups stop at the first matching tag and advance their option ordinal together.
      by_cases matched : first == selector
      · obtain rfl : option = child := by simpa [lookupOption, matched] using chosen
        exact ⟨0, by simp [List.idxOf?_cons, matched], rfl⟩
      · simp only [lookupOption, matched, Bool.false_eq_true, ↓reduceIte] at chosen
        obtain ⟨slot, named, found⟩ := ih options chosen
        exact ⟨slot + 1, by simp [List.idxOf?_cons, matched, named], by simpa using found⟩

/-- A compatible union path follows its active selector into exactly the value it carries. -/
theorem PathSelects.unionOption {selectors : List Nat} {options : List Desc}
    {selector : Nat} {child : Desc} {inner : Value} {rest : List PathStep} {node : Bytes}
    (bounded : minSelector ≤ selector ∧ selector ≤ maxSelector)
    (chosen : lookupOption selectors options selector = .ok child)
    (suffix : PathSelects child inner rest node) :
    PathSelects (.compatibleUnion selectors options) (.union selector inner)
      (.position selector :: rest) node := by
  -- EIP-8016 places the active value under index two, opposite its selector word.
  let layout := MerkleLayout.nesting [some (child, inner)] (some 1) (lengthWord selector)
  have laid : merkleLayout (.compatibleUnion selectors options) (.union selector inner) =
      .ok layout := by
    simp [merkleLayout, chosen, selectorWord, checkSelector_of_range bounded, layout,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨slot, named, found⟩ := lookupOption_position selectors options selector child chosen
  -- The successful lookup justifies reading the selected option at that exact ordinal.
  have option : options[slot]! = child := by simp [List.getElem!_eq_getElem?_getD, found]
  apply PathSelects.nestedMixed (ordinal := 0) laid rfl rfl (by decide) rfl rfl _ suffix
  simpa [option, nextPow2, depthFor] using resolveStep_compatibleUnion selectors options selector slot named

/-- An admissible value supplies the empty path's selected root. -/
theorem PathSelects.admissibleRoot {shape : Desc} {value : Value}
    (sound : shape.wellFormed = .ok ()) (fitted : Fits shape value) :
    ∃ root, PathSelects shape value [] root := by
  -- Root totality needs no serialization offset bound or path-read assumption.
  obtain ⟨root, rooted, _⟩ := hashTreeRoot_total shape value sound fitted
  exact ⟨root, PathSelects.root rooted⟩

end EthLib.Consensus.Ssz
