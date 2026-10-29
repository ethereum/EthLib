import EthLib.Serialization.Proofs.Ssz.Type.CompatibilitySymmetry
import EthLib.Serialization.Proofs.Ssz.Type.PathSteps

/-! What the compatibility checks buy: the tree positions two compatible types agree on. -/

namespace EthLib.Serialization.Ssz

/--
Every option a union declares is compatible with every option it declares.

This is what the pairwise check is for, and it is checked once per unordered pair.
-/
theorem optionsCompatible_pairwise : ∀ (selectors : List Nat) (options : List Desc),
    Desc.optionsCompatible selectors options = .ok () →
      ∀ left ∈ options, ∀ right ∈ options, isCompatible left right = true := by
  intro selectors options
  induction options generalizing selectors with
  | nil => simp
  | cons option rest ih =>
    intro checked left leftIn right rightIn
    rw [Desc.optionsCompatible] at checked
    -- A clash with any later option would have been found, and the search found none.
    cases searched : (List.range rest.length).find? (fun slot => !isCompatible option rest[slot]!)
      <;> simp only [searched, Bind.bind, Except.bind, reduceCtorEq] at checked
    -- Each later option is compatible with this one, read off the empty search.
    have later : ∀ other ∈ rest, isCompatible option other = true := by
      intro other member
      obtain ⟨slot, bounded, held⟩ := List.mem_iff_getElem.mp member
      have missed := List.find?_eq_none.mp searched slot (List.mem_range.mpr bounded)
      rw [getElem!_pos rest slot bounded, held] at missed
      simpa using missed
    -- The four ways two options can be drawn from this list.
    rcases List.mem_cons.mp leftIn with rfl | leftLater <;>
      rcases List.mem_cons.mp rightIn with rfl | rightLater
    · exact isCompatible_self _
    · exact later right rightLater
    · exact (isCompatible_symm _ _).trans (later left leftLater)
    · exact ih (selectors.drop 1) checked left leftLater right rightLater

/--
Whichever option a union carries, that option hangs at the same node.

Together with the pairwise check, that is what EIP-8016 asks: one tree shape serves them all.
-/
theorem union_options_share_one_tree {selectors : List Nat} {options : List Desc}
    (checked : Desc.optionsCompatible selectors options = .ok ()) :
    (∀ left ∈ options, ∀ right ∈ options, isCompatible left right = true) ∧
      ∀ selector slot, selectors.idxOf? selector = some slot →
        Desc.resolveStep (.compatibleUnion selectors options) (.position selector)
          = .ok (2, some options[slot]!) :=
  ⟨optionsCompatible_pairwise selectors options checked,
    fun selector slot found => resolveStep_compatibleUnion selectors options selector slot found⟩

/-- Positions the set bits of a layout occupy, in declaration order. -/
def activeSlots (active : List Bool) (start : Nat) : List Nat :=
  (active.zipIdx start).filterMap fun (present, position) => if present then some position else none

/-- The placed fields pair those positions with the declared names, one for one. -/
theorem placedFields_eq (active : List Bool) (names : List String) :
    placedFields active names = (activeSlots active 0).zip names := rfl

/-- The position of one field is where the walk over the layout says it sits. -/
theorem activeSlots_getElem? : ∀ (active : List Bool) (start ordinal : Nat),
    (activeSlots active start)[ordinal]? = (activePosition active ordinal).map (· + start) := by
  intro active
  induction active with
  | nil => simp [activeSlots, activePosition]
  | cons present rest ih =>
    intro start ordinal
    -- A gap consumes only a position, while a field consumes a position and an ordinal.
    simp only [activeSlots] at ih ⊢
    cases present <;> cases ordinal <;>
      simp [List.zipIdx_cons, activePosition, ih] <;> cases activePosition rest _ <;> simp <;> omega

/-- A placed field appears in the layout's own list of placed fields. -/
theorem placedOrdinals_mem {active : List Bool} {names : List String}
    {ordinal position : Nat} {name : String}
    (placed : activePosition active ordinal = some position)
    (named : names[ordinal]? = some name) :
    (position, name, ordinal) ∈ placedOrdinals active names := by
  -- Read the entry off at the field's own ordinal, one list at a time.
  have slot : (activeSlots active 0)[ordinal]? = some position := by
    rw [activeSlots_getElem?, placed]
    simp
  have paired : (placedFields active names)[ordinal]? = some (position, name) := by
    rw [placedFields_eq]
    exact List.getElem?_zip_eq_some.mpr ⟨slot, named⟩
  have mapped : (placedOrdinals active names)[ordinal]? = some (position, name, ordinal) := by
    rw [placedOrdinals, List.getElem?_map, List.getElem?_zipIdx, paired]
    simp
  exact List.mem_of_getElem? mapped

/-- Reading a field's layout position answers exactly when the walk over the layout does. -/
theorem layoutPosition_ok {active : List Bool} {ordinal position : Nat} :
    layoutPosition active ordinal = .ok position ↔ activePosition active ordinal = some position := by
  unfold layoutPosition
  cases activePosition active ordinal <;> simp

/--
Two layouts that agree place a field of one name at one position.

That is what keeps a field addressable at the same node as later fields are appended.
-/
theorem layoutsAgree_named_field_position {budget : Nat}
    {leftActive rightActive : List Bool} {leftNames rightNames : List String}
    {leftFields rightFields : List Desc}
    (agree : layoutsAgree budget leftActive leftNames leftFields
      rightActive rightNames rightFields = true)
    {leftOrdinal rightOrdinal leftPosition rightPosition : Nat} {name : String}
    (leftPlaced : layoutPosition leftActive leftOrdinal = .ok leftPosition)
    (rightPlaced : layoutPosition rightActive rightOrdinal = .ok rightPosition)
    (leftNamed : leftNames[leftOrdinal]? = some name)
    (rightNamed : rightNames[rightOrdinal]? = some name) :
    leftPosition = rightPosition :=
  layoutsAgree_name_position agree
    (placedOrdinals_mem (layoutPosition_ok.mp leftPlaced) leftNamed)
    (placedOrdinals_mem (layoutPosition_ok.mp rightPlaced) rightNamed) rfl


/-- Two different progressive containers are compatible exactly when their layouts agree. -/
theorem compatibleAt_progressiveContainer {budget : Nat}
    {leftActive rightActive : List Bool} {leftNames rightNames : List String}
    {leftFields rightFields : List Desc}
    (compatible : compatibleAt (budget + 1)
        (.progressiveContainer leftActive leftNames leftFields)
        (.progressiveContainer rightActive rightNames rightFields) = true)
    (distinct : Desc.progressiveContainer leftActive leftNames leftFields
        ≠ .progressiveContainer rightActive rightNames rightFields) :
    layoutsAgree budget leftActive leftNames leftFields
      rightActive rightNames rightFields = true := by
  -- Neither shape spells a byte array, so the comparison reaches the layout rule.
  rw [compatibleAt, ite_eq_right (by simpa using distinct)] at compatible
  simpa [Desc.byteSequence] using compatible

/-- Every spine node a chunk lands on is a node, so an index built from one names something. -/
theorem progressiveChunkGindex_pos (chunk : Nat) :
    ∀ depth spine, 1 ≤ spine → 1 ≤ progressiveChunkGindex chunk depth spine := by
  -- Each level of the walk takes at least one chunk off, so the chunk count carries it.
  induction chunk using Nat.strongRecOn with
  | _ chunk ih =>
    intro depth spine named
    rw [progressiveChunkGindex]
    have wide : 0 < 2 ^ depth := Nat.pos_of_neZero (2 ^ depth)
    split
    · -- The chunk sits on this level, below a spine node that is already past the root.
      have product : 0 < spine * 2 * 2 ^ depth :=
        Nat.mul_pos (Nat.mul_pos named (by omega)) wide
      omega
    · -- The walk moves along the spine, whose next node is wider still.
      rename_i notFits
      exact ih (chunk - 2 ^ depth) (by omega) (depth + 2) (spine * 2 + 1) (by omega)

/-- A field of a progressive container is addressed at the spine node its position names. -/
theorem progressiveContainer_field_index {active : List Bool} {names : List String}
    {fields : List Desc} {ordinal position : Nat} {child : Desc}
    (selected : fields[ordinal]? = some child)
    (placed : layoutPosition active ordinal = .ok position) :
    getGeneralizedIndex (.progressiveContainer active names fields) [.position ordinal]
      = .ok (progressiveChunkGindex position) := by
  -- One step reaches the field, and the empty path below it adds no turn of its own.
  rw [getGeneralizedIndex_cons (resolveStep_progressiveContainer active names fields
    ordinal position child selected placed) []]
  simp only [getGeneralizedIndex, Bind.bind, Except.bind]
  exact gindexConcat_root_right (progressiveChunkGindex_pos position 0 2 (by omega))

/--
Compatible progressive containers address a field of one name at one node.

    left   active [1,1]      names ["a","b"]        "b" sits at position 1
    right  active [1,1,1]    names ["a","b","c"]    "b" sits at position 1

Appending a field leaves every earlier field where it was.
A proof of "b" written against the shorter declaration therefore reads against the longer one.
Where no name is shared the two say nothing about each other, which is the other half of the rule.

The two declarations are required to differ.
A declaration that repeats a field name disagrees with its own layout, and is compatible
with itself only because a declaration is compared with itself before its layout is read.
-/
theorem compatible_named_field_index
    {leftActive rightActive : List Bool} {leftNames rightNames : List String}
    {leftFields rightFields : List Desc}
    (compatible : isCompatible (.progressiveContainer leftActive leftNames leftFields)
        (.progressiveContainer rightActive rightNames rightFields) = true)
    (distinct : Desc.progressiveContainer leftActive leftNames leftFields
        ≠ .progressiveContainer rightActive rightNames rightFields)
    {leftOrdinal rightOrdinal leftPosition rightPosition : Nat} {name : String}
    {leftChild rightChild : Desc}
    (leftPlaced : layoutPosition leftActive leftOrdinal = .ok leftPosition)
    (rightPlaced : layoutPosition rightActive rightOrdinal = .ok rightPosition)
    (leftSelected : leftFields[leftOrdinal]? = some leftChild)
    (rightSelected : rightFields[rightOrdinal]? = some rightChild)
    (leftNamed : leftNames[leftOrdinal]? = some name)
    (rightNamed : rightNames[rightOrdinal]? = some name) :
    getGeneralizedIndex (.progressiveContainer leftActive leftNames leftFields)
        [.position leftOrdinal]
      = getGeneralizedIndex (.progressiveContainer rightActive rightNames rightFields)
        [.position rightOrdinal] := by
  -- The comparison always has a step to spend, both declarations nesting at least one level.
  have positive := Desc.nesting_pos (Desc.progressiveContainer leftActive leftNames leftFields)
  obtain ⟨spare, budget⟩ : ∃ spare,
      (Desc.progressiveContainer leftActive leftNames leftFields).nesting
        + (Desc.progressiveContainer rightActive rightNames rightFields).nesting = spare + 1 :=
    ⟨(Desc.progressiveContainer leftActive leftNames leftFields).nesting
        + (Desc.progressiveContainer rightActive rightNames rightFields).nesting - 1, by omega⟩
  rw [isCompatible, budget] at compatible
  -- A shared name is a shared position, and a shared position is a shared node.
  have same := layoutsAgree_named_field_position
    (compatibleAt_progressiveContainer compatible distinct)
    leftPlaced rightPlaced leftNamed rightNamed
  rw [progressiveContainer_field_index leftSelected leftPlaced,
    progressiveContainer_field_index rightSelected rightPlaced, same]


/-
A worked pair, so the theorems above are known to say something about real declarations.

    before  active [1,1]    names ["a","b"]        field "b" reads at index 40
    after   active [1,1,1]  names ["a","b","c"]    field "b" reads at index 40

The appended field takes index 41, which is a node the shorter declaration never named.
-/
private def beforeAppend : Desc :=
  .progressiveContainer [true, true] ["a", "b"] [.uint 8, .uint 4]

private def afterAppend : Desc :=
  .progressiveContainer [true, true, true] ["a", "b", "c"] [.uint 8, .uint 4, .uint 2]

private example : isCompatible beforeAppend afterAppend = true := by
  simp [beforeAppend, afterAppend, isCompatible, Desc.nesting, Desc.deepestNesting, compatibleAt,
    Desc.byteSequence, layoutsAgree, placedOrdinals, placedFields, layoutPairAgree]

private example :
    getGeneralizedIndex beforeAppend [.position 1] = getGeneralizedIndex afterAppend [.position 1] := by
  rw [beforeAppend, afterAppend, progressiveContainer_field_index (child := .uint 4) rfl rfl,
    progressiveContainer_field_index (child := .uint 4) rfl rfl]


end EthLib.Serialization.Ssz
