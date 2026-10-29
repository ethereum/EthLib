import EthLib.Serialization.Proofs.Ssz.Codec.BindingPacking
import EthLib.Serialization.Proofs.Ssz.Codec.BindingDomain
import EthLib.Serialization.Proofs.Ssz.Codec.LengthBinding
import EthLib.Serialization.Proofs.Ssz.Codec.LayoutMixin

/-! Before hashing, SSZ layouts preserve admissible values with exact length words. -/

namespace EthLib.Serialization.Ssz

/-- Fixed-size leaf layouts preserve their entire encoding. -/
theorem fixedLeaf_injective {shape : Desc} {left right : Value} {layout : MerkleLayout}
    (sound : shape.wellFormed = .ok ()) (leftFits : Fits shape left) (rightFits : Fits shape right)
    {width : Nat} (fixed : shape.fixedSize = some width)
    (first : fixedLeaf shape left = .ok layout) (second : fixedLeaf shape right = .ok layout) :
    left = right := by
  -- A successful fixed leaf must contain a successful encoding of its value.
  cases a : serialize shape left <;> cases b : serialize shape right <;>
    simp only [fixedLeaf, a, b, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq,
      reduceCtorEq] at first second
  rename_i bytes other
  -- Equal layouts contain equal arrays of packed encoding nodes.
  have nodes : packBytes bytes = packBytes other :=
    Leaves.packed.inj (congrArg MerkleLayout.leaves (first.trans second.symm))
  -- The fixed type determines the byte count, allowing final node padding to be removed unambiguously.
  have encoded := packBytes_injective
    ((serialize_size_of_wellFormed sound leftFits fixed a).trans
      (serialize_size_of_wellFormed sound rightFits fixed b).symm) nodes
  -- Canonical encoding recovers the same admissible value from the common byte string.
  exact serialize_injective_of_wellFormed sound leftFits rightFits a (encoded ▸ b)

/-- Equal sequence layouts preserve their elements when the element counts agree. -/
theorem sequenceLayout_injective {element : Desc} {left right : List Value}
    {positions : Option Nat} {leftWord rightWord : Option Bytes} {layout : MerkleLayout}
    (sound : element.wellFormed = .ok ()) (counts : left.length = right.length)
    (leftFits : ∀ value ∈ left, Fits element value)
    (rightFits : ∀ value ∈ right, Fits element value)
    (first : sequenceLayout element left positions leftWord = .ok layout)
    (second : sequenceLayout element right positions rightWord = .ok layout) : left = right := by
  -- Basic elements share packed nodes, while composite elements remain explicit values in the unhashed layout.
  by_cases basic : element.isBasic = true
  · cases a : serializeEach element left <;> cases b : serializeEach element right <;>
      simp only [sequenceLayout, basic, ite_true, a, b, Bind.bind, Except.bind,
        pure, Except.pure, Except.ok.injEq, reduceCtorEq] at first second
    rename_i parts other
    -- Equality of the layouts preserves the packed encoded streams.
    have packed : packElements parts = packElements other :=
      Leaves.packed.inj (congrArg MerkleLayout.leaves (first.trans second.symm))
    -- Every basic element has a fixed byte width determined by its type.
    have fixed : element.fixedSize = some element.itemLength := by
      cases element <;> simp_all [Desc.isBasic, Desc.fixedSize, Desc.itemLength]
    -- The common element count and width recover the same ordered sequence from the packed stream.
    exact packElements_injective sound fixed counts leftFits rightFits a b packed
  · have noBasic : element.isBasic = false := Bool.eq_false_iff.mpr basic
    simp only [sequenceLayout, noBasic, Bool.false_eq_true, ite_false, pure, Except.pure,
      Except.ok.injEq] at first second
    -- For composite elements, each occupied slot still stores its original value and type.
    have entries := Leaves.nested.inj (congrArg MerkleLayout.leaves (first.trans second.symm))
    -- Projecting away the shared element type recovers the original optional values in order.
    have recovered := congrArg (List.map fun entry => entry.map Prod.snd) entries
    -- Marking a value as present does not identify two different values.
    apply (List.map_inj_right fun _ _ equal => Option.some.inj equal).mp
    simpa only [List.map_map, Function.comp_def, Option.map_some] using recovered

/-- Equal length words recover their counts throughout the admitted commitment domain. -/
theorem sequenceLayout_count {element : Desc} {left right : List Value} {positions : Option Nat}
    {layout : MerkleLayout} (leftBound : left.length < 2 ^ 256)
    (rightBound : right.length < 2 ^ 256)
    (first : sequenceLayout element left positions (lengthWord left.length) = .ok layout)
    (second : sequenceLayout element right positions (lengthWord right.length) = .ok layout) :
    left.length = right.length := by
  -- The 256-bit bounds make length-word equality imply equality of the complete natural-number counts.
  apply lengthWord_injective leftBound rightBound
  exact Option.some.inj ((sequenceLayout_mixin first).symm.trans (sequenceLayout_mixin second))

private theorem zip_values_injective {fields : List Desc} {left right : List Value}
    (leftCount : fields.length = left.length) (rightCount : fields.length = right.length)
    (same : fields.zip left = fields.zip right) : left = right := by
  -- There is exactly one value per field, so pairing with fields cannot discard a trailing value.
  induction fields generalizing left right with
  | nil => cases left <;> cases right <;> simp_all
  | cons field fields ih =>
    cases left <;> cases right <;> simp_all
    exact ih rfl (by omega) same.2

/-- The unhashed-layout binding obligation for one declared type. -/
private def LayoutDeterminesValue (shape : Desc) : Prop :=
  -- The declared type, admissibility, and exact nested counts are shared across all layout families.
  ∀ {left right : Value} {layout : MerkleLayout}, shape.wellFormed = .ok () →
    Fits shape left → Fits shape right → CommitmentSized shape left → CommitmentSized shape right →
    merkleLayout shape left = .ok layout → merkleLayout shape right = .ok layout → left = right

/-- Byte-list length words recover the byte count before the packed payload is compared. -/
private theorem layoutDetermines_byteList (capacity : Nat) : LayoutDeterminesValue (.byteList capacity) := by
  -- Admissibility supplies the capacity bound, while exact-count bounds prevent length-word truncation.
  intro left right layout sound leftFits rightFits leftSized rightSized first second
  cases leftFits with
  | byteList limit =>
    cases rightFits with
    | byteList otherLimit =>
      cases leftSized with
      | byteList bound =>
        cases rightSized with
        | byteList otherBound =>
          simp only [merkleLayout, Nat.not_lt.mpr limit, Nat.not_lt.mpr otherLimit, ite_false,
            pure, Except.pure, Except.ok.injEq] at first second
          have same := first.trans second.symm
          -- Equal mixing words recover equal payload counts before the packed nodes are unpacked.
          have counts := lengthWord_injective bound otherBound
            (Option.some.inj (congrArg MerkleLayout.mixin same))
          exact congrArg Value.bytes (packBytes_injective counts
            (Leaves.packed.inj (congrArg MerkleLayout.leaves same)))

/-- A byte vector's declared count fixes how many packed bytes are payload. -/
private theorem layoutDetermines_byteVector (count : Nat) :
    LayoutDeterminesValue (.byteVector count) := by
  -- Both values have the declared byte count, so the final node padding is known.
  intro left right layout sound leftFits rightFits leftSized rightSized first second
  cases leftFits with
  | byteVector length =>
    cases rightFits with
    | byteVector otherLength =>
      simp only [merkleLayout, length, otherLength, bne_self_eq_false, Bool.false_eq_true,
        ite_false, pure, Except.pure, Except.ok.injEq] at first second
      exact congrArg Value.bytes (packBytes_injective (length.trans otherLength.symm)
        (Leaves.packed.inj (congrArg MerkleLayout.leaves (first.trans second.symm))))

/-- A bitvector’s declared count disambiguates its final padded byte. -/
private theorem layoutDetermines_bitVector (count : Nat) : LayoutDeterminesValue (.bitVector count) := by
  -- Both values have the declared bit count, including any zero bits at the end.
  intro left right layout sound leftFits rightFits leftSized rightSized first second
  cases leftFits with
  | bitVector length =>
    cases rightFits with
    | bitVector otherLength =>
      simp only [merkleLayout, length, otherLength, bne_self_eq_false, Bool.false_eq_true,
        ite_false, pure, Except.pure, Except.ok.injEq] at first second
      exact congrArg Value.bits (packedBits_injective (length.trans otherLength.symm)
        (Leaves.packed.inj (congrArg MerkleLayout.leaves (first.trans second.symm))))

/-- Bit-list length words distinguish significant bits from final padding. -/
private theorem layoutDetermines_bitList (capacity : Nat) : LayoutDeterminesValue (.bitList capacity) := by
  -- Admissibility supplies the capacity bound, and the mixing word retains the exact bit count.
  intro left right layout sound leftFits rightFits leftSized rightSized first second
  cases leftFits with
  | bitList limit =>
    cases rightFits with
    | bitList otherLimit =>
      cases leftSized with
      | bitList bound =>
        cases rightSized with
        | bitList otherBound =>
          simp only [merkleLayout, Nat.not_lt.mpr limit, Nat.not_lt.mpr otherLimit, ite_false,
            pure, Except.pure, Except.ok.injEq] at first second
          have same := first.trans second.symm
          -- Equal mixing words recover equal payload counts before the packed nodes are unpacked.
          have counts := lengthWord_injective bound otherBound
            (Option.some.inj (congrArg MerkleLayout.mixin same))
          exact congrArg Value.bits (packedBits_injective counts
            (Leaves.packed.inj (congrArg MerkleLayout.leaves same)))

/-- Progressive bit lists retain their exact bit counts, bound or none. -/
private theorem layoutDetermines_progressiveBitList (limit : Option Nat) :
    LayoutDeterminesValue (.progressiveBitList limit) := by
  -- A bound does not remove the need for an exact 256-bit length word.
  intro left right layout sound leftFits rightFits leftSized rightSized first second
  cases leftFits with
  | progressiveBitList within =>
    cases rightFits with
    | progressiveBitList otherWithin =>
      cases leftSized with
      | progressiveBitList bound =>
        cases rightSized with
        | progressiveBitList otherBound =>
          simp only [merkleLayout, boundCheck_of_withinBound _ _ within,
            boundCheck_of_withinBound _ _ otherWithin, Bind.bind, Except.bind, pure, Except.pure,
            Except.ok.injEq] at first second
          have same := first.trans second.symm
          -- Equal mixing words recover equal payload counts before the packed nodes are unpacked.
          have counts := lengthWord_injective bound otherBound
            (Option.some.inj (congrArg MerkleLayout.mixin same))
          exact congrArg Value.bits (packedBits_injective counts
            (Leaves.packed.inj (congrArg MerkleLayout.leaves same)))

/-- Vectors recover their element count from the type declaration. -/
private theorem layoutDetermines_vector (element : Desc) (count : Nat) : LayoutDeterminesValue (.vector element count) := by
  -- The type determines the number of elements before any shared-node padding is removed.
  intro left right layout sound leftFits rightFits leftSized rightSized first second
  cases leftFits with
  | vector count each =>
    cases rightFits with
    | vector otherCount otherEach =>
      simp only [merkleLayout, count, otherCount, bne_self_eq_false, Bool.false_eq_true,
        ite_false] at first second
      -- The well-formed enclosing type guarantees a well-formed element type for recovering each element.
      have childSound := wellFormed_vector sound
      exact congrArg Value.seq (sequenceLayout_injective childSound (count.trans otherCount.symm)
        each otherEach first second)

/-- Lists recover their element count from the length word. -/
private theorem layoutDetermines_list (element : Desc) (capacity : Nat) : LayoutDeterminesValue (.list element capacity) := by
  -- Recover the actual element count from the mixing word before comparing element contents.
  intro left right layout sound leftFits rightFits leftSized rightSized first second
  cases leftFits with
  | list limit each =>
    cases rightFits with
    | list otherLimit otherEach =>
      cases leftSized with
      | list bound _ =>
        cases rightSized with
        | list otherBound _ =>
          simp only [merkleLayout, Nat.not_lt.mpr limit, Nat.not_lt.mpr otherLimit, ite_false] at first second
          -- The well-formed enclosing type guarantees a well-formed element type for recovering each element.
          have childSound := wellFormed_list sound
          exact congrArg Value.seq (sequenceLayout_injective childSound
            (sequenceLayout_count bound otherBound first second) each otherEach first second)

/-- Progressive lists recover their count before comparing their element streams. -/
private theorem layoutDetermines_progressiveList (element : Desc) (limit : Option Nat) :
    LayoutDeterminesValue (.progressiveList element limit) := by
  -- The exact length word determines how many elements the progressive layout must contain.
  intro left right layout sound leftFits rightFits leftSized rightSized first second
  cases leftFits with
  | progressiveList within each =>
    cases rightFits with
    | progressiveList otherWithin otherEach =>
      cases leftSized with
      | progressiveList bound _ =>
        cases rightSized with
        | progressiveList otherBound _ =>
          simp only [merkleLayout, boundCheck_of_withinBound _ _ within,
            boundCheck_of_withinBound _ _ otherWithin, Bind.bind, Except.bind] at first second
          -- The well-formed enclosing type guarantees a well-formed element type for recovering each element.
          have childSound := wellFormed_progressiveList sound
          exact congrArg Value.seq (sequenceLayout_injective childSound
            (sequenceLayout_count bound otherBound first second) each otherEach first second)

/-- Container positions preserve the original field-value pairing. -/
private theorem layoutDetermines_container (names : List String) (fields : List Desc) : LayoutDeterminesValue (.container names fields) := by
  -- Both values provide one value for every declared field in the same order.
  intro left right layout sound leftFits rightFits leftSized rightSized first second
  cases leftFits with
  | container count _ =>
    cases rightFits with
    | container otherCount _ =>
      simp only [merkleLayout, ← count, ← otherCount, bne_self_eq_false, Bool.false_eq_true,
        ite_false, pure, Except.pure, Except.ok.injEq] at first second
      -- Equal nested positions recover equal field-value pairs, with no hashing involved yet.
      have pairs := Leaves.nested.inj (congrArg MerkleLayout.leaves (first.trans second.symm))
      have same := (List.map_inj_right (fun _ _ equal => Option.some.inj equal)).mp pairs
      -- Removing the common field declarations leaves the same ordered values.
      exact congrArg Value.seq (zip_values_injective count otherCount same)

/-- Removing inactive positions recovers every progressive-container field in order. -/
private theorem layoutDetermines_progressiveContainer (active : List Bool) (names : List String) (fields : List Desc) : LayoutDeterminesValue (.progressiveContainer active names fields) := by
  -- Successful placement preserves all field values while inserting the declared inactive positions.
  intro left right layout sound leftFits rightFits leftSized rightSized first second
  cases leftFits with
  | @progressiveContainer active names fields values count each =>
    cases rightFits with
    | @progressiveContainer _ _ _ other otherCount otherEach =>
      cases a : layoutSlots active fields values <;> cases b : layoutSlots active fields other <;>
        simp only [merkleLayout, a, b, Bind.bind, Except.bind, pure, Except.pure,
          Except.ok.injEq, reduceCtorEq] at first second
      -- Equal nested leaves retain identical placed fields, including identical gaps.
      have same := Leaves.nested.inj (congrArg MerkleLayout.leaves (first.trans second.symm))
      simp only [layoutSlots, ← count, ← otherCount, bne_self_eq_false, Bool.false_eq_true,
        ite_false] at a b
      split at a <;> try contradiction
      split at b <;> try contradiction
      -- Removing inactive positions restores all original field-value pairs in declaration order.
      have pairs := (placeSlots_fields a).symm.trans
        ((congrArg (List.filterMap id) same).trans (placeSlots_fields b))
      exact congrArg Value.seq (zip_values_injective count otherCount pairs)

/-- A union layout retains both the exact selector and the selected value. -/
private theorem layoutDetermines_compatibleUnion (selectors : List Nat) (options : List Desc) : LayoutDeterminesValue (.compatibleUnion selectors options) := by
  -- Both layouts retain one selected option and the selector word attached to it.
  intro left right layout sound leftFits rightFits leftSized rightSized first second
  cases leftFits with
  | compatibleUnion bound named inner =>
    cases rightFits with
    | compatibleUnion otherBound otherNamed otherInner =>
      rename_i selector option value otherSelector otherOption otherValue
      -- Selectors occupy one byte, so both are also fully represented by their 256-bit mixing words.
      have top : maxSelector = 127 := rfl
      simp only [merkleLayout, named, otherNamed, selectorWord, checkSelector_of_range bound,
        checkSelector_of_range otherBound, Bind.bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at first second
      have same := first.trans second.symm
      -- The equal mixing words recover the exact selector, without assuming a selected option in advance.
      have selectorsEqual := lengthWord_injective (by omega : selector < 2 ^ 256)
        (by omega : otherSelector < 2 ^ 256)
        (Option.some.inj (congrArg MerkleLayout.mixin same))
      -- The single occupied position retains the option value itself in the unhashed layout.
      have entries := Leaves.nested.inj (congrArg MerkleLayout.leaves same)
      cases selectorsEqual
      cases (Prod.mk.inj (Option.some.inj (List.cons.inj entries).1)).2
      rfl

/--
An unhashed SSZ layout uniquely determines an admissible value of its declared type.
Every nested variable-size count must fit its 256-bit mixing word.
-/
theorem merkleLayout_injective {shape : Desc} {left right : Value} {layout : MerkleLayout}
    (sound : shape.wellFormed = .ok ()) (leftFits : Fits shape left) (rightFits : Fits shape right)
    (leftSized : CommitmentSized shape left) (rightSized : CommitmentSized shape right)
    (first : merkleLayout shape left = .ok layout)
    (second : merkleLayout shape right = .ok layout) : left = right := by
  -- Fixed encodings, exact length words, and explicit nested values supply the appropriate recovery rule for each type.
  suffices determines : LayoutDeterminesValue shape from
    determines sound leftFits rightFits leftSized rightSized first second
  cases shape
  case bool | uint =>
    exact fun sound leftFits rightFits _ _ first second =>
      fixedLeaf_injective sound leftFits rightFits rfl first second
  case byteVector => exact layoutDetermines_byteVector _
  case byteList => exact layoutDetermines_byteList _
  case bitVector => exact layoutDetermines_bitVector _
  case bitList => exact layoutDetermines_bitList _
  case progressiveBitList => exact layoutDetermines_progressiveBitList _
  case vector => exact layoutDetermines_vector _ _
  case list => exact layoutDetermines_list _ _
  case progressiveList => exact layoutDetermines_progressiveList _ _
  case container => exact layoutDetermines_container _ _
  case progressiveContainer => exact layoutDetermines_progressiveContainer _ _ _
  case compatibleUnion => exact layoutDetermines_compatibleUnion _ _

end EthLib.Serialization.Ssz
