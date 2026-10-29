import EthLib.Consensus.Proofs.Ssz.Codec.BindingLeafShape
import EthLib.Consensus.Proofs.Ssz.Codec.BindingDomain
import EthLib.Consensus.Proofs.Ssz.Codec.RootDomain
import EthLib.Consensus.Proofs.Ssz.Codec.LengthBinding
import EthLib.Consensus.Proofs.Ssz.Codec.LayoutMixin

/-! A type and its exact mixing word determine the alignment of its Merkle leaves. -/

namespace EthLib.Consensus.Ssz

private theorem each_basic_bytes {element : Desc} {values : List Value} {parts : List Bytes}
    (basic : element.isBasic = true) (each : ∀ value ∈ values, Fits element value)
    (wrote : serializeEach element values = .ok parts) :
    (parts.foldl (fun total part => total ++ part) (#[] : Bytes)).size =
      values.length * element.itemLength := by
  -- Basic elements have a fixed byte width, so the packed stream length is element count times width.
  obtain ⟨_, generated, sized⟩ := serializeEach_basic_size basic values each
  -- Deterministic serialization identifies the given parts with the parts of the size theorem.
  rwa [← Except.ok.inj (wrote.symm.trans generated)] at sized

/-- Equal-length sequences under the same element type have aligned leaf shapes. -/
theorem sequenceLayout_shapes {element : Desc} {left right : List Value}
    {positions : Option Nat} {leftMixin rightMixin : Option Bytes}
    {first second : MerkleLayout}
    (lengths : left.length = right.length)
    (leftFits : ∀ value ∈ left, Fits element value)
    (rightFits : ∀ value ∈ right, Fits element value)
    (laid : sequenceLayout element left positions leftMixin = .ok first)
    (otherLaid : sequenceLayout element right positions rightMixin = .ok second) :
    first.limit = second.limit ∧ first.leaves.shapes = second.leaves.shapes := by
  -- Composite elements contribute one typed position each, while basic elements share packed nodes.
  cases basic : element.isBasic with
  | false =>
    simp only [sequenceLayout, basic, Bool.false_eq_true, ite_false, pure, Except.pure,
      Except.ok.injEq] at laid otherLaid
    subst first second
    -- Equal element counts give the same repeated child-type sequence.
    simp [MerkleLayout.nesting, Leaves.shapes, List.map_map, Function.comp_def,
      List.map_const', lengths]
  | true =>
    cases a : serializeEach element left <;> cases b : serializeEach element right <;>
      simp only [sequenceLayout, basic, ite_true, a, b, Bind.bind, Except.bind,
        pure, Except.pure, Except.ok.injEq, reduceCtorEq] at laid otherLaid
    subst first second
    -- Equal element counts and byte widths produce equal packed-node counts and capacities.
    simp only [MerkleLayout.packing, Leaves.shapes, packElements, packBytes_size,
      each_basic_bytes basic leftFits a, each_basic_bytes basic rightFits b, lengths,
      and_self]

/-- Placing fields preserves their type projection independently of their values. -/
theorem placeSlots_shapes {active : List Bool} {left right : List (Desc × Value)}
    {first second : List (Option (Desc × Value))}
    (types : left.map Prod.fst = right.map Prod.fst)
    (placed : placeSlots active left = .ok first)
    (otherPlaced : placeSlots active right = .ok second) :
    first.map (Option.map Prod.fst) = second.map (Option.map Prod.fst) := by
  -- Use the common active-field mask to place both type sequences at the same positions.
  induction active generalizing left right first second with
  -- An exhausted mask requires that both field sequences are also exhausted.
  | nil =>
    cases left <;> cases right <;> simp [placeSlots] at placed otherPlaced
    subst first second
    rfl
  | cons bit active ih =>
    cases bit with
    -- An inactive position adds a gap to both layouts without consuming a field.
    | false =>
      cases a : placeSlots active left <;> cases b : placeSlots active right <;>
        simp [placeSlots, a, b, Bind.bind, Except.bind, pure, Except.pure] at placed otherPlaced
      subst first second
      simp [ih types a b]
    -- An active position consumes one field from each sequence.
    | true =>
      cases left <;> cases right <;> simp [placeSlots] at placed otherPlaced
      rename_i l left r right
      -- The consumed fields have equal types, and their remaining type sequences still agree.
      obtain ⟨head, tails⟩ := List.cons.inj types
      cases a : placeSlots active left <;> cases b : placeSlots active right <;>
        simp [a, b, Functor.map, Except.map] at placed otherPlaced
      subst first second
      simp [head, ih tails a b]

private theorem merkleLayout_mixed {shape : Desc} {value : Value} {layout : MerkleLayout}
    (laid : merkleLayout shape value = .ok layout) :
    layout.mixin.isSome = (match shape with
      | .bool | .uint _ | .byteVector _ | .bitVector _ | .vector _ _ | .container _ _ => false
      | _ => true) := by
  -- Fixed-size leaves, vectors, and ordinary containers omit metadata mixing.
  -- Variable-size collections, progressive containers, and unions always include a word.
  cases shape <;> cases value <;>
    simp only [merkleLayout, fixedLeaf, sequenceLayout, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at laid
  all_goals repeat first | split at laid | contradiction
  all_goals cases laid; rfl

/-- The type alone determines whether a root includes a mixing word. -/
theorem merkleLayout_mixin_presence {shape : Desc} {left right : Value}
    {first second : MerkleLayout}
    (laid : merkleLayout shape left = .ok first)
    (otherLaid : merkleLayout shape right = .ok second) :
    first.mixin.isSome = second.mixin.isSome := by
  -- The common type makes the metadata-presence decision identically for both values.
  cases shape <;> exact (merkleLayout_mixed laid).trans (merkleLayout_mixed otherLaid).symm

private theorem fixedLeaf_shapes {shape : Desc} {left right : Value}
    {a b : Bytes} {first second : MerkleLayout}
    (leftBytes : serialize shape left = .ok a) (rightBytes : serialize shape right = .ok b)
    (sizes : a.size = b.size)
    (laid : fixedLeaf shape left = .ok first) (other : fixedLeaf shape right = .ok second) :
    first.limit = second.limit ∧ first.leaves.shapes = second.leaves.shapes := by
  -- Equal encoded byte lengths round up to equal packed-node counts and hence equal capacities.
  simp only [fixedLeaf, leftBytes, rightBytes, Bind.bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at laid other
  subst first second
  simp [MerkleLayout.packing, Leaves.shapes, packBytes_size, sizes]

private theorem zip_shapes {fields : List Desc} {left right : List Value}
    (first : fields.length = left.length) (second : fields.length = right.length) :
    (fields.zip left).map Prod.fst = (fields.zip right).map Prod.fst := by
  -- Pairing every field with one value preserves the complete field-type sequence.
  rw [List.map_fst_zip (by omega), List.map_fst_zip (by omega)]

/--
A fixed type and equal mixing words align all packed or nested leaf positions.
Variable-size counts must fit in 256 bits so that equal words imply equal counts.
-/
theorem merkleLayout_shapes {shape : Desc} {left right : Value} {first second : MerkleLayout}
    (sound : shape.wellFormed = .ok ()) (leftFits : Fits shape left) (rightFits : Fits shape right)
    (leftSized : CommitmentSized shape left) (rightSized : CommitmentSized shape right)
    (laid : merkleLayout shape left = .ok first)
    (other : merkleLayout shape right = .ok second) (mixed : first.mixin = second.mixin) :
    first.limit = second.limit ∧ first.leaves.shapes = second.leaves.shapes := by
  -- Fixed counts come from the type, while variable counts and union selections come from exact mixing words.
  cases shape with
  -- Either boolean occupies one encoded byte before zero padding.
  | bool =>
    match leftFits, rightFits with
    | .bool b, .bool c =>
      exact fixedLeaf_shapes (a := #[if b then 1 else 0]) (b := #[if c then 1 else 0])
        (by simp [serialize]) (by simp [serialize]) rfl laid other
  -- Every admissible integer uses exactly its declared byte width.
  | uint width =>
    match leftFits, rightFits with
    | .uint (n := n) bound, .uint (n := m) otherBound =>
      exact fixedLeaf_shapes (a := uintBytes width n) (b := uintBytes width m)
        (by simp [serialize, bound]) (by simp [serialize, otherBound])
        (by simp [uintBytes_size]) laid other
  -- Both payload lengths equal the fixed byte count declared by the type.
  | byteVector length =>
    match leftFits, rightFits with
    | .byteVector count, .byteVector otherCount =>
      simp only [merkleLayout, count, otherCount, bne_self_eq_false, Bool.false_eq_true,
        ite_false, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at laid other
      subst first second
      simp [MerkleLayout.packing, Leaves.shapes, packBytes_size, count, otherCount]
  -- Exact 256-bit length words recover the byte counts needed to align packed nodes.
  | byteList limit =>
    match leftFits, rightFits, leftSized, rightSized with
    | .byteList within, .byteList otherWithin, .byteList count, .byteList otherCount =>
      simp only [merkleLayout, Nat.not_lt.mpr within, Nat.not_lt.mpr otherWithin,
        ite_false, pure, Except.pure, Except.ok.injEq] at laid other
      subst first second
      -- The count bounds exclude truncation when the equal 256-bit words are decoded.
      have sizes := lengthWord_injective count otherCount (Option.some.inj mixed)
      simp [MerkleLayout.packing, Leaves.shapes, packBytes_size, sizes]
  -- Both bit counts equal the fixed count declared by the type.
  | bitVector length =>
    match leftFits, rightFits with
    | .bitVector count, .bitVector otherCount =>
      simp only [merkleLayout, count, otherCount, bne_self_eq_false, Bool.false_eq_true,
        ite_false, pure, Except.pure, Except.ok.injEq] at laid other
      subst first second
      simp [MerkleLayout.packing, Leaves.shapes, packedBits, packBytes_size, packBits, count, otherCount]
  -- The mixing word authenticates the bit count, including trailing zero bits.
  | bitList limit =>
    match leftFits, rightFits, leftSized, rightSized with
    | .bitList within, .bitList otherWithin, .bitList count, .bitList otherCount =>
      simp only [merkleLayout, Nat.not_lt.mpr within, Nat.not_lt.mpr otherWithin,
        ite_false, pure, Except.pure, Except.ok.injEq] at laid other
      subst first second
      -- The count bounds exclude truncation when the equal 256-bit words are decoded.
      have sizes := lengthWord_injective count otherCount (Option.some.inj mixed)
      simp [MerkleLayout.packing, Leaves.shapes, packedBits, packBytes_size, packBits, sizes]
  -- An exact bit count fixes the progressive spine's stored node count, bound or none.
  | progressiveBitList =>
    match leftFits, rightFits, leftSized, rightSized with
    | .progressiveBitList within, .progressiveBitList otherWithin, .progressiveBitList count,
        .progressiveBitList otherCount =>
      simp only [merkleLayout, boundCheck_of_withinBound _ _ within,
        boundCheck_of_withinBound _ _ otherWithin, Bind.bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at laid other
      subst first second
      -- The count bounds exclude truncation when the equal 256-bit words are decoded.
      have sizes := lengthWord_injective count otherCount (Option.some.inj mixed)
      simp [MerkleLayout.packing, Leaves.shapes, packedBits, packBytes_size, packBits, sizes]
  -- Both element counts equal the fixed count declared by the type.
  | vector element length =>
    match leftFits, rightFits with
    | .vector count each, .vector otherCount otherEach =>
      simp only [merkleLayout, count, otherCount, bne_self_eq_false, Bool.false_eq_true,
        ite_false] at laid other
      exact sequenceLayout_shapes (count.trans otherCount.symm) each otherEach laid other
  -- An exact element count determines the packing or typed positions beneath the list root.
  | list element limit =>
    match leftFits, rightFits, leftSized, rightSized with
    | .list within each, .list otherWithin otherEach, .list count _, .list otherCount _ =>
      simp only [merkleLayout, Nat.not_lt.mpr within, Nat.not_lt.mpr otherWithin, ite_false] at laid other
      -- The sequence layout keeps the supplied length word unchanged in its metadata.
      have words : lengthWord _ = lengthWord _ := Option.some.inj
        ((sequenceLayout_mixin laid).symm.trans (mixed.trans (sequenceLayout_mixin other)))
      -- Recover equal counts from the words before aligning packed or nested leaves.
      exact sequenceLayout_shapes (lengthWord_injective count otherCount words) each otherEach laid other
  -- The mixing word aligns progressive element lists by their actual counts.
  | progressiveList element =>
    match leftFits, rightFits, leftSized, rightSized with
    | .progressiveList within each, .progressiveList otherWithin otherEach, .progressiveList count _,
        .progressiveList otherCount _ =>
      simp only [merkleLayout, boundCheck_of_withinBound _ _ within,
        boundCheck_of_withinBound _ _ otherWithin, Bind.bind, Except.bind] at laid other
      -- The sequence layout keeps the supplied length word unchanged in its metadata.
      have words : lengthWord _ = lengthWord _ := Option.some.inj
        ((sequenceLayout_mixin laid).symm.trans (mixed.trans (sequenceLayout_mixin other)))
      -- Recover equal counts from the words before aligning packed or nested leaves.
      exact sequenceLayout_shapes (lengthWord_injective count otherCount words) each otherEach laid other
  -- Ordinary containers retain exactly one position for every declared field.
  | container names fields =>
    match leftFits, rightFits with
    | .container paired _, .container otherPaired _ =>
      simp only [merkleLayout, paired, bne_self_eq_false, Bool.false_eq_true,
        ite_false, pure, Except.pure, Except.ok.injEq] at laid
      simp only [merkleLayout, otherPaired, bne_self_eq_false, Bool.false_eq_true,
        ite_false, pure, Except.pure, Except.ok.injEq] at other
      subst first second
      -- Projecting paired fields back to their types removes the values without losing positions.
      exact ⟨congrArg some (paired.symm.trans otherPaired), congrArg Sum.inr (by
        simpa only [List.map_map, Function.comp_def, Option.map_some] using
          congrArg (List.map some) (zip_shapes paired otherPaired))⟩
  -- A well-formed active-field mask has exactly enough occupied positions for the declared fields.
  | progressiveContainer active names fields =>
    match leftFits, rightFits with
    | .progressiveContainer (values := values) paired _,
        .progressiveContainer (values := others) otherPaired _ =>
      -- Both values can be placed into the same active positions, including gaps between fields.
      obtain ⟨slots, placed⟩ := placeSlots_exists active (fields.zip values)
        (by simp [progressive_count sound, paired])
      obtain ⟨otherSlots, otherPlaced⟩ := placeSlots_exists active (fields.zip others)
        (by simp [progressive_count sound, otherPaired])
      simp [merkleLayout, layoutSlots, paired, progressive_count sound, placed,
        Bind.bind, Except.bind, pure, Except.pure] at laid
      simp only [merkleLayout, bind, Except.bind, layoutSlots, otherPaired, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte, progressive_count sound, otherPlaced, pure, Except.pure,
        Except.ok.injEq] at other
      subst first second
      -- The common mask and common field-type sequence determine identical nested leaf shapes.
      exact ⟨rfl, congrArg Sum.inr (placeSlots_shapes (zip_shapes paired otherPaired)
        placed otherPlaced)⟩
  -- The authenticated selector identifies which child type occupies the union's sole position.
  | compatibleUnion selectors options =>
    match leftFits, rightFits with
    | .compatibleUnion (selector := selector) bounded named _,
        .compatibleUnion (selector := otherSelector) otherBounded otherNamed _ =>
      simp only [merkleLayout, bind, Except.bind, named, selectorWord,
        checkSelector_of_range bounded, pure, Except.pure, Except.ok.injEq, otherNamed,
        checkSelector_of_range otherBounded] at laid other
      have top : maxSelector = 127 := rfl
      subst first second
      -- A one-byte selector always fits in the 256-bit word, so equal words recover equal selectors.
      have selectorsEqual := lengthWord_injective
        (left := selector) (right := otherSelector) (by omega) (by omega) (Option.some.inj mixed)
      subst otherSelector
      -- The same selector lookup must return the same child type on both sides.
      rw [named] at otherNamed
      cases Except.ok.inj otherNamed
      exact ⟨rfl, rfl⟩

end EthLib.Consensus.Ssz
