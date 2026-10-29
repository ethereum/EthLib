import EthLib.Consensus.Proofs.Ssz.Codec.BindingDomain
import EthLib.Consensus.Proofs.Ssz.Codec.RootDomain

/-! Admissibility and count bounds descend to the children that a layout actually selects. -/

namespace EthLib.Consensus.Ssz

/-- Every occupied layout position retains a well-formed type and an admissible value. -/
theorem merkleLayout_child_fits {shape : Desc} {value : Value} {layout : MerkleLayout}
    (sound : shape.wellFormed = .ok ()) (fitted : Fits shape value)
    (laid : merkleLayout shape value = .ok layout)
    {slots : List (Option (Desc × Value))} (nested : layout.leaves = .nested slots)
    {child : Desc} {inner : Value} (member : some (child, inner) ∈ slots) :
    Fits child inner ∧ child.wellFormed = .ok () := by
  -- Admissibility supplies a layout whose occupied positions contain well-formed admissible children.
  obtain ⟨expected, generated, valid⟩ := layout_exists fitted sound
  -- The deterministic layout operation identifies that admissible layout with the selected one.
  rw [laid] at generated
  cases Except.ok.inj generated
  -- The selected occupied position inherits the layout's child guarantee.
  exact (nested ▸ valid.1) child inner member

private theorem sequence_child_sized {element : Desc} {values : List Value}
    {positions : Option Nat} {mixin : Option Bytes} {layout : MerkleLayout}
    (each : ∀ value ∈ values, CommitmentSized element value)
    (laid : sequenceLayout element values positions mixin = .ok layout)
    {slots : List (Option (Desc × Value))} (nested : layout.leaves = .nested slots)
    {child : Desc} {inner : Value} (member : some (child, inner) ∈ slots) :
    CommitmentSized child inner := by
  -- Basic elements are packed bytes, so they cannot supply a nested child position.
  unfold sequenceLayout at laid
  split at laid
  · cases wrote : serializeEach element values <;>
      simp [wrote, Bind.bind, Except.bind, pure, Except.pure] at laid
    subst layout
    cases nested
  · simp only [pure, Except.pure, Except.ok.injEq] at laid
    subst layout
    simp only [MerkleLayout.nesting, Leaves.nested.injEq] at nested
    subst slots
    -- Every remaining occupied position is one original element with the shared element type.
    simp only [List.mem_map, Option.some.injEq, Prod.mk.injEq] at member
    obtain ⟨item, member, rfl, rfl⟩ := member
    exact each item member

/-- Count representability follows every occupied child of the actual Merkle layout. -/
theorem merkleLayout_child_sized {shape : Desc} {value : Value} {layout : MerkleLayout}
    (sized : CommitmentSized shape value) (laid : merkleLayout shape value = .ok layout)
    {slots : List (Option (Desc × Value))} (nested : layout.leaves = .nested slots)
    {child : Desc} {inner : Value} (member : some (child, inner) ∈ slots) :
    CommitmentSized child inner := by
  -- Scalar and packed layouts have no nested children, leaving only sequences, fields, and union options.
  cases sized <;>
    simp only [merkleLayout, fixedLeaf, Bind.bind, Except.bind] at laid
  all_goals try solve
    | cases wrote : serialize _ _ <;>
        simp [pure, Except.pure] at laid
    | split at laid <;>
        simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq, pure, Except.pure,
          Except.ok.injEq] at laid
      subst layout
      cases nested
  -- A fixed-length sequence retains the count bounds carried by each element.
  case vector element length values each =>
    split at laid
    · cases laid
    · exact sequence_child_sized each laid nested member
  -- A bounded list retains its elements' nested count bounds after its own length check.
  case list element limit values count each =>
    split at laid
    · cases laid
    · exact sequence_child_sized each laid nested member
  -- A progressive list changes the tree shape without changing its elements' count bounds.
  case progressiveList element limit values count each =>
    cases checked : boundCheck limit values.length <;>
      simp only [checked, reduceCtorEq] at laid
    exact sequence_child_sized each laid nested member
  -- Each ordinary container position is one declared field paired with its value.
  case container names fields values each =>
    split at laid
    · cases laid
    · simp only [pure, Except.pure, Except.ok.injEq] at laid
      subst layout
      simp only [MerkleLayout.nesting, Leaves.nested.injEq] at nested
      subst slots
      simp only [List.mem_map, Option.some.injEq] at member
      obtain ⟨pair, member, rfl⟩ := member
      exact each (child, inner) member
  -- Progressive containers insert zero gaps while preserving all declared field-value pairs.
  case progressiveContainer active names fields values each =>
    cases placed : layoutSlots active fields values with
    | error fault => simp [placed] at laid
    | ok actual =>
      simp only [placed, pure, Except.pure, Except.ok.injEq] at laid
      subst layout
      simp only [MerkleLayout.nesting, Leaves.nested.injEq] at nested
      subst slots
      unfold layoutSlots at placed
      split at placed
      · cases placed
      · dsimp only at placed
        split at placed
        · cases placed
        -- Removing gaps recovers the original field sequence, so each occupied slot inherits its field bound.
        · exact each (child, inner)
            (placeSlots_fields placed ▸ List.mem_filterMap.mpr ⟨_, member, rfl⟩)
  -- The selector identifies one option whose nested count bounds were already established.
  case compatibleUnion selectors options selector option value named innerSized =>
    simp only [named] at laid
    cases word : selectorWord selector with
    | error fault => simp [word] at laid
    | ok bytes =>
      simp only [word, pure, Except.pure, Except.ok.injEq] at laid
      subst layout
      simp only [MerkleLayout.nesting, Leaves.nested.injEq] at nested
      subst slots
      -- The union has exactly one occupied child position, containing the chosen option value.
      simp only [List.mem_singleton, Option.some.injEq, Prod.mk.injEq] at member
      obtain ⟨rfl, rfl⟩ := member
      exact innerSized

end EthLib.Consensus.Ssz
