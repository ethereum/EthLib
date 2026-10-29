import EthLib.Serialization.Proofs.Ssz.Codec.BindingChildren
import EthLib.Serialization.Proofs.Ssz.Codec.BindingLayout
import EthLib.Serialization.Proofs.Ssz.Codec.BindingLayoutInjectivity
import EthLib.Serialization.Proofs.Ssz.Codec.BindingLeaves
import EthLib.Serialization.Proofs.Ssz.Codec.BindingShape

/-! Whole-value binding reduces conflicting same-type SSZ commitments to a concrete SHA-256 collision. -/

namespace EthLib.Serialization.Ssz
open CommitmentTree

/-- Equal fields, capacity, and mixing words describe the same complete layout. -/
private theorem layout_ext {left right : MerkleLayout}
    (leaves : left.leaves = right.leaves) (limit : left.limit = right.limit)
    (mixin : left.mixin = right.mixin) : left = right := by
  -- A layout carries only its leaves, capacity, and optional mixing word.
  cases left
  cases right
  simp_all

/--
Without a collision between the two computations, an SSZ root determines its whole value.
Counts are checked before comparing variable-shaped subtrees, and nested values use the same argument.
-/
theorem valueTreeAt_eq_of_noCollision (budget : Nat) {shape : Desc} {left right : Value}
    {first second : CommitmentTree} (enough : shape.nesting ≤ budget)
    (sound : shape.wellFormed = .ok ()) (leftFits : Fits shape left) (rightFits : Fits shape right)
    (leftSized : CommitmentSized shape left) (rightSized : CommitmentSized shape right)
    (leftTrace : valueTreeAt budget shape left = .ok first)
    (rightTrace : valueTreeAt budget shape right = .ok second)
    (clean : NoCollision first second) (same : first.root = second.root) : left = right := by
  -- The recursion budget decreases whenever a leaf contains another SSZ value.
  induction budget generalizing shape left right first second with
  | zero => simp [valueTreeAt] at leftTrace
  | succ budget ih =>
    -- Both computations contain complete 32-byte nodes, so each parent input splits unambiguously.
    have leftComplete := (valueTreeAt_complete enough sound leftFits leftTrace).1
    have rightComplete := (valueTreeAt_complete enough sound rightFits rightTrace).1
    -- Expose the leaves and mixing words chosen by the actual layout rules.
    obtain ⟨leftLayout, leftTrees, laid, leftMaterialized, leftRoom, rfl⟩ := valueTreeAt_view leftTrace
    obtain ⟨rightLayout, rightTrees, otherLaid, rightMaterialized, rightRoom, rfl⟩ := valueTreeAt_view rightTrace
    -- Authenticate the count or selector before deciding how the underlying trees align.
    have mixed := withMixin_comparison (merkleLayout_mixin_presence laid otherLaid)
      leftComplete rightComplete clean same
    -- The common type and exact mixing word determine the capacity and every child type.
    have skeleton := merkleLayout_shapes sound leftFits rightFits leftSized rightSized
      laid otherLaid mixed.1
    -- Any collision inside the contents would also belong to the enclosing computations.
    have contentClean := clean.restrict (withMixin_included _ _) (withMixin_included _ _)
    -- Equal contents roots now preserve packed nodes or corresponding nested values.
    have leaves := layout_leaves_eq_of_noCollision skeleton.2 skeleton.1
      leftMaterialized rightMaterialized leftRoom rightRoom
      (withMixin_complete leftComplete) (withMixin_complete rightComplete)
      contentClean mixed.2 (by
        intro leftSlots rightSlots child a b ta tb leftNested rightNested leftMember rightMember
          aTrace bTrace roots collisionFree
        -- Every occupied position inherits admissibility and a well-formed child type.
        have aValid := merkleLayout_child_fits sound leftFits laid leftNested leftMember
        have bValid := merkleLayout_child_fits sound rightFits otherLaid rightNested rightMember
        -- Nested variable-size values also retain exact 256-bit counts.
        have aSized := merkleLayout_child_sized leftSized laid leftNested leftMember
        have bSized := merkleLayout_child_sized rightSized otherLaid rightNested rightMember
        -- A child type is strictly shallower, leaving enough budget for its binding proof.
        have smaller := merkleLayout_child_nesting shape left leftLayout laid leftSlots
          leftNested child a leftMember
        exact ih (by omega) aValid.2 aValid.1 bValid.1 aSized bSized
          aTrace bTrace collisionFree roots)
    -- Equal leaves, capacity, and mixing words recover the full unhashed layouts.
    have layouts := layout_ext leaves skeleton.1 mixed.1
    -- The layout rules preserve the original values once lengths and child contents are known.
    apply merkleLayout_injective sound leftFits rightFits leftSized rightSized laid
    exact otherLaid.trans (congrArg Except.ok layouts.symm)

/--
Conflicting values of the same well-formed type expose a collision in their expanded SSZ computations.
Every nested variable-size count must fit its 256-bit mixing word.
The witnesses are distinct 64-byte inputs with the same SHA-256 digest.
-/
theorem hashTreeRoot_binding {shape : Desc} {left right : Value} {root : Bytes}
    (sound : shape.wellFormed = .ok ()) (leftFits : Fits shape left) (rightFits : Fits shape right)
    (leftSized : CommitmentSized shape left) (rightSized : CommitmentSized shape right)
    (first : hashTreeRoot shape left = .ok root)
    (second : hashTreeRoot shape right = .ok root) :
    left = right ∨ ∃ leftTree rightTree,
      valueTree shape left = .ok leftTree ∧ valueTree shape right = .ok rightTree ∧
      ∃ a ∈ leftTree.messages, ∃ b ∈ rightTree.messages,
        a.size = 2 * bytesPerChunk ∧ b.size = 2 * bytesPerChunk ∧ a ≠ b ∧
        Cryptography.Hash.Sha256.hash (ByteArray.mk a) = Cryptography.Hash.Sha256.hash (ByteArray.mk b) := by
  -- Expand both executable roots into finite computations with the same results.
  obtain ⟨leftTree, leftTrace, leftRoot, leftComplete⟩ := valueTree_of_hashTreeRoot _ _ _ first
  obtain ⟨rightTree, rightTrace, rightRoot, rightComplete⟩ := valueTree_of_hashTreeRoot _ _ _ second
  -- Either the computations contain a conflicting hash pair, or structural recovery gives equal values.
  by_cases clean : NoCollision leftTree rightTree
  · exact .inl (valueTreeAt_eq_of_noCollision shape.nesting (Nat.le_refl _) sound
      leftFits rightFits leftSized rightSized leftTrace rightTrace clean
      (leftRoot.trans rightRoot.symm))
  · -- The collision witnesses come from the two computations rather than unrelated SHA-256 inputs.
    obtain ⟨a, aMember, b, bMember, different, hashed⟩ : Collision leftTree rightTree :=
      Classical.not_not.mp clean
    -- Each witnessed message concatenates two 32-byte child nodes.
    exact .inr ⟨leftTree, rightTree, leftTrace, rightTrace, a, aMember, b, bMember,
      messages_size leftTree leftComplete a aMember,
      messages_size rightTree rightComplete b bMember, different, hashed⟩

end EthLib.Serialization.Ssz
