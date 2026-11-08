module

public import EthLib.Serialization.Proofs.Ssz.Codec.BindingChildren
public import EthLib.Serialization.Proofs.Ssz.Codec.BindingLayout
public import EthLib.Serialization.Proofs.Ssz.Codec.BindingLayoutInjectivity
public import EthLib.Serialization.Proofs.Ssz.Codec.BindingLeaves
public import EthLib.Serialization.Proofs.Ssz.Codec.BindingShape

/-!
Two values of one type with one root are equal, or a search finds a SHA-256 collision.

The same holds for any hash with 32-byte digests, with the zero subtrees computed by that hash.

The search reads only the hash inputs of the two root computations.
-/

@[expose] public section

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
theorem valueTreeAt_eq_of_noCollision {hash : ByteArray → ByteArray} (budget : Nat)
    {shape : Desc} {left right : Value}
    {first second : CommitmentTree} (enough : shape.nesting ≤ budget)
    (sound : shape.wellFormed = .ok ()) (leftFits : Fits shape left) (rightFits : Fits shape right)
    (leftSized : CommitmentSized shape left) (rightSized : CommitmentSized shape right)
    (leftTrace : valueTreeAt budget shape left = .ok first)
    (rightTrace : valueTreeAt budget shape right = .ok second)
    (clean : NoCollision first second hash) (same : first.root hash = second.root hash)
    (width : ∀ x, (hash x).size = 32 := by exact EthLib.Cryptography.Hash.Sha256.hash_size) :
    left = right := by
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
      leftComplete rightComplete clean same width
    -- The common type and exact mixing word determine the capacity and every child type.
    have skeleton := merkleLayout_shapes sound leftFits rightFits leftSized rightSized
      laid otherLaid mixed.1
    -- Any collision inside the contents would also belong to the enclosing computations.
    have contentClean :=
      clean.restrict (withMixin_included _ _ hash) (withMixin_included _ _ hash)
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
          aTrace bTrace collisionFree roots) width
    -- Equal leaves, capacity, and mixing words recover the full unhashed layouts.
    have layouts := layout_ext leaves skeleton.1 mixed.1
    -- The layout rules preserve the original values once lengths and child contents are known.
    apply merkleLayout_injective sound leftFits rightFits leftSized rightSized laid
    exact otherLaid.trans (congrArg Except.ok layouts.symm)

/--
Two values of one well-formed type with one root are equal, or a search finds a collision.

The root is the one that a hash with 32-byte digests computes.

The search compares the hash inputs of the two root computations.

It returns two different 64-byte inputs with one digest, one hashed in each computation.

Every nested variable-size count must fit its 256-bit mixing word.
-/
theorem hashTreeRootM_binding (hash : ByteArray → ByteArray) (width : ∀ x, (hash x).size = 32)
    {shape : Desc} {left right : Value} {root : Bytes}
    (sound : shape.wellFormed = .ok ()) (leftFits : Fits shape left) (rightFits : Fits shape right)
    (leftSized : CommitmentSized shape left) (rightSized : CommitmentSized shape right)
    (first : (hashTreeRootM (Hasher.ofHash (m := Id) hash) shape left).run = .ok root)
    (second : (hashTreeRootM (Hasher.ofHash (m := Id) hash) shape right).run = .ok root) :
    left = right ∨ ∃ leftTree rightTree,
      valueTree shape left = .ok leftTree ∧ valueTree shape right = .ok rightTree ∧
      ∃ a b, findMessageCollision (leftTree.messages hash) (rightTree.messages hash) hash
          = some (a, b) ∧
        a ∈ leftTree.messages hash ∧ b ∈ rightTree.messages hash ∧ MessageCollision a b hash := by
  -- Expand both roots into finite computations with the same results.
  obtain ⟨leftTree, leftTrace, leftRoot, leftComplete⟩ :=
    valueTree_of_hashTreeRootM hash _ _ _ first
  obtain ⟨rightTree, rightTrace, rightRoot, rightComplete⟩ :=
    valueTree_of_hashTreeRootM hash _ _ _ second
  cases found : findMessageCollision (leftTree.messages hash) (rightTree.messages hash) hash with
  | none =>
    -- No collision between the computations: structural recovery gives equal values.
    refine .inl (valueTreeAt_eq_of_noCollision shape.nesting (Nat.le_refl _) sound
      leftFits rightFits leftSized rightSized leftTrace rightTrace ?_
      (leftRoot.trans rightRoot.symm) width)
    -- Every message of a complete computation has 64 bytes, so the search would see a collision.
    rintro ⟨a, aMember, b, bMember, different, hashed⟩
    exact findMessageCollision_eq_none_iff.mp found a aMember b bMember
      ⟨messages_size_of_width hash width leftTree leftComplete a aMember,
        messages_size_of_width hash width rightTree rightComplete b bMember, different, hashed⟩
  | some pair =>
    -- The search names the collision, with one message from each computation.
    exact .inr ⟨leftTree, rightTree, leftTrace, rightTrace, pair.1, pair.2, found,
      findMessageCollision_valid found⟩

/--
Two values of one well-formed type with one root are equal, or a search finds a collision.

The search compares the hash inputs of the two root computations.

It returns two different 64-byte inputs with one SHA-256 digest, one hashed in each computation.

Every nested variable-size count must fit its 256-bit mixing word.
-/
theorem hashTreeRoot_binding {shape : Desc} {left right : Value} {root : Bytes}
    (sound : shape.wellFormed = .ok ()) (leftFits : Fits shape left) (rightFits : Fits shape right)
    (leftSized : CommitmentSized shape left) (rightSized : CommitmentSized shape right)
    (first : hashTreeRoot shape left = .ok root)
    (second : hashTreeRoot shape right = .ok root) :
    left = right ∨ ∃ leftTree rightTree,
      valueTree shape left = .ok leftTree ∧ valueTree shape right = .ok rightTree ∧
      ∃ a b, findMessageCollision leftTree.messages rightTree.messages = some (a, b) ∧
        a ∈ leftTree.messages ∧ b ∈ rightTree.messages ∧ MessageCollision a b := by
  -- The specification's hasher is the one built from SHA-256 alone.
  rw [hashTreeRoot, ← ofHash_sha256] at first second
  exact hashTreeRootM_binding _ Cryptography.Hash.Sha256.hash_size sound leftFits rightFits
    leftSized rightSized first second

end EthLib.Serialization.Ssz
