import EthLib.Consensus.Proofs.Ssz.Merkle.Authentication
import EthLib.Consensus.Proofs.Ssz.Merkle.Widths

/-! Equal roots of equally shaped trees reveal equal leaves or a collision in their own hashes. -/

namespace EthLib.Consensus.Ssz

/-- A finite Merkle computation, retaining the complete nodes at its leaves. -/
inductive CommitmentTree where
  /-- A complete node is already a commitment at this boundary. -/
  | leaf (node : Bytes)
  /-- A parent records both child computations, not only their resulting digests. -/
  | fork (left right : CommitmentTree)
  deriving DecidableEq

namespace CommitmentTree

/-- Execute precisely the binary hashes recorded by the tree. -/
def root : CommitmentTree → Bytes
  -- Leaves already contain nodes.
  -- Each fork hashes the two child roots in left-to-right order.
  | .leaf node => node
  | .fork left right => combine left.root right.root

/-- Inputs of all binary hashes in the computation, including its root hash. -/
def messages : CommitmentTree → List Bytes
  -- The parent hashes its two roots, and each child contributes its own internal hash inputs.
  | .leaf _ => []
  | .fork left right => (left.root ++ right.root) :: (left.messages ++ right.messages)

/-- Every leaf is a complete SSZ node. -/
def Complete : CommitmentTree → Prop
  -- Leaf width is the only requirement because every internal SHA-256 digest has width 32.
  | .leaf node => node.size = bytesPerChunk
  | .fork left right => left.Complete ∧ right.Complete

/-- Trees have the same branch structure, independently of their leaf contents. -/
def SameShape : CommitmentTree → CommitmentTree → Prop
  -- Only branching positions matter here.
  -- Leaf contents may differ.
  | .leaf _, .leaf _ => True
  | .fork left right, .fork otherLeft otherRight =>
      SameShape left otherLeft ∧ SameShape right otherRight
  | _, _ => False

/-- A collision occurs between messages actually hashed in the two computations. -/
def Collision (left right : CommitmentTree) : Prop :=
  -- Both witnesses must belong to these computations, excluding unrelated hash collisions.
  ∃ first ∈ left.messages, ∃ second ∈ right.messages,
    first ≠ second ∧ Cryptography.Hash.Sha256.hash (ByteArray.mk first) = Cryptography.Hash.Sha256.hash (ByteArray.mk second)

/-- Every complete computation has a complete root node. -/
@[simp] theorem root_size (tree : CommitmentTree) (complete : tree.Complete) :
    tree.root.size = bytesPerChunk := by
  -- A leaf inherits its assumed width, while an internal root inherits the digest width.
  cases tree with
  | leaf node => exact complete
  | fork left right => exact combine_size _ _

/-- Every recorded compression input consists of exactly two complete nodes. -/
theorem messages_size (tree : CommitmentTree) (complete : tree.Complete) :
    ∀ message ∈ tree.messages, message.size = 2 * bytesPerChunk := by
  -- Every message is either two complete child roots or a message already covered in a child.
  induction tree with
  | leaf node => simp [messages]
  | fork left right ihLeft ihRight =>
    intro message member
    simp only [messages, List.mem_cons, List.mem_append] at member
    rcases member with rfl | member | member
    · simp [root_size left complete.1, root_size right complete.2, Nat.two_mul]
    · exact ihLeft complete.1 _ member
    · exact ihRight complete.2 _ member

/-- Equal parent roots either preserve both children or expose their distinct hash inputs. -/
theorem fork_binding {left right otherLeft otherRight : CommitmentTree}
    (complete : (fork left right).Complete)
    (otherComplete : (fork otherLeft otherRight).Complete)
    (same : (fork left right).root = (fork otherLeft otherRight).root) :
    (left.root = otherLeft.root ∧ right.root = otherRight.root) ∨
      Collision (.fork left right) (.fork otherLeft otherRight) := by
  -- Two equal 64-byte concatenations split uniquely at byte 32.
  -- Unequal ones witness a collision.
  by_cases inputs : left.root ++ right.root = otherLeft.root ++ otherRight.root
  · exact .inl (Array.append_inj inputs ((root_size _ complete.1).trans
      (root_size _ otherComplete.1).symm))
  · exact .inr ⟨_, List.mem_cons_self, _, List.mem_cons_self, inputs, ByteArray.ext same⟩

/-- A collision in the left subcomputations remains a collision in the full trees. -/
theorem Collision.left {left otherLeft : CommitmentTree} (right otherRight : CommitmentTree)
    (collision : Collision left otherLeft) :
    Collision (.fork left right) (.fork otherLeft otherRight) := by
  -- The left subtree keeps both witnesses when its message list is included in the larger tree.
  obtain ⟨first, firstMem, second, secondMem, rest⟩ := collision
  exact ⟨first, by simp [messages, firstMem], second, by simp [messages, secondMem], rest⟩

/-- A collision in the right subcomputations remains a collision in the full trees. -/
theorem Collision.right {right otherRight : CommitmentTree} (left otherLeft : CommitmentTree)
    (collision : Collision right otherRight) :
    Collision (.fork left right) (.fork otherLeft otherRight) := by
  -- The right subtree keeps both witnesses when its message list is included in the larger tree.
  obtain ⟨first, firstMem, second, secondMem, rest⟩ := collision
  exact ⟨first, by simp [messages, firstMem], second, by simp [messages, secondMem], rest⟩

/-- A fixed tree shape commits to every leaf unless its own hash computations collide. -/
theorem binding (left right : CommitmentTree) (complete : left.Complete)
    (otherComplete : right.Complete) (shape : SameShape left right)
    (same : left.root = right.root) : left = right ∨ Collision left right := by
  -- Compare the root inputs first, then repeat only in children whose roots remain equal.
  induction left generalizing right with
  | leaf node =>
    cases right with
    | leaf other => exact .inl (congrArg leaf same)
    | fork otherLeft otherRight => exact False.elim shape
  | fork a b ihA ihB =>
    cases right with
    | leaf node => exact False.elim shape
    | fork c d =>
      rcases fork_binding complete otherComplete same with equal | collision
      · rcases ihA c complete.1 otherComplete.1 shape.1 equal.1 with rfl | collision
        · rcases ihB d complete.2 otherComplete.2 shape.2 equal.2 with rfl | collision
          · exact .inl rfl
          · exact .inr (collision.right a a)
        · exact .inr (collision.left b d)
      · exact .inr collision

/-- A perfect subtree with its padded leaves made explicit. -/
def perfect : Nat → (Nat → Bytes) → CommitmentTree
  -- At each fork the right leaf supply starts one half-width after the left supply.
  | 0, leaves => .leaf (leaves 0)
  | depth + 1, leaves => .fork (perfect depth leaves)
      (perfect depth fun i => leaves (i + 2 ^ depth))

/-- An expanded perfect tree evaluates to the same recursively defined root. -/
@[simp] theorem perfect_root (depth : Nat) (leaves : Nat → Bytes) :
    (perfect depth leaves).root = subtreeRoot combine depth leaves := by
  -- Both descriptions split at the same half-width and hash the same child roots.
  induction depth generalizing leaves with
  | zero => rfl
  | succ depth ih => simp [perfect, root, subtreeRoot, ih]

/-- Expanding cached zero subtrees gives exactly the executable bounded-tree root. -/
theorem perfect_subtreeAt (chunks : Array Bytes) (depth start : Nat) :
    (perfect depth fun i => padded zeroChunk chunks (start + i)).root =
      subtreeAt chunks depth start := by
  -- The zero-subtree equivalence replaces cache lookups by their full mathematical expansion.
  rw [perfect_root, subtreeAt_eq_subtreeRoot]

/-- Two perfect trees of the same depth always have the same branch structure. -/
theorem perfect_shape (depth : Nat) (left right : Nat → Bytes) :
    SameShape (perfect depth left) (perfect depth right) := by
  -- The depth alone fixes every fork, independently of the supplied leaf bytes.
  induction depth generalizing left right with
  | zero => trivial
  | succ depth ih => exact ⟨ih _ _, ih _ _⟩

/-- Complete leaf supplies give a complete perfect tree. -/
theorem perfect_complete (depth : Nat) (leaves : Nat → Bytes)
    (complete : ∀ i, i < 2 ^ depth → (leaves i).size = bytesPerChunk) :
    (perfect depth leaves).Complete := by
  -- Each half inherits complete leaves from its own half of the original bounded interval.
  induction depth generalizing leaves with
  | zero => exact complete 0 (by decide)
  | succ depth ih =>
    refine ⟨ih _ (fun i bound => complete i (by rw [Nat.pow_succ]; omega)),
      ih _ (fun i bound => complete (i + 2 ^ depth) (by rw [Nat.pow_succ]; omega))⟩

/-- Equal expanded perfect trees have equal leaf supplies throughout their width. -/
theorem perfect_injective (depth : Nat) {left right : Nat → Bytes}
    (same : perfect depth left = perfect depth right) :
    ∀ i, i < 2 ^ depth → left i = right i := by
  -- Choose the half containing the requested leaf and repeat at one smaller depth.
  induction depth generalizing left right with
  | zero =>
    intro i within
    obtain rfl := Nat.lt_one_iff.mp within
    exact CommitmentTree.leaf.inj same
  | succ depth ih =>
    obtain ⟨first, second⟩ := CommitmentTree.fork.inj same
    intro i within
    by_cases before : i < 2 ^ depth
    · exact ih first i before
    · have after := ih second (i - 2 ^ depth) (by rw [Nat.pow_succ] at within; omega)
      simpa [Nat.sub_add_cancel (Nat.le_of_not_gt before)] using after

end CommitmentTree
end EthLib.Consensus.Ssz
