module

public import EthLib.Serialization.Proofs.Ssz.Merkle.Authentication
public import EthLib.Serialization.Proofs.Ssz.Merkle.Widths

/-!
Equal roots of equally shaped trees reveal equal leaves or a collision in their own hashes.

The hash is SHA-256 unless another one is given.

The binding needs only that every digest of the hash is 32 bytes wide.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- A finite Merkle computation, retaining the complete nodes at its leaves. -/
inductive CommitmentTree where
  /-- A complete node is already a commitment at this boundary. -/
  | leaf (node : Bytes)
  /-- A parent records both child computations, not only their resulting digests. -/
  | fork (left right : CommitmentTree)
  deriving DecidableEq

/-- Two different 64-byte messages with one digest: a collision of the node hash. -/
def MessageCollision (a b : Bytes)
    (hash : ByteArray → ByteArray := Cryptography.Hash.Sha256.hash) : Prop :=
  a.size = 2 * bytesPerChunk ∧ b.size = 2 * bytesPerChunk ∧ a ≠ b ∧
    hash (ByteArray.mk a) = hash (ByteArray.mk b)

instance (a b : Bytes) (hash : ByteArray → ByteArray) :
    Decidable (MessageCollision a b hash) := by
  unfold MessageCollision
  infer_instance

/-- The first collision between a message of one list and a message of the other, if any.

It tries each message of the first list in order, against each message of the second. -/
def findMessageCollision (left right : List Bytes)
    (hash : ByteArray → ByteArray := Cryptography.Hash.Sha256.hash) : Option (Bytes × Bytes) :=
  match left with
  | [] => none
  | a :: left =>
    match right.find? fun b => decide (MessageCollision a b hash) with
    | some b => some (a, b)
    | none => findMessageCollision left right hash

/-- The search returns a collision, with one message from each list. -/
theorem findMessageCollision_valid {hash : ByteArray → ByteArray} :
    ∀ {left right : List Bytes} {a b : Bytes}, findMessageCollision left right hash = some (a, b) →
      a ∈ left ∧ b ∈ right ∧ MessageCollision a b hash
  | [], _, _, _, found => by cases found
  | c :: left, right, a, b, found => by
    unfold findMessageCollision at found
    split at found
    · -- The first message collides with a message of the other list.
      rename_i other hfind
      cases found
      have hother := List.find?_some hfind
      exact ⟨List.mem_cons_self, List.mem_of_find?_eq_some hfind, of_decide_eq_true hother⟩
    · -- The collision starts later in the first list.
      obtain ⟨member, rest⟩ := findMessageCollision_valid found
      exact ⟨List.mem_cons_of_mem _ member, rest⟩

/-- The search comes back empty exactly when no two messages of the lists collide. -/
theorem findMessageCollision_eq_none_iff {hash : ByteArray → ByteArray} :
    ∀ {left right : List Bytes}, findMessageCollision left right hash = none ↔
      ∀ a ∈ left, ∀ b ∈ right, ¬ MessageCollision a b hash
  | [], _ => by simp [findMessageCollision]
  | c :: left, right => by
    unfold findMessageCollision
    split
    · -- A collision of the first message makes the search return it.
      rename_i other hfind
      have hother := List.find?_some hfind
      simp only [reduceCtorEq, false_iff]
      exact fun clean => clean c List.mem_cons_self other (List.mem_of_find?_eq_some hfind)
        (of_decide_eq_true hother)
    · rename_i hfind
      rw [findMessageCollision_eq_none_iff]
      simp only [List.mem_cons, forall_eq_or_imp, iff_and_self]
      intro _ b member
      simpa using List.find?_eq_none.mp hfind b member

/-- Any collision between the two lists makes the search return one. -/
theorem findMessageCollision_of_collision {hash : ByteArray → ByteArray}
    {left right : List Bytes} {a b : Bytes}
    (aMember : a ∈ left) (bMember : b ∈ right) (collision : MessageCollision a b hash) :
    ∃ a b, findMessageCollision left right hash = some (a, b) := by
  cases found : findMessageCollision left right hash with
  | none => exact absurd collision (findMessageCollision_eq_none_iff.mp found a aMember b bMember)
  | some pair => exact ⟨pair.1, pair.2, rfl⟩

/-- A list with no collision among its own messages yields none against itself.

So the search can fail, and a theorem that returns it is not true by default. -/
theorem findMessageCollision_self {hash : ByteArray → ByteArray} {messages : List Bytes}
    (clean : ∀ a ∈ messages, ∀ b ∈ messages, ¬ MessageCollision a b hash) :
    findMessageCollision messages messages hash = none :=
  findMessageCollision_eq_none_iff.mpr clean

/-- Folding two nodes with SHA-256 in the identity monad is the specification's fold. -/
@[simp] theorem combineM_sha256 (left right : Bytes) :
    (combineM (m := Id) Cryptography.Hash.Sha256.hash left right).run = combine left right :=
  rfl

namespace CommitmentTree

/-- Execute precisely the binary hashes recorded by the tree. -/
def root (tree : CommitmentTree)
    (hash : ByteArray → ByteArray := Cryptography.Hash.Sha256.hash) : Bytes :=
  match tree with
  -- Leaves already contain nodes.
  -- Each fork hashes the two child roots in left-to-right order.
  | .leaf node => node
  | .fork left right => (combineM (m := Id) hash (left.root hash) (right.root hash)).run

/-- Inputs of all binary hashes in the computation, including its root hash. -/
def messages (tree : CommitmentTree)
    (hash : ByteArray → ByteArray := Cryptography.Hash.Sha256.hash) : List Bytes :=
  match tree with
  -- The parent hashes its two roots, and each child contributes its own internal hash inputs.
  | .leaf _ => []
  | .fork left right =>
    (left.root hash ++ right.root hash) :: (left.messages hash ++ right.messages hash)

/-- Every leaf is a complete SSZ node. -/
def Complete : CommitmentTree → Prop
  -- Leaf width is the only requirement because every internal digest has width 32.
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
def Collision (left right : CommitmentTree)
    (hash : ByteArray → ByteArray := Cryptography.Hash.Sha256.hash) : Prop :=
  -- Both witnesses must belong to these computations, excluding unrelated hash collisions.
  ∃ first ∈ left.messages hash, ∃ second ∈ right.messages hash,
    first ≠ second ∧ hash (ByteArray.mk first) = hash (ByteArray.mk second)

/-- Every complete computation has a complete root node, when every digest has 32 bytes. -/
@[simp] theorem root_size (tree : CommitmentTree) (complete : tree.Complete)
    (hash : ByteArray → ByteArray := Cryptography.Hash.Sha256.hash)
    (width : ∀ x, (hash x).size = 32 := by exact EthLib.Cryptography.Hash.Sha256.hash_size) :
    (tree.root hash).size = bytesPerChunk := by
  -- A leaf inherits its assumed width, while an internal root inherits the digest width.
  cases tree with
  | leaf node => exact complete
  | fork left right => exact width _

/-- Every compression input is two complete nodes, when every digest has 32 bytes. -/
theorem messages_size_of_width (hash : ByteArray → ByteArray)
    (width : ∀ x, (hash x).size = 32) (tree : CommitmentTree) (complete : tree.Complete) :
    ∀ message ∈ tree.messages hash, message.size = 2 * bytesPerChunk := by
  -- Every message is either two complete child roots or a message already covered in a child.
  induction tree with
  | leaf node => simp [messages]
  | fork left right ihLeft ihRight =>
    intro message member
    simp only [messages, List.mem_cons, List.mem_append] at member
    rcases member with rfl | member | member
    · simp [root_size left complete.1 hash width, root_size right complete.2 hash width,
        Nat.two_mul]
    · exact ihLeft complete.1 _ member
    · exact ihRight complete.2 _ member

/-- Every recorded compression input consists of exactly two complete nodes. -/
theorem messages_size (tree : CommitmentTree) (complete : tree.Complete) :
    ∀ message ∈ tree.messages, message.size = 2 * bytesPerChunk :=
  messages_size_of_width _ Cryptography.Hash.Sha256.hash_size tree complete

/-- Equal parent roots either preserve both children or expose their distinct hash inputs. -/
theorem fork_binding {hash : ByteArray → ByteArray}
    {left right otherLeft otherRight : CommitmentTree}
    (complete : (fork left right).Complete)
    (otherComplete : (fork otherLeft otherRight).Complete)
    (same : (fork left right).root hash = (fork otherLeft otherRight).root hash)
    (width : ∀ x, (hash x).size = 32 := by exact EthLib.Cryptography.Hash.Sha256.hash_size) :
    (left.root hash = otherLeft.root hash ∧ right.root hash = otherRight.root hash) ∨
      Collision (.fork left right) (.fork otherLeft otherRight) hash := by
  -- Two equal 64-byte concatenations split uniquely at byte 32.
  -- Unequal ones witness a collision.
  by_cases inputs : left.root hash ++ right.root hash = otherLeft.root hash ++ otherRight.root hash
  · exact .inl (Array.append_inj inputs ((root_size _ complete.1 hash width).trans
      (root_size _ otherComplete.1 hash width).symm))
  · exact .inr ⟨_, List.mem_cons_self, _, List.mem_cons_self, inputs, ByteArray.ext same⟩

/-- A collision in the left subcomputations remains a collision in the full trees. -/
theorem Collision.left {hash : ByteArray → ByteArray} {left otherLeft : CommitmentTree}
    (right otherRight : CommitmentTree) (collision : Collision left otherLeft hash) :
    Collision (.fork left right) (.fork otherLeft otherRight) hash := by
  -- The left subtree keeps both witnesses when its message list is included in the larger tree.
  obtain ⟨first, firstMem, second, secondMem, rest⟩ := collision
  exact ⟨first, by simp [messages, firstMem], second, by simp [messages, secondMem], rest⟩

/-- A collision in the right subcomputations remains a collision in the full trees. -/
theorem Collision.right {hash : ByteArray → ByteArray} {right otherRight : CommitmentTree}
    (left otherLeft : CommitmentTree) (collision : Collision right otherRight hash) :
    Collision (.fork left right) (.fork otherLeft otherRight) hash := by
  -- The right subtree keeps both witnesses when its message list is included in the larger tree.
  obtain ⟨first, firstMem, second, secondMem, rest⟩ := collision
  exact ⟨first, by simp [messages, firstMem], second, by simp [messages, secondMem], rest⟩

/-- A fixed tree shape commits to every leaf unless its own hash computations collide. -/
theorem binding {hash : ByteArray → ByteArray} (left right : CommitmentTree)
    (complete : left.Complete) (otherComplete : right.Complete) (shape : SameShape left right)
    (same : left.root hash = right.root hash)
    (width : ∀ x, (hash x).size = 32 := by exact EthLib.Cryptography.Hash.Sha256.hash_size) :
    left = right ∨ Collision left right hash := by
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
      rcases fork_binding complete otherComplete same width with equal | collision
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
@[simp] theorem perfect_root (depth : Nat) (leaves : Nat → Bytes)
    (hash : ByteArray → ByteArray := Cryptography.Hash.Sha256.hash) :
    (perfect depth leaves).root hash
      = subtreeRoot (fun a b => (combineM (m := Id) hash a b).run) depth leaves := by
  -- Both descriptions split at the same half-width and hash the same child roots.
  induction depth generalizing leaves with
  | zero => rfl
  | succ depth ih => simp [perfect, root, subtreeRoot_halves, ih]

/-- Expanding the zero subtrees of any hash gives exactly its bounded-tree root. -/
theorem perfect_subtreeAtM (hash : ByteArray → ByteArray) (chunks : Array Bytes)
    (depth start : Nat) :
    (perfect depth fun i => padded zeroChunk chunks (start + i)).root hash =
      (subtreeAtM (Hasher.ofHash (m := Id) hash) chunks depth start).run := by
  -- Both sides are the specification's tree over the same padded leaves.
  rw [perfect_root (hash := hash), subtreeAtM_ofHash_eq_subtreeRoot]

/-- Expanding cached zero subtrees gives exactly the executable bounded-tree root. -/
theorem perfect_subtreeAt (chunks : Array Bytes) (depth start : Nat) :
    (perfect depth fun i => padded zeroChunk chunks (start + i)).root =
      subtreeAt chunks depth start := by
  -- The specification's hasher is the one built from SHA-256 alone.
  rw [perfect_subtreeAtM, ofHash_sha256]
  rfl

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
end EthLib.Serialization.Ssz
