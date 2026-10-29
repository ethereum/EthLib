import EthLib.Serialization.Proofs.Ssz.Codec.Proof
import EthLib.Serialization.Proofs.Ssz.Merkle.HelperFrontier
import EthLib.Serialization.Proofs.Ssz.Type.Equality

/-! A bounded proof walk reads the same binary subtrees that merkleization hashes. -/

namespace EthLib.Serialization.Ssz

/-- A binary subtree selected by the remaining turns of a generalized index. -/
def boundedTreeNode (chunks : Array Bytes) (height index depth start : Nat) : Bytes :=
  -- Each remaining turn halves the leaf interval and the low path bits select its start.
  subtreeAt chunks (height - depth) (start + gindexBelow index depth * 2 ^ (height - depth))

/-- Walking within a bounded tree returns the root of the selected leaf interval. -/
theorem boundedNode_window {budget : Nat} {layout : MerkleLayout} {chunks : Array Bytes}
    (windows : ∀ start stop, layoutChunksAt budget layout start (some stop) =
      .ok (chunks.extract start stop))
    (index depth start capacity : Nat) (inside : depth ≤ depthFor capacity) :
    boundedNode budget layout index depth start capacity =
      .ok (boundedTreeNode chunks (depthFor capacity) index depth start) := by
  -- The remaining width is a power of two, so interval merkleization is exactly a subtree.
  have width : nextPow2 capacity >>> depth = 2 ^ (depthFor capacity - depth) := by
    rw [nextPow2, Nat.shiftRight_eq_div_pow, Nat.pow_div inside (by decide)]
  simp only [boundedNode, nextPow2, Nat.log2_two_pow, ite_eq_left inside]
  rw [show 2 ^ depthFor capacity >>> depth = 2 ^ (depthFor capacity - depth) from width]
  simp only [windows, Bind.bind, Except.bind]
  exact merkleizeBoundedUnchecked_window chunks _

/-- Appending a left or right turn doubles the old position and adds that turn. -/
theorem gindexBelow_children (index depth : Nat) :
    gindexBelow (2 * index) (depth + 1) = 2 * gindexBelow index depth ∧
    gindexBelow (2 * index + 1) (depth + 1) = 2 * gindexBelow index depth + 1 := by
  -- Reducing modulo the enlarged width retains precisely the old turns and the new bit.
  -- A positive binary width bounds the retained remainder before a child turn is appended.
  have positive : 0 < 2 ^ depth := Nat.two_pow_pos depth
  have remainder : index % 2 ^ depth < 2 ^ depth := Nat.mod_lt _ positive
  have left : 2 * index % (2 * 2 ^ depth) = 2 * (index % 2 ^ depth) :=
    Nat.mul_mod_mul_left 2 index (2 ^ depth)
  constructor
  · simpa [gindexBelow, Nat.pow_succ, Nat.mul_comm] using left
  · simp only [gindexBelow, Nat.pow_succ]
    rw [Nat.mul_comm (2 ^ depth) 2, Nat.add_mod, left,
      Nat.mod_eq_of_lt (by omega : 1 < 2 * 2 ^ depth), Nat.mod_eq_of_lt (by omega)]

/-- An internal bounded node is the hash of its two child intervals. -/
theorem boundedTreeNode_split (chunks : Array Bytes) (height index depth start : Nat)
    (inside : depth < height) :
    boundedTreeNode chunks height index depth start =
      combine (boundedTreeNode chunks height (2 * index) (depth + 1) start)
        (boundedTreeNode chunks height (2 * index + 1) (depth + 1) start) := by
  -- One more turn halves the interval and places its right half immediately after the left.
  obtain ⟨left, right⟩ := gindexBelow_children index depth
  -- An internal node has one more remaining level than either child interval.
  have remaining : height - depth = height - (depth + 1) + 1 := by omega
  unfold boundedTreeNode
  rw [remaining, subtreeAt_split, left, right]
  simp [Nat.pow_succ, Nat.mul_add, Nat.add_assoc, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- The nodes of one bounded binary tree, indexed from its root. -/
def boundedReading (chunks : Array Bytes) (height index : Nat) : Bytes :=
  -- The generalized index’s bit depth supplies exactly the turns below the tree’s root bit.
  boundedTreeNode chunks height index (Nat.log2 index) 0

/-- At index one, the bounded node reading is the entire padded tree. -/
theorem boundedReading_root (chunks : Array Bytes) (height : Nat) :
    boundedReading chunks height 1 = subtreeAt chunks height 0 := by
  -- The root consumes no turns and starts at the first leaf.
  have depth : Nat.log2 1 = 0 := rfl
  simp [boundedReading, boundedTreeNode, depth, gindexBelow]

/-- A bounded tree with one word mixed in as its right child. -/
def mixedReading (chunks : Array Bytes) (height : Nat) (word : Bytes) (index : Nat) : Bytes :=
  -- The root combines contents and word, while index three names the word directly.
  if index = 1 then combine (subtreeAt chunks height 0) word
  else if index = 3 then word
  else boundedTreeNode chunks height index (Nat.log2 index - 1) 0

/-- A child keeps the parent's higher branch turns. -/
theorem gindexBit_children (index level : Nat) :
    gindexBit (2 * index) (level + 1) = gindexBit index level ∧
    gindexBit (2 * index + 1) (level + 1) = gindexBit index level := by
  -- Reading above the lowest bit is reading the halved index.
  have left : 2 * index / 2 = index := by omega
  have right : (2 * index + 1) / 2 = index := by omega
  simp [gindexBit, Nat.testBit_add_one, left, right]

/-- Removing a branch turn decreases the depth by one until the root is reached. -/
theorem levelOf_shift {index : Nat} (named : 1 ≤ index) :
    ∀ step, step ≤ Nat.log2 index → levelOf (index >>> step) + step = Nat.log2 index := by
  -- Every intermediate ancestor is below the root until the final shift.
  intro step
  induction step with
  | zero => simp [levelOf]
  | succ step ih =>
    intro bounded
    have previous := ih (by omega)
    have parent := levelOf_parent (path_shift_positive named (by omega : step < Nat.log2 index))
    rw [shiftRight_succ]
    omega

/-- An ancestor below the root keeps the first turn of the original branch. -/
theorem gindexBit_shift_top {index step : Nat} (named : 1 ≤ index)
    (below : step < Nat.log2 index) :
    gindexBit (index >>> step) (Nat.log2 (index >>> step) - 1) =
      gindexBit index (Nat.log2 index - 1) := by
  -- Shifting drops lower turns, so the top turn moves down by the same number of places.
  have depth := levelOf_shift named step (by omega)
  change Nat.log2 (index >>> step) + step = Nat.log2 index at depth
  have position : step + (Nat.log2 (index >>> step) - 1) = Nat.log2 index - 1 := by omega
  simp [gindexBit, Nat.testBit_shiftRight, position]

/-- Swapping siblings changes only the lowest turn of their indices. -/
theorem gindexBit_sibling_high (index position : Nat) (above : 0 < position) :
    gindexBit (gindexSibling index) position = gindexBit index position := by
  -- Any higher bit is read from the common parent.
  cases position with
  | zero => omega
  | succ position => simp [gindexBit, Nat.testBit_add_one, gindexSibling_half]

end EthLib.Serialization.Ssz
