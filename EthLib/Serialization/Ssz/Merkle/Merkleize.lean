module

public import EthLib.Cryptography.Merkle.Tree
public import EthLib.Serialization.Ssz.Merkle.Chunk

/-! The root of an SSZ Merkle tree, and the facts an implementation of it leans on. -/

@[expose] public section

namespace EthLib.Serialization.Ssz

variable {α : Type}

/--
Root of the perfect binary tree of a given depth.

Leaves arrive as a function from position to node, not as a list.

A tree wider than its data therefore needs no padding to describe.

For example, at depth 2 the root hashes two parents, of leaves 0 and 1, and of leaves 2 and 3.

Nothing here reads a node, so this holds for any node type at all.

It is the Merkle tree of that depth, hashing every node alike.
-/
def subtreeRoot (combine : α → α → α) (depth : Nat) (leaves : Nat → α) : α :=
  (Cryptography.Merkle.root (m := Id) (fun _ _ => combine) leaves depth).run

/--
Root of the perfect binary tree of a given depth whose every leaf is zero.

A value with a large capacity is mostly padding, so implementations precompute this.
-/
def zeroRoot (combine : α → α → α) (zero : α) : Nat → α
  | 0 => zero
  | depth + 1 => combine (zeroRoot combine zero depth) (zeroRoot combine zero depth)

/-- Smallest depth whose perfect tree holds the given number of leaves. -/
def depthFor (leafCount : Nat) : Nat :=
  if leafCount ≤ 1 then 0
  -- Rounding up is what stops an odd count from losing its last leaf.
  else depthFor ((leafCount + 1) / 2) + 1
decreasing_by omega

/--
The chosen depth really does hold the requested number of leaves.

Without this the capacity check names a number unrelated to the tree built.
-/
theorem le_two_pow_depthFor (leafCount : Nat) : leafCount ≤ 2 ^ depthFor leafCount := by
  -- Recursing the proof the way the definition recurses keeps the two in step.
  --
  -- Widths double one level up, and the halved count already fits the level below.
  induction leafCount using depthFor.induct with
  | case1 leafCount small => simp [depthFor, small]
  | case2 leafCount large ih => rw [depthFor, ite_eq_right large, Nat.pow_succ]; omega

/--
No shallower tree holds them, so the depth chosen is the least one that does.

Together with the bound above this pins the depth exactly.

That is what ties it to the specification's next power of two.
-/
theorem depthFor_le_of_le_two_pow {leafCount depth : Nat} (holds : leafCount ≤ 2 ^ depth) :
    depthFor leafCount ≤ depth := by
  induction leafCount using depthFor.induct generalizing depth with
  | case1 leafCount small =>
    -- A depth-zero tree is already the shallowest there is.
    simp [depthFor, small]
  | case2 leafCount large ih =>
    -- Two or more leaves need a level, so the bound must have come from one too.
    rw [depthFor, ite_eq_right large]
    cases depth with
    | zero => simp at holds; omega
    | succ shallower =>
      have := @ih shallower (by rw [Nat.pow_succ] at holds; omega)
      omega

/-- A larger capacity never asks for a shallower tree. -/
theorem depthFor_le_depthFor {count capacity : Nat} (room : count ≤ capacity) :
    depthFor count ≤ depthFor capacity :=
  depthFor_le_of_le_two_pow (Nat.le_trans room (le_two_pow_depthFor capacity))

/--
Leaves of a tree, taken from an array of nodes.

Positions past the end of the array read as zero.
-/
def padded (zero : α) (chunks : Array α) : Nat → α :=
  fun position => chunks[position]?.getD zero

/-- A spine of perfect trees with capacities 1, 4, 16, and so on.

Source: [EIP-7916](https://eips.ethereum.org/EIPS/eip-7916). -/
def progressiveRoot (combine : α → α → α) (zero : α) (chunks : List α)
    (level : Nat := 0) : α :=
  -- EIP-7916 closes an empty suffix with a single zero node.
  if chunks.isEmpty then zero
  else
    let width := 4 ^ level
    let left := subtreeRoot combine (depthFor width) (padded zero (chunks.take width).toArray)
    combine left (progressiveRoot combine zero (chunks.drop width) (level + 1))
termination_by chunks.length
decreasing_by
  have positive : 0 < 4 ^ level := Nat.pos_of_neZero _
  have nonempty : 0 < chunks.length := by cases chunks <;> simp_all
  simp only [List.length_drop]
  omega

end EthLib.Serialization.Ssz
