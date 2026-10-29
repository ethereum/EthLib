import EthLib.Serialization.Ssz.Merkle.Chunk

/-! The root of an SSZ Merkle tree, and the facts an implementation of it leans on. -/

namespace EthLib.Serialization.Ssz

variable {α : Type}

/--
Root of the perfect binary tree of a given depth.

Leaves arrive as a function from position to node, not as a list.

A tree wider than its data therefore needs no padding to describe.

    depth 2:

    parent hash
     +-- left parent hash
     |    +-- leaf 0
     |    `-- leaf 1
     `-- right parent hash
          +-- leaf 2
          `-- leaf 3

Nothing here reads a node, so this holds for any node type at all.
-/
def subtreeRoot (combine : α → α → α) : (depth : Nat) → (leaves : Nat → α) → α
  | 0, leaves => leaves 0
  -- The right half sees the same leaves, shifted past the left half's width.
  | depth + 1, leaves =>
      combine
        (subtreeRoot combine depth leaves)
        (subtreeRoot combine depth fun i => leaves (i + 2 ^ depth))

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
Leaves of a tree, taken from an array of nodes.

Positions past the end of the array read as zero.
-/
def padded (zero : α) (chunks : Array α) : Nat → α :=
  fun position => chunks[position]?.getD zero

/-- A spine of perfect trees with capacities 1, 4, 16, and so on, per [EIP-7916](https://eips.ethereum.org/EIPS/eip-7916). -/
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
