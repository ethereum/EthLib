module

public import EthLib.Cryptography.Merkle.Tree
public import EthLib.Serialization.Ssz.Merkle.Chunk

/-!
The root of an SSZ Merkle tree, and the facts an implementation of it leans on.

The rules of a bounded tree are stated in EthLib's own terms, one step per comment.

A node `k` has the children `2k` and `2k + 1`, and its value is `H(left || right)`.

Here `H` is the hash the caller gives.

[EIP-7916][eip7916] defines the progressive tree: a spine of subtrees of 1, 4, 16, ... leaves.

[eip7916]: https://github.com/ethereum/EIPs/blob/875fcf6d084c096195fec170310514444f537133/EIPS/eip-7916.md#progressive-merkle-tree
-/

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
  -- The root of depth `d` over the leaves `0` to `2^d - 1`, each parent `H(left || right)`.
  (Cryptography.Merkle.root (m := Id) (fun _ => combine) leaves depth).run

/-- Root of the perfect tree of a given depth whose leaves are all zero, one hash per level. -/
def zeroRootM {m : Type → Type} [Monad m] (combine : α → α → m α) (zero : α) : Nat → m α
  -- `Z_0` is the zero leaf.
  | 0 => pure zero
  -- `Z_{d+1} = H(Z_d || Z_d)`: both children of a zero subtree are zero subtrees.
  | depth + 1 => do
    let below ← zeroRootM combine zero depth
    combine below below

/-- The same root, with a pure hash. -/
def zeroRoot (combine : α → α → α) (zero : α) (depth : Nat) : α :=
  (zeroRootM (m := Id) combine zero depth).run

/-- Smallest depth whose perfect tree holds the given number of leaves. -/
def depthFor (leafCount : Nat) : Nat :=
  -- A tree of `n` leaves is padded to the next power of two `2^d`, with 0 and 1 giving 1.
  --
  -- So `d(n) = 0` for `n <= 1`, and `d(n) = d(ceil(n / 2)) + 1` above.
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
  -- The padding to the width of the tree is zero leaves, read here rather than stored.
  fun position => chunks[position]?.getD zero

/--
The root of a progressive spine: each subtree root hashed against the spine after it.

A zero node closes the spine, and the hash may answer in a monad.
-/
def spineM {m : Type → Type} [Monad m] (combine : α → α → m α) (zero : α) (tops : List α) : m α :=
  -- EIP-7916: the root is `H(a || b)`, `a` the subtree of a level and `b` the spine after it.
  --
  -- With no level left, the spine is the zero node.
  tops.foldrM combine zero

/-- The same spine, with a pure hash. -/
def spine (combine : α → α → α) (zero : α) (tops : List α) : α :=
  (spineM (m := Id) combine zero tops).run

/--
The runs of nodes that the subtrees of a progressive spine hold, each with its level.

The run at `level` holds the next `4 ^ level` nodes, and the runs go on while nodes remain.
-/
def progressiveWindows (chunks : List α) (level : Nat := 0) : List (List α × Nat) :=
  -- EIP-7916: level `k` takes the next `4^k` chunks, or the rest if fewer remain.
  --
  -- A level opens only while chunks remain, so an empty input opens none.
  if chunks.isEmpty then []
  else (chunks.take (4 ^ level), level) :: progressiveWindows (chunks.drop (4 ^ level)) (level + 1)
termination_by chunks.length
decreasing_by
  have positive : 0 < 4 ^ level := Nat.pos_of_neZero _
  have nonempty : 0 < chunks.length := by cases chunks <;> simp_all
  simp only [List.length_drop]
  omega

/-- A spine of perfect trees with capacities 1, 4, 16, and so on.

Source: [EIP-7916, Progressive Merkle tree][eip7916].

[eip7916]: https://github.com/ethereum/EIPs/blob/875fcf6d084c096195fec170310514444f537133/EIPS/eip-7916.md#progressive-merkle-tree
-/
def progressiveRoot (combine : α → α → α) (zero : α) (chunks : List α)
    (level : Nat := 0) : α :=
  -- EIP-7916 closes an empty suffix with a single zero node.
  spine combine zero <| (progressiveWindows chunks level).map fun (window, windowLevel) =>
    -- The subtree of level `k` has `4^k` leaves, so depth `2k`, its chunks zero-padded.
    subtreeRoot combine (depthFor (4 ^ windowLevel)) (padded zero window.toArray)

end EthLib.Serialization.Ssz
