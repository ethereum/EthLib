module

public import EthLib.Serialization.Ssz.Merkle.Verify

/-!
# Merkle branches by depth and index

A branch here is named by its depth and the index of its leaf among the `2^depth` leaves.

Bit `i` of the index says whether the path node `i` levels above the leaf is a right child.

The generalized index of that leaf is `2^depth + index`.

These rules are stated in EthLib's own terms, one step per comment, with `H` SHA-256.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/--
The root reached from a leaf at an index, climbing the first `depth` branch nodes.

A branch shorter than the depth names no root.
-/
def computeMerkleBranchRoot (leaf : Vector UInt8 32) (branch : List (Vector UInt8 32))
    (depth index : Nat) : Except Err (Vector UInt8 32) := do
  -- The branch holds at least `depth` nodes, and the first `depth` are read.
  if branch.length < depth then throw (.branchLength depth branch.length)
  -- For `i < depth`: `v = H(b_i || v)` if bit `i` of the index is 1, else `v = H(v || b_i)`.
  toChunk (climbBranch index 0 ⟨leaf.toArray⟩ ((branch.take depth).map fun node => ⟨node.toArray⟩))

/-- Whether a branch of exactly `depth` nodes climbs from the leaf at an index to the root. -/
def isValidMerkleBranch (leaf : Vector UInt8 32) (branch : List (Vector UInt8 32))
    (depth index : Nat) (root : Vector UInt8 32) : Bool :=
  -- EthLib asks for exactly `depth` nodes, so no node of a branch goes unread.
  --
  -- The branch is valid when the climb of `depth` levels ends at the root.
  depth == branch.length &&
    match computeMerkleBranchRoot leaf branch depth index with
    | .ok rebuilt => rebuilt == root
    | .error _ => false

/--
The index of a node among the nodes of its level, read from its generalized index.

Index zero names no node.
-/
def getSubtreeIndex (gindex : Nat) : Except Err Nat := do
  -- `k mod 2^depth(k)`, which is `k - 2^depth(k)`: the leading bit dropped.
  return gindexBelow gindex (← gindexDepth gindex)

/--
Whether a branch, after a run of zero nodes in front, climbs from the leaf to the root.

The leaf sits at a generalized index, so its depth is the bit width of that index less one.

Nodes beyond that depth come first, and each must be the zero node.

A branch shorter than the depth fails the check, and index zero names no leaf.
-/
def isValidNormalizedMerkleBranch (leaf : Vector UInt8 32) (branch : List (Vector UInt8 32))
    (gindex : Nat) (root : Vector UInt8 32) : Except Err Bool := do
  -- The depth is `floor(log2 k)` and the leaf index `k - 2^depth`.
  let depth ← gindexDepth gindex
  let index ← getSubtreeIndex gindex
  -- A branch of `n` nodes has `n - depth` extra nodes in front, none if `n < depth`.
  let extra := branch.length - depth
  -- Each extra node is the zero chunk, and the rest is a branch of `depth` nodes to the root.
  return (branch.take extra).all (· == Vector.replicate 32 0) &&
    isValidMerkleBranch leaf (branch.drop extra) depth index root

end EthLib.Serialization.Ssz
