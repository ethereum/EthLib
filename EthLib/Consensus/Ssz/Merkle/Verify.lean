import EthLib.Consensus.Ssz.Merkle.Gindex
import EthLib.Consensus.Ssz.Merkle.Tree

/-! Rebuilding a root from nodes and the indices they sit at, reading no declaration. -/

namespace EthLib.Consensus.Ssz

/--
Joining a node with each branch node in turn, from the leaf upward.

The level counts how far the walk has climbed, which is the bit of the index it reads.
-/
def climbBranch (index : Nat) : (level : Nat) → (node : Bytes) → List Bytes → Bytes
  | _, node, [] => node
  | level, node, sibling :: rest =>
    -- A set bit puts this node on the right, so the branch node joins on the left.
    let parent := if gindexBit index level then combine sibling node else combine node sibling
    climbBranch index (level + 1) parent rest

/--
A root rebuilt from one leaf and its branch, trusting every node to be 32 bytes wide.

Each bit of the index, read from the leaf upward, says which side the branch node joins on.

Only the index and the branch length are checked.
-/
def calculateMerkleRootUnchecked (leaf : Bytes) (proof : List Bytes) (index : Nat) :
    Except Err Bytes := do
  let depth ← gindexLength index
  if proof.length != depth then throw (.branchLength depth proof.length)
  return climbBranch index 0 leaf proof

/--
A root rebuilt from one leaf and its branch.

The index and the branch length are checked first, then the width of every node hashed.
-/
def calculateMerkleRoot (leaf : Bytes) (proof : List Bytes) (index : Nat) :
    Except Err Bytes := do
  let rebuilt ← calculateMerkleRootUnchecked leaf proof index
  -- A 31-byte child and a 33-byte sibling must not impersonate two 32-byte nodes.
  checkChunk leaf
  checkChunks proof
  return rebuilt

/--
Whether one leaf and its branch rebuild the expected root.

The root is only compared, so a root of the wrong width is answered false rather than refused.
-/
def verifyMerkleProof (leaf : Bytes) (proof : List Bytes) (index : Nat) (root : Bytes) :
    Except Err Bool := do
  let rebuilt ← calculateMerkleRoot leaf proof index
  return rebuilt == root

/-- The node held at an index, where one is held. -/
def nodeAt (nodes : List (Nat × Bytes)) (index : Nat) : Option Bytes :=
  (nodes.find? fun (at_, _) => at_ == index).map fun (_, node) => node

/-- Levels a node sits below the root, which its index carries in its leading bit. -/
def levelOf (index : Nat) : Nat :=
  Nat.log2 index

/-- One level's parents and shallower nodes, kept in their original order. -/
def foldLevelNodes (depth : Nat) (nodes : List (Nat × Bytes)) :
    List (Nat × Bytes) → Except Err (List (Nat × Bytes) × List (Nat × Bytes))
  | [] => .ok ([], [])
  | (index, node) :: rest => do
    if levelOf index != depth then
      -- A shallower node waits until the walk reaches its level.
      let (parents, kept) ← foldLevelNodes depth nodes rest
      return (parents, (index, node) :: kept)
    else if index % 2 == 0 then
      -- An even index owns the pair, with the odd index on its right.
      match nodeAt nodes (index + 1) with
      | some sibling =>
        let (parents, kept) ← foldLevelNodes depth nodes rest
        return ((gindexParent index, combine node sibling) :: parents, kept)
      | none => throw .proofIncomplete
    else if (nodeAt nodes (index - 1)).isNone then
      -- An odd node must have a left sibling, which performs the actual hash.
      throw .proofIncomplete
    else foldLevelNodes depth nodes rest

/-- Every pair at one level folded into its parent, with shallower nodes kept aside. -/
def foldLevel (depth : Nat) (nodes : List (Nat × Bytes)) :
    Except Err (List (Nat × Bytes)) := do
  let (parents, kept) ← foldLevelNodes depth nodes nodes
  return parents ++ kept

/--
Folding a node set upward one level at a time, until only the root is left.

Recursion is on the depth rather than on the node set.

The fold is therefore structural, and needs no bound of its own.
-/
def foldToRoot : Nat → List (Nat × Bytes) → Except Err Bytes
  | 0, nodes =>
    match nodeAt nodes 1 with
    | some root => .ok root
    -- A proof from which the root never appeared authenticates nothing.
    | none => .error .proofIncomplete
  | depth + 1, nodes => do foldToRoot depth (← foldLevel (depth + 1) nodes)

/--
A root rebuilt from several leaves and the nodes they share, trusting each to be 32 bytes wide.

Pairs combine from the deepest level upward, each parent built once.

Only the counts and the indices are checked.
-/
def calculateMultiMerkleRootUnchecked (leaves proof : List Bytes) (indices : List Nat) :
    Except Err Bytes := do
  if leaves.length != indices.length then throw (.leafCount indices.length leaves.length)
  let helpers ← getHelperIndices indices
  if proof.length != helpers.length then throw (.proofLength helpers.length proof.length)
  let nodes := indices.zip leaves ++ helpers.zip proof
  -- No node sits below the deepest index given, so that is where the fold starts.
  let deepest := (nodes.map fun (index, _) => levelOf index).foldl max 0
  foldToRoot deepest nodes

/--
A root rebuilt from several leaves and the nodes they share.

The counts and the indices are checked first, then the width of every node hashed.
-/
def calculateMultiMerkleRoot (leaves proof : List Bytes) (indices : List Nat) :
    Except Err Bytes := do
  let rebuilt ← calculateMultiMerkleRootUnchecked leaves proof indices
  -- A node of another width would move the boundary between two hashed operands.
  checkChunks leaves
  checkChunks proof
  return rebuilt

/--
Whether several leaves and their nodes rebuild the expected root.

The root is only compared, so a root of the wrong width is answered false rather than refused.
-/
def verifyMerkleMultiproof (leaves proof : List Bytes) (indices : List Nat) (root : Bytes) :
    Except Err Bool := do
  let rebuilt ← calculateMultiMerkleRoot leaves proof indices
  return rebuilt == root

/--
A node reading that is a Merkle tree: every node is the two below it, combined.

Nothing here fixes the leaves, so this covers any tree built with the same pairing.
-/
def MerkleTree (node : Nat → Bytes) : Prop :=
  -- The equation holds at every index, though a proof about one branch uses only its ancestors.
  ∀ index, 1 ≤ index → node index = combine (node (2 * index)) (node (2 * index + 1))

/-- Each parent on one branch is its child and sibling hashed in tree order. -/
def BranchConsistent (node : Nat → Bytes) (index : Nat) : Prop :=
  -- Only the parents along this one path are required, and nothing below its leaf.
  ∀ level, level < Nat.log2 index →
    (if gindexBit index level then
      combine (node (gindexSibling (index >>> level))) (node (index >>> level))
    else combine (node (index >>> level)) (node (gindexSibling (index >>> level))))
      = node (index >>> (level + 1))

end EthLib.Consensus.Ssz
