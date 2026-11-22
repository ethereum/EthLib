module

public import EthLib.Serialization.Ssz.Merkle.Gindex
public import EthLib.Serialization.Ssz.Merkle.Tree

/-!
Rebuilding a root from nodes and the indices they sit at, reading no declaration.

The rules of single and multiple proofs are stated in EthLib's own terms, one step per comment.

A parent is `H(left || right)`, with `H` SHA-256, and node `k` has the children `2k` and `2k + 1`.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/--
Joining a node with each branch node in turn, from the leaf upward.

The hash may answer in a monad.

The level counts how far the walk has climbed, which is the bit of the index it reads.

It is the Merkle climb from the node at that level, hashing every node alike.
-/
def climbBranchM {m : Type → Type} [Monad m] (hash : ByteArray → m ByteArray)
    (index level : Nat) (node : Bytes) (branch : List Bytes) : m Bytes :=
  -- For the branch node `b_i` at level `i`: `v = H(b_i || v)` if bit `i` of `k` is 1.
  --
  -- Otherwise `v = H(v || b_i)`.
  Cryptography.Merkle.climb (fun _ => combineM hash) ⟨level, index >>> level⟩ node branch

/-- Joining a node with each branch node in turn, from the leaf upward, with SHA-256. -/
def climbBranch (index level : Nat) (node : Bytes) (branch : List Bytes) : Bytes :=
  (climbBranchM (m := Id) Cryptography.Hash.Sha256.hash index level node branch).run

/--
A root rebuilt from one leaf and its branch, trusting every node to be 32 bytes wide.

Each bit of the index, read from the leaf upward, says which side the branch node joins on.

Only the index and the branch length are checked.
-/
def calculateMerkleRootUnchecked (leaf : Bytes) (proof : List Bytes) (index : Nat) :
    Except Err Bytes := do
  -- EthLib asks for a node below the root, `k >= 2`: the root alone has no branch to check.
  let depth ← gindexLength index
  -- The branch holds one node per level: `depth(k)` of them.
  if proof.length != depth then throw (.branchLength depth proof.length)
  -- The climb starts at the leaf, level 0, and reads bit 0 of `k` first.
  return climbBranch index 0 leaf proof

/--
A root rebuilt from one leaf and its branch.

The index and the branch length are checked first, then the width of every node hashed.
-/
def calculateMerkleRoot (leaf : Bytes) (proof : List Bytes) (index : Nat) :
    Except Err Bytes := do
  let rebuilt ← calculateMerkleRootUnchecked leaf proof index
  -- EthLib's check: every node is one 32-byte chunk.
  --
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
  -- The proof holds when the rebuilt root equals the expected one.
  return rebuilt == root

/-- The node hash of SSZ trees: SHA-256 of the two children, the same at every position. -/
abbrev sszNodeHash : Cryptography.Merkle.Position → Bytes → Bytes → Id Bytes :=
  fun _ => combineM Cryptography.Hash.Sha256.hash

/--
A root rebuilt from several leaves and the nodes they share, trusting each to be 32 bytes wide.

It is the root the Merkle multiproof rebuilds, in the tree as deep as the deepest index.

Only the counts and the indices are checked.
-/
def calculateMultiMerkleRootUnchecked (leaves proof : List Bytes) (indices : List Nat) :
    Except Err Bytes := do
  -- One leaf per index.
  if leaves.length != indices.length then throw (.leafCount indices.length leaves.length)
  let (height, opened) ← claimPositions indices
  -- The helpers are those of the indices, as positions.
  let helpers := Cryptography.Merkle.helpers height opened
  -- One proof node per helper index, in the order of the helper indices.
  if proof.length != helpers.length then throw (.proofLength helpers.length proof.length)
  -- Each leaf sits at its index and each proof node at its helper index.
  --
  -- Each node not given is `H(node(2j) || node(2j + 1))`, computed from node 1 down.
  match (Cryptography.Merkle.rebuild sszNodeHash (opened.zip leaves ++ helpers.zip proof)
      height).run with
  | some root => return root
  -- Checked indices always determine the root, so this error is never raised.
  | none => throw .proofIncomplete

/--
A root rebuilt from several leaves and the nodes they share.

The counts and the indices are checked first, then the width of every node hashed.
-/
def calculateMultiMerkleRoot (leaves proof : List Bytes) (indices : List Nat) :
    Except Err Bytes := do
  let rebuilt ← calculateMultiMerkleRootUnchecked leaves proof indices
  -- EthLib's check: every node is one 32-byte chunk.
  --
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
  -- The multiproof holds when the rebuilt root equals the expected one.
  return rebuilt == root

/--
A node reading that is a Merkle tree: every node is the two below it, combined.

Nothing here fixes the leaves, so this covers any tree built with the same pairing.
-/
def MerkleTree (node : Nat → Bytes) : Prop :=
  -- `node(k) = H(node(2k) || node(2k + 1))` for every `k >= 1`.
  --
  -- The equation holds at every index, though a proof about one branch uses only its ancestors.
  ∀ index, 1 ≤ index → node index = combine (node (2 * index)) (node (2 * index + 1))

/-- Each parent on one branch is its child and sibling hashed in tree order. -/
def BranchConsistent (node : Nat → Bytes) (index : Nat) : Prop :=
  -- For each level `i` of the branch, the parent of `p = floor(k / 2^i)` is `H` of its children.
  --
  -- Those children are `p` and its sibling, in the order bit `i` of `k` gives.
  --
  -- Only the parents along this one path are required, and nothing below its leaf.
  ∀ level, level < Nat.log2 index →
    (if gindexBit index level then
      combine (node (gindexSibling (index >>> level))) (node (index >>> level))
    else combine (node (index >>> level)) (node (gindexSibling (index >>> level))))
      = node (index >>> (level + 1))

end EthLib.Serialization.Ssz
