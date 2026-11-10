module

public import EthLib.Consensus.Containers.Misc
public import EthLib.Cryptography.Hash.Sha256

/-!
# The deposit tree and its snapshot

The deposit contract commits to its deposits with a Merkle tree of depth 32.

The tree fills its leaves from the left, and its root mixes in the number of deposits.

A node keeps the tree to prove the deposits that the beacon chain has not yet processed.

Once the chain has finalized a deposit, its proof is never needed again.

Finalizing the tree replaces each complete subtree of finalized deposits by its root.

A snapshot holds those roots, with the count, the root and the execution block of the tree.

A node that starts from a checkpoint rebuilds the tree from a snapshot, without older deposits.

The tree, its finalization and the snapshot follow [EIP-4881][eip-4881].

[eip-4881]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-4881.md
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

/-- The reasons why an operation on the deposit tree or its snapshot fails. -/
inductive DepositTreeError where
  /-- The tree already holds the most deposits that the deposit contract accepts. -/
  | treeFull
  /-- Finalization names more deposits than the tree holds. -/
  | finalizeBeyondCount (finalized count : Nat)
  /-- Finalization names fewer deposits than an earlier finalization. -/
  | finalizeBelowFinalized (finalized earlier : Nat)
  /-- A snapshot needs a finalized execution block, and the tree has none. -/
  | notFinalized
  /-- The deposit at this index is finalized, so the tree keeps no proof of it. -/
  | proofOfFinalized (index finalized : Nat)
  /-- The tree holds no deposit at this index. -/
  | proofBeyondCount (index count : Nat)
  /-- A count of deposits reaches the number of leaves of the tree. -/
  | countBeyondCapacity (count : Nat)
  /-- A snapshot holds fewer finalized roots than its count has bits set. -/
  | missingFinalized
  /-- A snapshot holds more finalized roots than its count has bits set. -/
  | extraFinalized
  /-- A deposit root is not the root that the finalized roots and their count compute. -/
  | rootMismatch
  deriving DecidableEq, Repr

/-- The code of an error at the C boundary, one for each constructor. -/
def DepositTreeError.code : DepositTreeError → UInt32
  | .treeFull => 1
  | .finalizeBeyondCount .. => 2
  | .notFinalized => 3
  | .proofOfFinalized .. => 4
  | .proofBeyondCount .. => 5
  | .countBeyondCapacity _ => 6
  | .missingFinalized => 7
  | .extraFinalized => 8
  | .rootMismatch => 9
  | .finalizeBelowFinalized .. => 10


/-! ## Hashes -/

namespace DepositMerkleTree

/-- The parent of two nodes: SHA-256 of the left node, then the right one. -/
def hashPair (left right : Root) : Root :=
  Cryptography.Hash.Sha256.hash32 ⟨left.toArray ++ right.toArray⟩

/-- The root of the subtree of a height whose leaves are all zero. -/
def zeroNode : Nat → Root
  | 0 => Vector.replicate 32 0
  | height + 1 =>
    -- One recursive call per level: the two children are the same subtree.
    let below := zeroNode height
    hashPair below below

/--
A root with a count mixed in: the parent of the root and the count as 32 little-endian bytes.
-/
def mixInCount (root : Root) (count : Nat) : Root :=
  hashPair root (uintToBytes 32 count)

end DepositMerkleTree

/-! ## The sparse tree -/

/--
A deposit tree in which each subtree is stored only as far as it is needed.

As in the EIP, only an empty subtree stores its height.

The height of any other subtree is the height at which its parent places it.
-/
inductive DepositMerkleTree where
  /-- A subtree of the given height whose leaves are all zero. -/
  | zero (height : Nat)
  /-- One deposit, by the root of its data. -/
  | leaf (hash : Root)
  /-- A complete subtree of finalized deposits, by its count of leaves and its root. -/
  | finalized (count : Nat) (hash : Root)
  /-- A subtree by its two halves. -/
  | node (left right : DepositMerkleTree)
  deriving DecidableEq, Repr

namespace DepositMerkleTree

/-- The root of a subtree. -/
def root : DepositMerkleTree → Root
  | .zero height => zeroNode height
  | .leaf hash => hash
  | .finalized _ hash => hash
  | .node left right => hashPair left.root right.root

/-- Whether every leaf of a subtree holds a deposit, given that leaves fill from the left. -/
def isFull : DepositMerkleTree → Bool
  | .zero _ => false
  | .leaf _ => true
  | .finalized .. => true
  | .node _ right => right.isFull

/--
The subtree of a height whose first leaves are the given deposits.

The left half takes as many leaves as it has room for, and the right half the rest.

Leaves past the capacity of the subtree are not placed.
-/
def create : List Root → Nat → DepositMerkleTree
  | [], height => .zero height
  | first :: _, 0 => .leaf first
  | leaves@(_ :: _), height + 1 =>
    let split := min (2 ^ height) leaves.length
    .node (create (leaves.take split) height) (create (leaves.drop split) height)

/--
The subtree with one more deposit, in its first empty leaf.

A full subtree has no empty leaf, so it has no such subtree.
-/
def pushLeaf (hash : Root) : DepositMerkleTree → Option DepositMerkleTree
  | .zero height => some (create [hash] height)
  | .leaf _ => none
  | .finalized .. => none
  | .node left right =>
    if left.isFull then (.node left ·) <$> right.pushLeaf hash
    else (.node · right) <$> left.pushLeaf hash

/--
The subtree of a height with its first deposits finalized.

Each complete subtree of finalized deposits becomes its root.

A subtree with a finalized deposit receives the count that reaches into it.

The count must be positive: as in the EIP, a count of zero still finalizes the first leaf.
-/
def finalize (count : Nat) : DepositMerkleTree → Nat → DepositMerkleTree
  | .node left right, height + 1 =>
    if 2 ^ (height + 1) ≤ count then
      .finalized (2 ^ (height + 1)) (DepositMerkleTree.node left right).root
    else
      let left := left.finalize count height
      -- The right half holds a finalized deposit only past the leaves of the left half.
      let right := if 2 ^ height < count then right.finalize (count - 2 ^ height) height else right
      .node left right
  | .leaf hash, _ => .finalized 1 hash
  | tree, _ => tree

/-- The roots of the finalized subtrees from left to right, and the count of their deposits. -/
def getFinalized : DepositMerkleTree → List Root × Nat
  | .finalized count hash => ([hash], count)
  | .node left right =>
    let (leftRoots, leftCount) := left.getFinalized
    let (rightRoots, rightCount) := right.getFinalized
    (leftRoots ++ rightRoots, leftCount + rightCount)
  | _ => ([], 0)

/--
The subtree of a height rebuilt from the roots of its finalized subtrees and their count.

The first root is that of the largest finalized subtree, on the left.

A count past the capacity of the height has no such subtree.

It trusts the roots to number the bits set in the count, which the root check of a snapshot ensures.
-/
def fromSnapshotParts : List Root → Nat → Nat → Option DepositMerkleTree
  | [], _, height => some (.zero height)
  | first :: rest, deposits, height =>
    if deposits = 0 then some (.zero height)
    else if deposits = 2 ^ height then some (.finalized deposits first)
    else if 2 ^ height < deposits then none
    else match height with
      | 0 => none
      | height + 1 =>
        if deposits ≤ 2 ^ height then
          (.node · (.zero height)) <$> fromSnapshotParts (first :: rest) deposits height
        else
          (.node (.finalized (2 ^ height) first) ·) <$>
            fromSnapshotParts rest (deposits - 2 ^ height) height

/--
The leaf at an index of a subtree of a height, and its branch from the leaf up.

Bit `i` of the index says whether the node `i` levels above the leaf is a right child.

A path that meets a finalized or empty subtree above the leaves reaches no leaf.
-/
def generateProof (index : Nat) :
    DepositMerkleTree → (height : Nat) → Option (Root × Vector Root height)
  | tree, 0 => some (tree.root, #v[])
  | .node left right, height + 1 => do
    let (below, sibling) := if index.testBit height then (right, left) else (left, right)
    let (found, branch) ← below.generateProof index height
    pure (found, branch.push sibling.root)
  | _, _ + 1 => none

end DepositMerkleTree

/-! ## The snapshot -/

/--
A snapshot of a finalized deposit tree.

In a valid snapshot, it holds the roots of the finalized subtrees from left to right.

There is one root per bit set in the count.

The root, the count and the block hash are those of the finalized deposit vote of the chain.

The height is that of the execution block with that hash.
-/
structure DepositTreeSnapshot where
  /-- The roots of the finalized subtrees, from left to right. -/
  finalized : SszList Hash32 DEPOSIT_CONTRACT_TREE_DEPTH.toNat
  /-- The root of the deposit tree, with the count mixed in. -/
  depositRoot : Hash32
  /-- The number of finalized deposits. -/
  depositCount : UInt64
  /-- The hash of the execution block whose deposits the snapshot holds. -/
  executionBlockHash : Hash32
  /-- The height of that execution block. -/
  executionBlockHeight : UInt64
  deriving DecidableEq

instance : SszType DepositTreeSnapshot :=
  .container
    ["finalized", "deposit_root", "deposit_count", "execution_block_hash",
      "execution_block_height"]
    (fun s => (s.finalized, s.depositRoot, s.depositCount, s.executionBlockHash,
      s.executionBlockHeight))
    (fun (finalized, depositRoot, depositCount, executionBlockHash, executionBlockHeight) =>
      ⟨finalized, depositRoot, depositCount, executionBlockHash, executionBlockHeight⟩)

namespace DepositTreeSnapshot

open DepositMerkleTree (hashPair zeroNode mixInCount)

/--
The root below the count, built up from a level, with the finalized roots not yet used.

At each level, a set bit of the count takes the last unused root as the left child.

A clear bit takes the zero subtree of that level as the right child.
-/
def climbFinalized (pending : List Root) (size : Nat) (root : Root) :
    (level : Nat) → (levels : Nat) → Except DepositTreeError Root
  | _, 0 => if pending.isEmpty then .ok root else .error .extraFinalized
  | level, levels + 1 =>
    if size.testBit level then
      match pending with
      | [] => .error .missingFinalized
      | last :: earlier => climbFinalized earlier size (hashPair last root) (level + 1) levels
    else climbFinalized pending size (hashPair root (zeroNode level)) (level + 1) levels

/--
The deposit root that finalized roots and a count compute.

The count must be below the number of leaves of the tree.

The roots must number exactly the bits set in the count.

The reference implementation of the EIP checks neither.

It ignores extra roots at the front, and reuses roots from the end when they run out.
-/
def calculateRootOf (finalized : List Root) (count : Nat) : Except DepositTreeError Root := do
  let depth := DEPOSIT_CONTRACT_TREE_DEPTH.toNat
  if 2 ^ depth ≤ count then throw (.countBeyondCapacity count)
  let root ← climbFinalized finalized.reverse count (zeroNode 0) 0 depth
  return mixInCount root count

/-- The deposit root that the finalized roots and the count of a snapshot compute. -/
def calculateRoot (snapshot : DepositTreeSnapshot) : Except DepositTreeError Root :=
  calculateRootOf snapshot.finalized.data.toList snapshot.depositCount.toNat

/--
The snapshot of finalized roots, their count and an execution block, with its computed root.
-/
def fromTreeParts (finalized : List Root) (count : Nat) (block : Hash32 × UInt64) :
    Except DepositTreeError DepositTreeSnapshot := do
  let depositRoot ← calculateRootOf finalized count
  -- The root check above leaves one root per set bit of the count, so at most one per level.
  if bound : finalized.toArray.size ≤ DEPOSIT_CONTRACT_TREE_DEPTH.toNat then
    return {
      finalized := ⟨finalized.toArray, bound⟩
      depositRoot
      depositCount := count.toUInt64
      executionBlockHash := block.1
      executionBlockHeight := block.2 }
  else throw .extraFinalized

end DepositTreeSnapshot

/-! ## The deposit tree -/

/-- The deposit tree of a node: the sparse tree, its count, and the block it was finalized at. -/
structure DepositTree where
  /-- The sparse tree of height 32. -/
  tree : DepositMerkleTree
  /-- The number of deposits in the tree, finalized or not, which the root mixes in. -/
  mixInLength : Nat
  /-- The hash and the height of the execution block of the last finalization, if any. -/
  finalizedExecutionBlock : Option (Hash32 × UInt64)
  deriving DecidableEq, Repr

namespace DepositTree

open DepositMerkleTree (mixInCount fromSnapshotParts)

/-- The tree with no deposit. -/
def new : DepositTree :=
  ⟨.zero DEPOSIT_CONTRACT_TREE_DEPTH.toNat, 0, none⟩

/-- The deposit root: the root of the tree with the number of deposits mixed in. -/
def getRoot (tree : DepositTree) : Root :=
  mixInCount tree.tree.root tree.mixInLength

/--
The tree with one more deposit, by the root of its data.

The deposit contract accepts at most `2^32 - 1` deposits, one fewer than the leaves of its tree.

The reference implementation of the EIP has no such limit.
-/
def pushLeaf (tree : DepositTree) (leaf : Root) : Except DepositTreeError DepositTree :=
  if 2 ^ DEPOSIT_CONTRACT_TREE_DEPTH.toNat - 1 ≤ tree.mixInLength then .error .treeFull
  else
    match tree.tree.pushLeaf leaf with
    | some sparse => .ok { tree with tree := sparse, mixInLength := tree.mixInLength + 1 }
    | none => .error .treeFull

/-- The tree after pushing deposits in order. -/
def pushLeaves (tree : DepositTree) (leaves : List Root) : Except DepositTreeError DepositTree :=
  leaves.foldlM pushLeaf tree

/--
The tree with the deposits that finalized deposit data counts pruned, and its block recorded.

The data counts at least the deposits of an earlier finalization, and at most the tree's deposits.

Its root must be the root of the deposits it counts, so that a later snapshot holds that root.

Finalizing no deposit prunes nothing.

The reference implementation of the EIP checks none of this.

It also finalizes the first deposit when the count is zero.
-/
def finalize (tree : DepositTree) (eth1Data : Eth1Data) (executionBlockHeight : UInt64) :
    Except DepositTreeError DepositTree := do
  let count := eth1Data.depositCount.toNat
  if tree.mixInLength < count then throw (.finalizeBeyondCount count tree.mixInLength)
  let earlier := tree.tree.getFinalized.2
  if count < earlier then throw (.finalizeBelowFinalized count earlier)
  let sparse :=
    if count = 0 then tree.tree else tree.tree.finalize count DEPOSIT_CONTRACT_TREE_DEPTH.toNat
  let (roots, finalizedCount) := sparse.getFinalized
  let computed ← DepositTreeSnapshot.calculateRootOf roots finalizedCount
  if computed ≠ eth1Data.depositRoot then throw .rootMismatch
  return { tree with
    tree := sparse
    finalizedExecutionBlock := some (eth1Data.blockHash, executionBlockHeight) }

/-- The snapshot of a finalized tree. -/
def getSnapshot (tree : DepositTree) : Except DepositTreeError DepositTreeSnapshot :=
  match tree.finalizedExecutionBlock with
  | none => .error .notFinalized
  | some block =>
    let (finalized, count) := tree.tree.getFinalized
    DepositTreeSnapshot.fromTreeParts finalized count block

/--
The tree rebuilt from a snapshot.

The snapshot's root must be the root that its finalized roots and its count compute.
-/
def fromSnapshot (snapshot : DepositTreeSnapshot) : Except DepositTreeError DepositTree := do
  let computed ← snapshot.calculateRoot
  if snapshot.depositRoot ≠ computed then throw .rootMismatch
  let count := snapshot.depositCount.toNat
  let finalized := snapshot.finalized.data.toList
  match fromSnapshotParts finalized count DEPOSIT_CONTRACT_TREE_DEPTH.toNat with
  | some sparse =>
    return ⟨sparse, count, some (snapshot.executionBlockHash, snapshot.executionBlockHeight)⟩
  -- The root check has bounded the count by the capacity of the tree.
  | none => throw (.countBeyondCapacity count)

/--
The leaf at an index and its proof against the deposit root.

The proof is the branch from the leaf up, then the count as 32 little-endian bytes.

Only a deposit that the tree holds and has not finalized has a proof.

The reference implementation of the EIP proves an empty leaf for an index past the deposits.
-/
def getProof (tree : DepositTree) (index : Nat) :
    Except DepositTreeError (Root × Vector Root (DEPOSIT_CONTRACT_TREE_DEPTH.toNat + 1)) := do
  let finalized := tree.tree.getFinalized.2
  if index < finalized then throw (.proofOfFinalized index finalized)
  if tree.mixInLength ≤ index then throw (.proofBeyondCount index tree.mixInLength)
  match tree.tree.generateProof index DEPOSIT_CONTRACT_TREE_DEPTH.toNat with
  | some (leaf, branch) => return (leaf, branch.push (uintToBytes 32 tree.mixInLength))
  -- A tree that the operations build always holds a leaf at an index below its count.
  | none => throw (.proofBeyondCount index tree.mixInLength)

end DepositTree

end EthLib.Consensus
