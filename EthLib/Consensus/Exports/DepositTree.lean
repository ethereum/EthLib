module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Consensus.DepositTree

/-!
# `Exports.DepositTree`

C-ABI exports of the deposit tree and its snapshot.

A tree crosses the boundary as a tuple of its sparse tree, its count and its finalized block.

The sparse tree is a list of its subtrees in preorder, each one a tagged tuple.

So the Python form of a tree follows the constructors of the sparse tree.

Python holds that tuple, and every export decodes it again.

It accepts only a tree that the operations on deposit trees build.

Each call reads the whole tree, so a caller pushes many deposits in one call.

A snapshot crosses the boundary as the tuple of its five fields, in order.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz
open EthLib.Exports (Result PyValue pyExport ToPy FromPy FromPyItems toPy fromPy)

/-- The result of a deposit tree operation, with the code and the text of its error. -/
def runDepositTree {α : Type} (result : Except DepositTreeError α) : Result α :=
  result.mapError fun e => (e.code, reprStr e)

/-- The subtrees of a sparse tree in preorder, each one a tagged tuple. -/
def depositMerkleTreeItems : DepositMerkleTree → List PyValue
  | .zero height => [toPy ("zero", height)]
  | .leaf hash => [toPy ("leaf", hash)]
  | .finalized count hash => [toPy ("finalized", count, hash)]
  | .node left right =>
    toPy "node" :: (depositMerkleTreeItems left ++ depositMerkleTreeItems right)

/--
The subtrees on a stack, with one more item of a preorder read from the end.

A node takes the two subtrees on top: the left one on top, the right one below it.
-/
def pushDepositMerkleTreeItem (stack : List DepositMerkleTree) (item : PyValue) :
    Except String (List DepositMerkleTree) :=
  match (fromPy item : Except String String) with
  | .ok "node" =>
    match stack with
    | left :: right :: rest => .ok (.node left right :: rest)
    | _ => .error "a node needs two subtrees"
  | _ =>
    match (fromPy item : Except String (String × Nat × Root)) with
    | .ok ("finalized", count, hash) => .ok (.finalized count hash :: stack)
    | _ =>
      match (fromPy item : Except String (String × Root)) with
      | .ok ("leaf", hash) => .ok (.leaf hash :: stack)
      | _ =>
        match (fromPy item : Except String (String × Nat)) with
        | .ok ("zero", height) => .ok (.zero height :: stack)
        | _ => .error "expected a tagged subtree"

/-- The sparse tree whose preorder these items are. -/
def depositMerkleTreeOfItems (items : List PyValue) : Except String DepositMerkleTree := do
  match ← items.reverse.foldlM pushDepositMerkleTreeItem [] with
  | [tree] => .ok tree
  | _ => .error "expected exactly one tree"

/-- The deposits of a sparse tree that are not finalized, from left to right. -/
def pendingLeaves : DepositMerkleTree → List Root
  | .leaf hash => [hash]
  | .node left right => pendingLeaves left ++ pendingLeaves right
  | _ => []

/--
The tree that the operations build from the finalized roots and pending deposits of a tree.

It rebuilds the finalized part from its roots, then pushes the pending deposits in order.
-/
def canonicalDepositMerkleTree (tree : DepositMerkleTree) : Option DepositMerkleTree := do
  let (roots, finalized) := tree.getFinalized
  let base ← DepositMerkleTree.fromSnapshotParts roots finalized DEPOSIT_CONTRACT_TREE_DEPTH.toNat
  (pendingLeaves tree).foldlM (fun built leaf => built.pushLeaf leaf) base

/-- A deposit tree as the tuple of its sparse tree, its count and its finalized block. -/
abbrev DepositTreeValue := List PyValue × Nat × Option (Hash32 × UInt64)

/-- The value of a deposit tree. -/
def depositTreeToValue (tree : DepositTree) : DepositTreeValue :=
  (depositMerkleTreeItems tree.tree, tree.mixInLength, tree.finalizedExecutionBlock)

/--
The deposit tree of a value, if the operations on deposit trees can build it.

The sparse tree is the one that its finalized roots and pending deposits rebuild.

The count is that of its deposits, below `2^32`, and finalized deposits come with a finalized block.
-/
def depositTreeOfValue (value : DepositTreeValue) : Result DepositTree := do
  let (items, mixInLength, finalizedExecutionBlock) := value
  let tree ← (depositMerkleTreeOfItems items).mapError fun message => (0, message)
  if canonicalDepositMerkleTree tree ≠ some tree then
    throw (0, "the subtrees do not have the shape of a deposit tree")
  let finalized := tree.getFinalized.2
  let count := finalized + (pendingLeaves tree).length
  if count ≠ mixInLength then throw (0, s!"the tree holds {count} deposits, not {mixInLength}")
  if 2 ^ DEPOSIT_CONTRACT_TREE_DEPTH.toNat ≤ count then
    throw (0, s!"a tree holds fewer than 2^{DEPOSIT_CONTRACT_TREE_DEPTH} deposits")
  if finalized ≠ 0 ∧ finalizedExecutionBlock.isNone then
    throw (0, "a tree with finalized deposits has a finalized block")
  return { tree, mixInLength, finalizedExecutionBlock }

/-- A snapshot as the tuple of its fields, in order. -/
abbrev DepositTreeSnapshotValue := List Hash32 × Hash32 × UInt64 × Hash32 × UInt64

/-- The value of a snapshot. -/
def depositTreeSnapshotToValue (snapshot : DepositTreeSnapshot) : DepositTreeSnapshotValue :=
  (snapshot.finalized.data.toList, snapshot.depositRoot, snapshot.depositCount,
    snapshot.executionBlockHash, snapshot.executionBlockHeight)

/-- The snapshot of a value, whose finalized roots number at most the depth of the tree. -/
def depositTreeSnapshotOfValue (value : DepositTreeSnapshotValue) :
    Result DepositTreeSnapshot := do
  let (finalized, depositRoot, depositCount, executionBlockHash, executionBlockHeight) := value
  if bound : finalized.toArray.size ≤ DEPOSIT_CONTRACT_TREE_DEPTH.toNat then
    return ⟨⟨finalized.toArray, bound⟩, depositRoot, depositCount, executionBlockHash,
      executionBlockHeight⟩
  else
    throw (0, s!"a snapshot holds at most {DEPOSIT_CONTRACT_TREE_DEPTH} finalized roots")

/-- The tree with no deposit. -/
@[export eth_consensus_deposit_tree_new]
def depositTreeNewExport (args : PyValue) : Result PyValue :=
  match args with
  | .tuple #[] => .ok (toPy (depositTreeToValue DepositTree.new))
  | _ => .error (0, "expected no argument")

/-- The tree with one more deposit, by the root of its data. -/
@[export eth_consensus_deposit_tree_push_leaf]
def depositTreePushLeafExport (args : PyValue) : Result PyValue :=
  pyExport (fun ((value, leaf) : DepositTreeValue × Root) => do
    let tree ← depositTreeOfValue value
    return depositTreeToValue (← runDepositTree (tree.pushLeaf leaf))) args

/-- The tree after pushing deposits in order, by the roots of their data. -/
@[export eth_consensus_deposit_tree_push_leaves]
def depositTreePushLeavesExport (args : PyValue) : Result PyValue :=
  pyExport (fun ((value, leaves) : DepositTreeValue × List Root) => do
    let tree ← depositTreeOfValue value
    return depositTreeToValue (← runDepositTree (tree.pushLeaves leaves))) args

/-- The deposit root of a tree. -/
@[export eth_consensus_deposit_tree_get_root]
def depositTreeGetRootExport (args : PyValue) : Result PyValue :=
  letI : FromPyItems DepositTreeValue := EthLib.Exports.instFromPyItemsOfFromPy
  pyExport (fun value => do return (← depositTreeOfValue value).getRoot) args

/-- The tree finalized at deposit data, given as its root, count and block hash, and a height. -/
@[export eth_consensus_deposit_tree_finalize]
def depositTreeFinalizeExport (args : PyValue) : Result PyValue :=
  pyExport (fun ((value, (depositRoot, depositCount, blockHash), height) :
      DepositTreeValue × (Root × UInt64 × Hash32) × UInt64) => do
    let tree ← depositTreeOfValue value
    let eth1Data : Eth1Data := { depositRoot, depositCount, blockHash }
    return depositTreeToValue (← runDepositTree (tree.finalize eth1Data height))) args

/-- The leaf at an index of a tree, and its proof against the deposit root. -/
@[export eth_consensus_deposit_tree_get_proof]
def depositTreeGetProofExport (args : PyValue) : Result PyValue :=
  pyExport (fun ((value, index) : DepositTreeValue × Nat) => do
    let tree ← depositTreeOfValue value
    let (leaf, proof) ← runDepositTree (tree.getProof index)
    return (leaf, proof.toList)) args

/-- The snapshot of a finalized tree. -/
@[export eth_consensus_deposit_tree_get_snapshot]
def depositTreeGetSnapshotExport (args : PyValue) : Result PyValue :=
  letI : FromPyItems DepositTreeValue := EthLib.Exports.instFromPyItemsOfFromPy
  pyExport (fun value => do
    let tree ← depositTreeOfValue value
    return depositTreeSnapshotToValue (← runDepositTree tree.getSnapshot)) args

/-- The tree rebuilt from a snapshot. -/
@[export eth_consensus_deposit_tree_from_snapshot]
def depositTreeFromSnapshotExport (args : PyValue) : Result PyValue :=
  letI : FromPyItems DepositTreeSnapshotValue := EthLib.Exports.instFromPyItemsOfFromPy
  pyExport (fun value => do
    let snapshot ← depositTreeSnapshotOfValue value
    return depositTreeToValue (← runDepositTree (DepositTree.fromSnapshot snapshot))) args

/-- The deposit root that the finalized roots and the count of a snapshot compute. -/
@[export eth_consensus_deposit_tree_snapshot_calculate_root]
def depositTreeSnapshotCalculateRootExport (args : PyValue) : Result PyValue :=
  letI : FromPyItems DepositTreeSnapshotValue := EthLib.Exports.instFromPyItemsOfFromPy
  pyExport (fun value => do
    let snapshot ← depositTreeSnapshotOfValue value
    runDepositTree snapshot.calculateRoot) args

end EthLib.Consensus.Exports
