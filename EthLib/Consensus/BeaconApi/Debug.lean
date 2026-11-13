module

public import EthLib.Consensus.BeaconApi.Committees
public import EthLib.Consensus.BeaconApi.Identifiers
public import EthLib.Consensus.BeaconApi.StateQueries

/-!
# `Consensus.BeaconApi.Debug`

The answers of the Beacon API that show the tree of the fork choice and its leaves.

The [fork choice endpoint] gives one view per node of the tree, with its parent node.

The [node type] fixes the fields of a view.

Before Gloas each block has one node, which the source calls full.

The [heads endpoint] gives the leaves of the tree.

SOUNDNESS.md records how this module reads the points that the source leaves open.

[fork choice endpoint]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/debug/fork_choice.v2.yaml
[node type]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/types/fork_choice.yaml
[heads endpoint]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/debug/heads.v2.yaml
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Lean Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- Whether the execution chain that a node ends at is verified. -/
inductive ExecutionValidity where
  /-- The execution layer found the chain valid, or the store trusts it. -/
  | valid
  /-- The execution layer found the chain invalid. -/
  | invalid
  /-- The execution layer has not yet judged the chain. -/
  | optimistic
  deriving DecidableEq, Repr

/-- The name of a validity in the API. -/
def ExecutionValidity.name : ExecutionValidity → String
  | .valid => "valid"
  | .invalid => "invalid"
  | .optimistic => "optimistic"

/-- The name of a payload status in the API. -/
def payloadStatusName : PayloadStatus → String
  | .pending => "pending"
  | .empty => "empty"
  | .full => "full"

/-- The view of one node of the fork choice, as the API gives it. -/
structure ForkChoiceNodeView where
  /-- The slot of the block. -/
  slot : Slot
  /-- The root of the block. -/
  blockRoot : Root
  /-- The status of the payload of the node, full for every node before Gloas. -/
  payloadStatus : PayloadStatus
  /-- The root of the block of the parent node. -/
  parentRoot : Root
  /-- The status of the payload of the parent node, or none when the tree does not hold it. -/
  parentPayloadStatus : Option PayloadStatus
  /-- The justified checkpoint of the state after the block. -/
  justifiedCheckpoint : Checkpoint
  /-- The finalized checkpoint of the state after the block. -/
  finalizedCheckpoint : Checkpoint
  /-- The weight of the node in Gwei. -/
  weight : Gwei
  /-- Whether the execution chain that the node ends at is verified. -/
  validity : ExecutionValidity
  /-- The block hash of the execution block that the node ends at. -/
  executionBlockHash : Hash32
  /-- The number of positions of the payload committee with a recorded vote. -/
  payloadAttesterCount : UInt64
  /-- The number of positions that vote that the payload came on time. -/
  payloadAvailabilityYesCount : UInt64
  /-- The number of positions that vote that the blob data is available. -/
  payloadDataAvailabilityYesCount : UInt64
  deriving DecidableEq, Repr

/-- A leaf of the tree, as the heads endpoint gives it. -/
structure ChainHead where
  /-- The root of the block of the leaf. -/
  root : Root
  /-- The slot of that block. -/
  slot : Slot
  /-- Whether the execution chain that one of its leaves ends at is not yet verified. -/
  executionOptimistic : Bool
  deriving DecidableEq, Repr

section Tree

variable (store : Store preset fork)

/-- Whether a node belongs to the tree of the store.

Its block must be in the store.

Before Gloas the node is pending, which stands for the block with its payload.

From Gloas a full node needs the verified payload of its block. -/
def isTreeNode (node : ForkChoiceNode) : Bool :=
  store.blocks.contains node.root &&
    if gloas : .glamsterdam ≤ fork then
      node.payloadStatus != .full || store.isPayloadVerified gloas node.root
    else node.payloadStatus == .pending

/-- The nodes of the block with a root: before Gloas its pending node alone.

From Gloas they are its pending and empty nodes, then its full node once its payload is verified. -/
def blockNodes (root : Root) : List ForkChoiceNode :=
  if gloas : .glamsterdam ≤ fork then
    ⟨root, .pending⟩ :: ⟨root, .empty⟩ ::
      if store.isPayloadVerified gloas root then [⟨root, .full⟩] else []
  else [⟨root, .pending⟩]

/-- The nodes of the tree, block by block in the order of roots. -/
def treeNodes : List ForkChoiceNode :=
  store.blocks.keys.flatMap (blockNodes store)

/-- The parent of a node by the links of the tree, whether the tree holds it or not.

From Gloas the parent of an empty or a full node is the pending node of its block.

The parent of another node is the node of the parent block that the block builds on.

It is none when the store lacks the block of the node.

It is also none when the parent is a node of the parent block, which the store lacks. -/
def parentLink (node : ForkChoiceNode) : Option ForkChoiceNode := do
  let block ← store.blocks[node.root]?
  if .glamsterdam ≤ fork ∧ node.payloadStatus ≠ .pending then return ⟨node.root, .pending⟩
  let parent ← store.blocks[block.parentRoot]?
  return ⟨block.parentRoot, Store.parentPayloadStatus block parent⟩

/-- The parent of a node in the tree, or none when the tree does not hold it. -/
def treeParent (node : ForkChoiceNode) : Option ForkChoiceNode :=
  (parentLink store node).filter (isTreeNode store)

/-- The leaves of the tree: its nodes without a child. -/
def treeLeaves : Except ForkChoiceError (List ForkChoiceNode) :=
  (treeNodes store).filterM fun node => return (← store.getNodeChildren node).isEmpty

/-- The three counts of the votes of the payload committee for a block.

The first counts the positions with a vote.

The second counts the positions that vote that the payload came on time.

The third counts the positions that vote that the blob data is available.

A member with two seats counts twice.

Before Gloas, and for a block without recorded votes, they are zero. -/
def ptcCounts (root : Root) : UInt64 × UInt64 × UInt64 :=
  if gloas : .glamsterdam ≤ fork then
    let noVotes := Vector.replicate preset.PTC_SIZE.toNat (none : Option Bool)
    let timely := ((store.payloadTimelinessVote gloas)[root]?).getD noVotes
    let available := ((store.payloadDataAvailabilityVote gloas)[root]?).getD noVotes
    (UInt64.ofNat (timely.toList.countP (·.isSome)),
      UInt64.ofNat (timely.toList.countP (· == some true)),
      UInt64.ofNat (available.toList.countP (· == some true)))
  else (0, 0, 0)

/-- The block hash of the execution block that a node ends at.

A full node from Gloas ends at the block hash of its bid.

A pending or empty node from Gloas ends at the parent block hash of its bid.

Before Gloas a node ends at the block hash of its payload, and at zero before Bellatrix. -/
def nodeBlockHash (node : ForkChoiceNode) (block : BeaconBlock preset fork) : Hash32 :=
  if gloas : .glamsterdam ≤ fork then
    let bid := (block.body.signedExecutionPayloadBid gloas).message
    if node.payloadStatus = .full then bid.blockHash else bid.parentBlockHash
  else if range : .bellatrix ≤ fork then
    (block.body.executionPayload ⟨range, Nat.lt_of_not_le gloas⟩).blockHash
  else Vector.replicate 32 0

end Tree

/-- Whether the execution chain that a node ends at is optimistic.

Before Gloas, and for a full node from Gloas, the chain ends at the payload of the block.

A pending or empty node from Gloas ends at the payload that its block builds on.

A payload that its block builds on outside the store came before the anchor, which is trusted.

It fails when the payload chain of the block cannot be read. -/
def nodeValidity (optimistic : OptimisticStore preset fork) (node : ForkChoiceNode) :
    Except ForkChoiceError ExecutionValidity := do
  let ends ← if .glamsterdam ≤ fork ∧ node.payloadStatus ≠ .full then
      pure (← optimistic.payloadChain node.root)[1]?
    else pure (some node.root)
  return if ends.any optimistic.isOptimistic then .optimistic else .valid

/-- The status of a node in the API: before Gloas every node is full. -/
def apiPayloadStatus (fork : Fork) (status : PayloadStatus) : PayloadStatus :=
  if .glamsterdam ≤ fork then status else .full

/-- The view of a node of the tree.

The weight is the one of the head computation, read from the votes of the given tally.

The checkpoints are those of the state after the block. -/
def nodeView (config : Config) (store : Store preset fork)
    (optimistic : OptimisticStore preset fork) (tally : Except ForkChoiceError VoteTally)
    (node : ForkChoiceNode) :
    Except ForkChoiceError ForkChoiceNodeView := do
  let block ← store.block node.root
  let state ← store.blockState node.root
  let parentRoot :=
    if .glamsterdam ≤ fork ∧ node.payloadStatus ≠ .pending then node.root else block.parentRoot
  let (attesters, timely, available) := ptcCounts store node.root
  return {
    slot := block.slot
    blockRoot := node.root
    payloadStatus := apiPayloadStatus fork node.payloadStatus
    parentRoot
    parentPayloadStatus := (treeParent store node).map (apiPayloadStatus fork ·.payloadStatus)
    justifiedCheckpoint := state.currentJustifiedCheckpoint
    finalizedCheckpoint := state.finalizedCheckpoint
    weight := ← store.getWeight config tally node
    validity := ← nodeValidity optimistic node
    executionBlockHash := nodeBlockHash node block
    payloadAttesterCount := attesters
    payloadAvailabilityYesCount := timely
    payloadDataAvailabilityYesCount := available }

/-- The views of the nodes of the tree, block by block in the order of roots.

The weights read the votes of the justified state, tallied once for every weight. -/
def nodeViews (config : Config) (store : Store preset fork)
    (optimistic : OptimisticStore preset fork) : Except ForkChoiceError (List ForkChoiceNodeView) :=
  (treeNodes store).mapM (nodeView config store optimistic store.justifiedTally)

/-- The leaves of the tree by the roots of their blocks, each once, in the order of roots.

From Gloas a block is listed when its empty or its full node is a leaf.

Its flag is set when the execution chain that one of those leaves ends at is optimistic. -/
def chainHeads (store : Store preset fork) (optimistic : OptimisticStore preset fork) :
    Except ForkChoiceError (List ChainHead) := do
  let leaves ← treeLeaves store
  (leaves.map (·.root)).eraseDups.mapM fun root => do
    let block ← store.block root
    let validities ← (leaves.filter (·.root = root)).mapM (nodeValidity optimistic)
    return { root, slot := block.slot, executionOptimistic := validities.contains .optimistic }

/-! ## Responses -/

/-- The JSON object of a checkpoint. -/
def checkpointJson (checkpoint : Checkpoint) : Json :=
  Json.mkObj [("epoch", uintJson checkpoint.epoch), ("root", .str (toHex checkpoint.root.toArray))]

/-- The JSON object of a node view, with empty extra data. -/
def ForkChoiceNodeView.toJson (view : ForkChoiceNodeView) : Json :=
  Json.mkObj [
    ("slot", uintJson view.slot),
    ("block_root", .str (toHex view.blockRoot.toArray)),
    ("payload_status", .str (payloadStatusName view.payloadStatus)),
    ("parent_root", .str (toHex view.parentRoot.toArray)),
    ("parent_payload_status",
      (view.parentPayloadStatus.map fun status => Json.str (payloadStatusName status)).getD .null),
    ("justified_checkpoint", checkpointJson view.justifiedCheckpoint),
    ("finalized_checkpoint", checkpointJson view.finalizedCheckpoint),
    ("weight", uintJson view.weight),
    ("validity", .str view.validity.name),
    ("execution_block_hash", .str (toHex view.executionBlockHash.toArray)),
    ("payload_attester_count", uintJson view.payloadAttesterCount),
    ("payload_availability_yes_count", uintJson view.payloadAvailabilityYesCount),
    ("payload_data_availability_yes_count", uintJson view.payloadDataAvailabilityYesCount),
    ("extra_data", Json.mkObj [])]

/-- The JSON object of a leaf. -/
def ChainHead.toJson (head : ChainHead) : Json :=
  Json.mkObj [("root", .str (toHex head.root.toArray)), ("slot", uintJson head.slot),
    ("execution_optimistic", .bool head.executionOptimistic)]

/-- The response of the fork choice endpoint, or the error with code 500.

It holds the checkpoints of the store, and the view of each node, with empty extra data. -/
def forkChoiceResponse (config : Config) (store : Store preset fork)
    (optimistic : OptimisticStore preset fork) : Except ErrorMessage ApiEnvelope := do
  let views ← (nodeViews config store optimistic).mapError fun e => internalError (reprStr e)
  return { data := Json.mkObj [
    ("justified_checkpoint", checkpointJson store.justifiedCheckpoint),
    ("finalized_checkpoint", checkpointJson store.finalizedCheckpoint),
    ("fork_choice_nodes", .arr (views.map (·.toJson)).toArray),
    ("extra_data", Json.mkObj [])] }

/-- The response of the heads endpoint, or the error with code 500. -/
def chainHeadsResponse (store : Store preset fork) (optimistic : OptimisticStore preset fork) :
    Except ErrorMessage ApiEnvelope := do
  let heads ← (chainHeads store optimistic).mapError fun e => internalError (reprStr e)
  return { data := .arr (heads.map (·.toJson)).toArray }

end EthLib.Consensus.BeaconApi
