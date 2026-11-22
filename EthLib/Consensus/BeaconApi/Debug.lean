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

[fork choice endpoint]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/debug/fork_choice.v2.yaml
[node type]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/types/fork_choice.yaml
[heads endpoint]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/debug/heads.v2.yaml
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

/-- Whether a node belongs to the tree of the store. -/
def isTreeNode (node : ForkChoiceNode) : Bool :=
  -- Its block must be in the store.
  store.blocks.contains node.root &&
    -- From Gloas, a full node needs the verified payload of its block.
    if gloas : .glamsterdam ≤ fork then
      node.payloadStatus != .full || store.isPayloadVerified gloas node.root
    -- Before Gloas the node is pending, which stands for the block with its payload.
    else node.payloadStatus == .pending

/-- The nodes of the block with a root. -/
def blockNodes (root : Root) : List ForkChoiceNode :=
  -- The source: one node per pair of a block root and a payload status.
  --
  -- From Gloas: the pending and empty nodes, then the full node once the payload is verified.
  if gloas : .glamsterdam ≤ fork then
    ⟨root, .pending⟩ :: ⟨root, .empty⟩ ::
      if store.isPayloadVerified gloas root then [⟨root, .full⟩] else []
  -- The source: before Gloas a block has a single node, which the API calls full.
  --
  -- EthLib keeps it as the pending node, and the view shows it as full.
  else [⟨root, .pending⟩]

/-- The nodes of the tree, block by block in the order of roots. -/
def treeNodes : List ForkChoiceNode :=
  -- The source fixes no order; EthLib lists the blocks in the order of their roots.
  store.blocks.keys.flatMap (blockNodes store)

/-- The parent of a node by the links of the tree, whether the tree holds it or not. -/
def parentLink (node : ForkChoiceNode) : Option ForkChoiceNode := do
  -- None when the store lacks the block of the node.
  let block ← store.blocks[node.root]?
  -- The source: from Gloas, the parent of an empty or a full node is the pending node of its block.
  if .glamsterdam ≤ fork ∧ node.payloadStatus ≠ .pending then return ⟨node.root, .pending⟩
  -- Otherwise the parent is the node of the parent block that the block builds on.
  --
  -- None when the store lacks the parent block.
  let parent ← store.blocks[block.parentRoot]?
  return ⟨block.parentRoot, Store.parentPayloadStatus block parent⟩

/-- The parent of a node in the tree, or none when the tree does not hold it. -/
def treeParent (node : ForkChoiceNode) : Option ForkChoiceNode :=
  -- The source: null when the parent is not retained in the tree.
  (parentLink store node).filter (isTreeNode store)

/-- The leaves of the tree: its nodes without a child. -/
def treeLeaves : Except ForkChoiceError (List ForkChoiceNode) :=
  -- The source: the leaves of the tree of the fork choice, read as the nodes without a child.
  (treeNodes store).filterM fun node => return (← store.getNodeChildren node).isEmpty

/-- The three counts of the votes of the payload committee for a block. -/
def ptcCounts (root : Root) : UInt64 × UInt64 × UInt64 :=
  -- The source: counts per position of the committee, so a member with two seats counts twice.
  --
  -- The source: the counts are the same for all nodes of a block.
  if gloas : .glamsterdam ≤ fork then
    -- A block without recorded votes has no vote at any position.
    let noVotes := Vector.replicate preset.PTC_SIZE.toNat (none : Option Bool)
    let timely := ((store.payloadTimelinessVote gloas)[root]?).getD noVotes
    let available := ((store.payloadDataAvailabilityVote gloas)[root]?).getD noVotes
    -- The positions with a recorded vote.
    --
    -- A vote records both of its answers, so the positions of the timeliness votes are those.
    (UInt64.ofNat (timely.toList.countP (·.isSome)),
      -- The positions that vote that the payload came on time.
      UInt64.ofNat (timely.toList.countP (· == some true)),
      -- The positions that vote that the blob data is available.
      UInt64.ofNat (available.toList.countP (· == some true)))
  -- The source: zero for a block before Gloas.
  else (0, 0, 0)

/-- The block hash of the execution block that a node ends at. -/
def nodeBlockHash (node : ForkChoiceNode) (block : BeaconBlock preset fork) : Hash32 :=
  if gloas : .glamsterdam ≤ fork then
    let bid := (block.body.signedExecutionPayloadBid gloas).message
    -- The source: a full node gives the hash of the execution payload of its block.
    --
    -- From Gloas, EthLib reads that hash from the bid of the block.
    --
    -- The source: a pending or empty node from Gloas gives the parent block hash of the bid.
    if node.payloadStatus = .full then bid.blockHash else bid.parentBlockHash
  -- The source: before Gloas every node is full, and gives the block hash of its payload.
  else if range : .bellatrix ≤ fork then
    (block.body.executionPayload ⟨range, Nat.lt_of_not_le gloas⟩).blockHash
  -- Before Bellatrix a block has no payload; EthLib's choice is the zero hash.
  else Vector.replicate 32 0

end Tree

/-- Whether the execution chain that a node ends at is optimistic.

It fails when the payload chain of the block cannot be read. -/
def nodeValidity (optimistic : OptimisticStore preset fork) (node : ForkChoiceNode) :
    Except ForkChoiceError ExecutionValidity := do
  -- The source: the validity of the chain that ends at the execution block hash of the node.
  --
  -- A pending or empty node from Gloas ends at the payload that its block builds on.
  --
  -- That payload is the second entry of the payload chain of the block.
  let ends ← if .glamsterdam ≤ fork ∧ node.payloadStatus ≠ .full then
      pure (← optimistic.payloadChain node.root)[1]?
    -- Before Gloas, and for a full node from Gloas, the chain ends at the payload of the block.
    else pure (some node.root)
  -- A payload outside the store came before the anchor, which is trusted, so it is valid.
  --
  -- EthLib never gives invalid, since the store drops the blocks on an invalid payload.
  return if ends.any optimistic.isOptimistic then .optimistic else .valid

/-- The status of a node in the API: before Gloas every node is full. -/
def apiPayloadStatus (fork : Fork) (status : PayloadStatus) : PayloadStatus :=
  -- The source: each block before Gloas has a single full node.
  if .glamsterdam ≤ fork then status else .full

/-- The view of a node of the tree, with the votes of the given tally. -/
def nodeView (config : Config) (store : Store preset fork)
    (optimistic : OptimisticStore preset fork) (tally : Except ForkChoiceError VoteTally)
    (node : ForkChoiceNode) :
    Except ForkChoiceError ForkChoiceNodeView := do
  let block ← store.block node.root
  let state ← store.blockState node.root
  -- The source: for an empty or a full node from Gloas, the parent root is the block root.
  --
  -- Otherwise it is the parent root of the block.
  let parentRoot :=
    if .glamsterdam ≤ fork ∧ node.payloadStatus ≠ .pending then node.root else block.parentRoot
  let (attesters, timely, available) := ptcCounts store node.root
  -- The fields that the node type of the source lists.
  return {
    slot := block.slot
    blockRoot := node.root
    payloadStatus := apiPayloadStatus fork node.payloadStatus
    parentRoot
    -- The source: null when the parent node is not in the tree.
    parentPayloadStatus := (treeParent store node).map (apiPayloadStatus fork ·.payloadStatus)
    -- The source: the checkpoints recorded for the node.
    --
    -- EthLib reads them as those of the state after the block.
    justifiedCheckpoint := state.currentJustifiedCheckpoint
    finalizedCheckpoint := state.finalizedCheckpoint
    -- The source: the raw stored weight of the node.
    --
    -- EthLib gives the weight of the head computation, from the votes of the tally.
    weight := ← store.getWeight config tally node
    validity := ← nodeValidity optimistic node
    executionBlockHash := nodeBlockHash node block
    payloadAttesterCount := attesters
    payloadAvailabilityYesCount := timely
    payloadDataAvailabilityYesCount := available }

/-- The views of the nodes of the tree, block by block in the order of roots. -/
def nodeViews (config : Config) (store : Store preset fork)
    (optimistic : OptimisticStore preset fork) : Except ForkChoiceError (List ForkChoiceNodeView) :=
  -- The weights read the votes of the justified state, tallied once and shared by every node.
  (treeNodes store).mapM (nodeView config store optimistic store.justifiedTally)

/-- The leaves of the tree by the roots of their blocks, each once, in the order of roots. -/
def chainHeads (store : Store preset fork) (optimistic : OptimisticStore preset fork) :
    Except ForkChoiceError (List ChainHead) := do
  let leaves ← treeLeaves store
  -- The source gives a root per head and no payload status; EthLib lists each block once.
  --
  -- From Gloas a block is listed when its empty or its full node is a leaf.
  (leaves.map (·.root)).eraseDups.mapM fun root => do
    let block ← store.block root
    -- The flag is set when the chain that one of its leaves ends at is optimistic.
    let validities ← (leaves.filter (·.root = root)).mapM (nodeValidity optimistic)
    -- The source: the root, the slot and the optimistic flag of the head.
    return { root, slot := block.slot, executionOptimistic := validities.contains .optimistic }

/-! ## Responses -/

/-- The JSON object of a checkpoint. -/
def checkpointJson (checkpoint : Checkpoint) : Json :=
  Json.mkObj [("epoch", uintJson checkpoint.epoch), ("root", .str (toHex checkpoint.root.toArray))]

/-- The JSON object of a node view, with empty extra data. -/
def ForkChoiceNodeView.toJson (view : ForkChoiceNodeView) : Json :=
  -- The fields that the node type lists, each integer as a quoted decimal and each root as hex.
  --
  -- The source lets the extra data vary, or be an empty object; EthLib gives an empty object.
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

/-- The response of the fork choice endpoint, or the error with code 500. -/
def forkChoiceResponse (config : Config) (store : Store preset fork)
    (optimistic : OptimisticStore preset fork) : Except ErrorMessage ApiEnvelope := do
  -- Any failed read of the store gives code 500, the internal error that the source lists.
  let views ← (nodeViews config store optimistic).mapError fun _ =>
    internalError "no fork choice nodes"
  -- The source: the checkpoints of the store, the view of each node, and empty extra data.
  return { data := Json.mkObj [
    ("justified_checkpoint", checkpointJson store.justifiedCheckpoint),
    ("finalized_checkpoint", checkpointJson store.finalizedCheckpoint),
    ("fork_choice_nodes", .arr (views.map (·.toJson)).toArray),
    ("extra_data", Json.mkObj [])] }

/-- The response of the heads endpoint, or the error with code 500. -/
def chainHeadsResponse (store : Store preset fork) (optimistic : OptimisticStore preset fork) :
    Except ErrorMessage ApiEnvelope := do
  -- Any failed read of the store gives code 500, the internal error that the source lists.
  let heads ← (chainHeads store optimistic).mapError fun _ => internalError "no chain heads"
  -- The source: the array of the heads under the data key.
  return { data := .arr (heads.map (·.toJson)).toArray }

end EthLib.Consensus.BeaconApi
