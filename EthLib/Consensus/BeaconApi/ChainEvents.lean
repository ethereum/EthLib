module

public import EthLib.Consensus.BeaconApi.Debug
public import EthLib.Consensus.BeaconApi.Duties
public import EthLib.Consensus.BeaconApi.Events
public import EthLib.Consensus.ForkChoice.FastConfirmation

/-!
# `Consensus.BeaconApi.ChainEvents`

The events that a beacon node sends when its fork choice changes.

A new head, a new finalized checkpoint and a reorganization follow from two stores.

The node sends the head event again when the payload of the head block arrives.

Each run of the fast confirmation rule sends the confirmed block, whether it changed or not.

The [event stream] gives the topics and the fields of each event.

[event stream]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/apis/eventstream/index.yaml
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Lean Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- A new head of the fork choice, with the status of its payload. -/
structure HeadEvent where
  /-- The slot of the head block. -/
  slot : Slot
  /-- The root of the head block. -/
  block : Root
  /-- The state root of the head block. -/
  state : Root
  /-- The status of the payload of the head, full before Gloas. -/
  payloadStatus : PayloadStatus
  /-- Whether the head is in another epoch than the head before it. -/
  epochTransition : Bool
  /-- The root on which the attester duties of the epoch of the head depend. -/
  currentEpochDependentRoot : Root
  /-- The root on which the attester duties of the next epoch depend. -/
  nextEpochDependentRoot : Root
  /-- Whether the payload of the head block is not yet verified. -/
  executionOptimistic : Bool
  deriving DecidableEq, Repr

/-- A new finalized checkpoint of the fork choice. -/
structure FinalizedCheckpointEvent where
  /-- The root of the block of the checkpoint. -/
  block : Root
  /-- The state root of that block. -/
  state : Root
  /-- The epoch of the checkpoint. -/
  epoch : Epoch
  /-- Whether the payload of that block is not yet verified. -/
  executionOptimistic : Bool
  deriving DecidableEq, Repr

/-- A new head that does not descend from the head before it. -/
structure ChainReorgEvent where
  /-- The slot of the new head. -/
  slot : Slot
  /-- The slots from the latest common ancestor of the two heads up to the old head.

The walk to that ancestor stops after as many steps as the slot of the old head. -/
  depth : UInt64
  /-- The root of the old head block. -/
  oldHeadBlock : Root
  /-- The root of the new head block. -/
  newHeadBlock : Root
  /-- The state root of the old head block. -/
  oldHeadState : Root
  /-- The state root of the new head block. -/
  newHeadState : Root
  /-- The epoch of the new head. -/
  epoch : Epoch
  /-- Whether the payload of the new head block is not yet verified. -/
  executionOptimistic : Bool
  deriving DecidableEq, Repr

/-- One run of the fast confirmation rule. -/
structure FastConfirmationEvent where
  /-- The root of the most recent confirmed block. -/
  block : Root
  /-- The slot of that block. -/
  slot : Slot
  /-- The slot of the clock when the rule ran. -/
  currentSlot : Slot
  deriving DecidableEq, Repr

/-- An event of the fork choice. -/
inductive ChainEvent where
  /-- A new head, or the same head block with its payload. -/
  | head (event : HeadEvent)
  /-- A new finalized checkpoint. -/
  | finalizedCheckpoint (event : FinalizedCheckpointEvent)
  /-- A new head that does not descend from the old one. -/
  | chainReorg (event : ChainReorgEvent)
  /-- One run of the fast confirmation rule. -/
  | fastConfirmation (event : FastConfirmationEvent)
  deriving DecidableEq, Repr

namespace ChainEvent

/-- The topic of an event. -/
def topic : ChainEvent → EventTopic
  -- EthLib's choice: a new head goes on the head topic of version 2 only.
  --
  -- The source deprecates the first head topic in its favour.
  | .head _ => .headV2
  | .finalizedCheckpoint _ => .finalizedCheckpoint
  | .chainReorg _ => .chainReorg
  | .fastConfirmation _ => .fastConfirmation

/-- A root as the API writes it. -/
def rootJson (root : Root) : Json := .str (toHex ⟨root.toArray⟩)

/-- The data of an event, as JSON. -/
def data (fork : Fork) : ChainEvent → Json
  -- The fields of each event are those of its example in the source.
  --
  -- A slot, an epoch or a depth is a quoted decimal integer, and a root is hex after `0x`.
  | .head e =>
    let fields := Json.mkObj [("slot", uintJson e.slot), ("block", rootJson e.block),
      ("state", rootJson e.state), ("payload_status", .str (payloadStatusName e.payloadStatus)),
      ("epoch_transition", .bool e.epochTransition),
      ("current_epoch_dependent_root", rootJson e.currentEpochDependentRoot),
      ("next_epoch_dependent_root", rootJson e.nextEpochDependentRoot),
      ("execution_optimistic", .bool e.executionOptimistic)]
    -- The head event of version 2 puts its fields under the data key, beside the version.
    { version := fork.consensusVersion?, data := fields : ApiEnvelope }.toJson
  | .finalizedCheckpoint e =>
    .mkObj [("block", rootJson e.block), ("state", rootJson e.state), ("epoch", uintJson e.epoch),
      ("execution_optimistic", .bool e.executionOptimistic)]
  | .chainReorg e =>
    .mkObj [("slot", uintJson e.slot), ("depth", uintJson e.depth),
      ("old_head_block", rootJson e.oldHeadBlock), ("new_head_block", rootJson e.newHeadBlock),
      ("old_head_state", rootJson e.oldHeadState), ("new_head_state", rootJson e.newHeadState),
      ("epoch", uintJson e.epoch), ("execution_optimistic", .bool e.executionOptimistic)]
  -- The source: the confirmed block, its slot, and the slot of the clock when the rule ran.
  | .fastConfirmation e =>
    .mkObj [("block", rootJson e.block), ("slot", uintJson e.slot),
      ("current_slot", uintJson e.currentSlot)]

/-- The event of the stream that an event of the fork choice gives. -/
def toApiEvent (fork : Fork) (event : ChainEvent) : ApiEvent :=
  ⟨event.topic, event.data fork⟩

end ChainEvent

/-- Why the events of a change of the fork choice cannot be given. -/
inductive ChainEventError where
  /-- A read of a store fails. -/
  | forkChoice (fault : ForkChoiceError)
  /-- A dependent root of the head state cannot be read. -/
  | dependentRoot (fault : ErrorMessage)
  deriving Repr

/-- The slot of the latest ancestor of a block that is also an ancestor of a node.

It fails when the store does not hold a block of the walk. -/
def commonAncestorSlot (store : Store preset fork) (node : ForkChoiceNode) :
    Nat → Root → Except ForkChoiceError Slot
  -- No step left: the walk stops at the block it reached.
  | 0, root => return (← store.block root).slot
  | steps + 1, root => do
    let block ← store.block root
    -- A block that is an ancestor of the node is the common ancestor.
    if ← store.isAncestor node ⟨root, .pending⟩ then return block.slot
    -- Else the walk goes on from the parent block, with one step less.
    else commonAncestorSlot store node steps block.parentRoot

/-- The head event of a head of a store, given the slot of the head before it. -/
def headEvent (store : Store preset fork) (optimistic : Root → Bool) (genesisRoot : Root)
    (previousSlot : Slot) (head : ForkChoiceNode) : Except ChainEventError HeadEvent := do
  -- The head block and its post state, which the store holds.
  let block ← (store.block head.root).mapError .forkChoice
  let state ← (store.blockState head.root).mapError .forkChoice
  -- The source: epoch is the epoch of the slot of the head block.
  let epoch := computeEpochAtSlot preset block.slot
  -- The source: the current epoch dependent root is the root at slot start(epoch - 1) - 1.
  --
  -- Here start(e) is the first slot of epoch e.
  --
  -- The source: on underflow, before the first epoch or slot, the root of the genesis block.
  let current ← (dependentRoot state 1 epoch genesisRoot).mapError .dependentRoot
  -- The source: the next epoch dependent root is the root at slot start(epoch) - 1.
  --
  -- The attester duties of the epoch of the head and of the next one depend on these two roots.
  let next ← (dependentRoot state 0 epoch genesisRoot).mapError .dependentRoot
  -- The slot, the root and the state root of the head block.
  return { slot := block.slot, block := head.root, state := block.stateRoot,
           -- The source: full for every head block before Gloas.
           payloadStatus := apiPayloadStatus fork head.payloadStatus,
           -- The source does not define the epoch transition.
           --
           -- EthLib reads it as an epoch of the head other than the epoch of the old head.
           epochTransition := computeEpochAtSlot preset previousSlot != epoch,
           currentEpochDependentRoot := current, nextEpochDependentRoot := next,
           -- Whether the payload of the head block is not yet verified.
           executionOptimistic := optimistic head.root }

/-- Whether a head event follows a change of the head. -/
def headChanged (before after : ForkChoiceNode) : Bool :=
  -- A new head block gives a head event.
  --
  -- The source: the same head block gives a second one when its payload moves from empty to full.
  --
  -- The source leaves the other moves of the payload status optional; EthLib sends nothing.
  before.root != after.root ||
    (before.payloadStatus == .empty && after.payloadStatus == .full)

/-- The events of the fork choice that a change of its store gives, in order.

The optimistic flag of a block tells whether its payload is not yet verified. -/
def chainEvents (config : Config) (optimistic : Root → Bool) (genesisRoot : Root)
    (before after : Store preset fork) : Except ChainEventError (List ChainEvent) := do
  let lift {α : Type} (x : Except ForkChoiceError α) : Except ChainEventError α :=
    x.mapError .forkChoice
  -- The heads of the fork choice before and after the change.
  let oldHead ← lift (before.getHead config)
  let newHead ← lift (after.getHead config)
  let oldBlock ← lift (before.block oldHead.root)
  let mut events := []
  -- The source: a new head of the fork choice gives a head event.
  if headChanged oldHead newHead then
    let event ← headEvent after optimistic genesisRoot oldBlock.slot newHead
    events := events ++ [.head event]
    -- The source: the node has reorganized its chain.
    --
    -- EthLib reads it as an old head block that is not an ancestor of the new head.
    unless ← lift (after.isAncestor newHead ⟨oldHead.root, .pending⟩) do
      let newBlock ← lift (after.block newHead.root)
      -- The slot of the latest common ancestor of the two heads, walking up from the old head.
      --
      -- EthLib's bound: slot(old head) + 1 steps, enough to reach slot 0, as parents are earlier.
      let ancestor ← lift (commonAncestorSlot after ⟨newHead.root, .pending⟩
        (oldBlock.slot.toNat + 1) oldHead.root)
      -- The fields of the reorganization example, with depth = slot(old head) - slot(ancestor).
      --
      -- The source defines none of these fields.
      --
      -- The depth, and the slot and the epoch of the new head, are EthLib's reading.
      events := events ++ [.chainReorg {
        slot := newBlock.slot, depth := oldBlock.slot - ancestor,
        oldHeadBlock := oldHead.root, newHeadBlock := newHead.root,
        oldHeadState := oldBlock.stateRoot, newHeadState := newBlock.stateRoot,
        -- The epoch of the slot of the new head.
        epoch := computeEpochAtSlot preset newBlock.slot,
        executionOptimistic := optimistic newHead.root }]
  -- The source: an update of the finalized checkpoint gives a finalized checkpoint event.
  if before.finalizedCheckpoint ≠ after.finalizedCheckpoint then
    let checkpoint := after.finalizedCheckpoint
    let block ← lift (after.block checkpoint.root)
    -- The root of the checkpoint block, its state root, the epoch and the optimistic flag.
    events := events ++ [.finalizedCheckpoint {
      block := checkpoint.root, state := block.stateRoot, epoch := checkpoint.epoch,
      executionOptimistic := optimistic checkpoint.root }]
  return events

/-- The event of one run of the fast confirmation rule, from its store after the run. -/
def fastConfirmationEvent (store : Store preset fork) (fcr : FastConfirmationStore)
    (currentSlot : Slot) : Except ForkChoiceError FastConfirmationEvent := do
  -- The source: the root and the slot of the most recent confirmed block.
  --
  -- The source: the slot of the clock at which the rule ran.
  return ⟨fcr.confirmedRoot, (← store.block fcr.confirmedRoot).slot, currentSlot⟩

end EthLib.Consensus.BeaconApi
