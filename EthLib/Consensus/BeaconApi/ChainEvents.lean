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

[event stream]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/eventstream/index.yaml
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
  | .head _ => .headV2
  | .finalizedCheckpoint _ => .finalizedCheckpoint
  | .chainReorg _ => .chainReorg
  | .fastConfirmation _ => .fastConfirmation

/-- A root as the API writes it. -/
def rootJson (root : Root) : Json := .str (toHex root.toArray)

/-- The data of an event, as JSON.

The head event names the consensus version of the fork beside its data. -/
def data (fork : Fork) : ChainEvent → Json
  | .head e =>
    let fields := Json.mkObj [("slot", uintJson e.slot), ("block", rootJson e.block),
      ("state", rootJson e.state), ("payload_status", .str (payloadStatusName e.payloadStatus)),
      ("epoch_transition", .bool e.epochTransition),
      ("current_epoch_dependent_root", rootJson e.currentEpochDependentRoot),
      ("next_epoch_dependent_root", rootJson e.nextEpochDependentRoot),
      ("execution_optimistic", .bool e.executionOptimistic)]
    { version := fork.consensusVersion?, data := fields : ApiEnvelope }.toJson
  | .finalizedCheckpoint e =>
    .mkObj [("block", rootJson e.block), ("state", rootJson e.state), ("epoch", uintJson e.epoch),
      ("execution_optimistic", .bool e.executionOptimistic)]
  | .chainReorg e =>
    .mkObj [("slot", uintJson e.slot), ("depth", uintJson e.depth),
      ("old_head_block", rootJson e.oldHeadBlock), ("new_head_block", rootJson e.newHeadBlock),
      ("old_head_state", rootJson e.oldHeadState), ("new_head_state", rootJson e.newHeadState),
      ("epoch", uintJson e.epoch), ("execution_optimistic", .bool e.executionOptimistic)]
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

The walk follows parents for at most some steps, then stops at the block it reached.

It fails when the store does not hold a block of the walk. -/
def commonAncestorSlot (store : Store preset fork) (node : ForkChoiceNode) :
    Nat → Root → Except ForkChoiceError Slot
  | 0, root => return (← store.block root).slot
  | steps + 1, root => do
    let block ← store.block root
    if ← store.isAncestor node ⟨root, .pending⟩ then return block.slot
    else commonAncestorSlot store node steps block.parentRoot

/-- The head event of a head of a store.

The slot of the head before it decides whether the epoch changed.

The two dependent roots are those of attester duties for the epoch of the head and the next one.

The genesis root stands in for a slot before the first. -/
def headEvent (store : Store preset fork) (optimistic : Root → Bool) (genesisRoot : Root)
    (previousSlot : Slot) (head : ForkChoiceNode) : Except ChainEventError HeadEvent := do
  let block ← (store.block head.root).mapError .forkChoice
  let state ← (store.blockState head.root).mapError .forkChoice
  let epoch := computeEpochAtSlot preset block.slot
  let current ← (dependentRoot state 1 epoch genesisRoot).mapError .dependentRoot
  let next ← (dependentRoot state 0 epoch genesisRoot).mapError .dependentRoot
  return { slot := block.slot, block := head.root, state := block.stateRoot,
           payloadStatus := apiPayloadStatus fork head.payloadStatus,
           epochTransition := computeEpochAtSlot preset previousSlot != epoch,
           currentEpochDependentRoot := current, nextEpochDependentRoot := next,
           executionOptimistic := optimistic head.root }

/-- Whether a head event follows a change of the head.

The head block changes, or it stays and its payload status moves from empty to full. -/
def headChanged (before after : ForkChoiceNode) : Bool :=
  before.root != after.root ||
    (before.payloadStatus == .empty && after.payloadStatus == .full)

/-- The events of the fork choice that a change of its store gives, in order.

A head event comes when the head changes, a finalized event when the checkpoint changes.

A reorganization comes when the old head block is not an ancestor of the new head.

The optimistic flag of a block tells whether its payload is not yet verified. -/
def chainEvents (config : Config) (optimistic : Root → Bool) (genesisRoot : Root)
    (before after : Store preset fork) : Except ChainEventError (List ChainEvent) := do
  let lift {α : Type} (x : Except ForkChoiceError α) : Except ChainEventError α :=
    x.mapError .forkChoice
  let oldHead ← lift (before.getHead config)
  let newHead ← lift (after.getHead config)
  let oldBlock ← lift (before.block oldHead.root)
  let mut events := []
  if headChanged oldHead newHead then
    let event ← headEvent after optimistic genesisRoot oldBlock.slot newHead
    events := events ++ [.head event]
    unless ← lift (after.isAncestor newHead ⟨oldHead.root, .pending⟩) do
      let newBlock ← lift (after.block newHead.root)
      let ancestor ← lift (commonAncestorSlot after ⟨newHead.root, .pending⟩
        (oldBlock.slot.toNat + 1) oldHead.root)
      events := events ++ [.chainReorg {
        slot := newBlock.slot, depth := oldBlock.slot - ancestor,
        oldHeadBlock := oldHead.root, newHeadBlock := newHead.root,
        oldHeadState := oldBlock.stateRoot, newHeadState := newBlock.stateRoot,
        epoch := computeEpochAtSlot preset newBlock.slot,
        executionOptimistic := optimistic newHead.root }]
  if before.finalizedCheckpoint ≠ after.finalizedCheckpoint then
    let checkpoint := after.finalizedCheckpoint
    let block ← lift (after.block checkpoint.root)
    events := events ++ [.finalizedCheckpoint {
      block := checkpoint.root, state := block.stateRoot, epoch := checkpoint.epoch,
      executionOptimistic := optimistic checkpoint.root }]
  return events

/-- The event of one run of the fast confirmation rule, from its store after the run.

It names the confirmed block and its slot, and the slot of the clock. -/
def fastConfirmationEvent (store : Store preset fork) (fcr : FastConfirmationStore)
    (currentSlot : Slot) : Except ForkChoiceError FastConfirmationEvent := do
  return ⟨fcr.confirmedRoot, (← store.block fcr.confirmedRoot).slot, currentSlot⟩

end EthLib.Consensus.BeaconApi
