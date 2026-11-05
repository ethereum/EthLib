module

public import EthLib.Consensus.Accessors
public import EthLib.Consensus.Containers.State
public import EthLib.Consensus.Time
public import EthLib.Consensus.Transition.Basic
public import Std.Data.TreeMap

/-!
# `Consensus.ForkChoice.Store`

The store of the fork choice: what a node has seen of the chain, and the time.

The fork choice is LMD-GHOST from the justified checkpoint, as Gasper section 3 defines it.

The source is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).

The store starts from a trusted anchor: a block and the state after it.

It never rolls back before the anchor.

The store holds the blocks and the states of one fork.

A node of the fork choice is a block root with a payload status.

Before Gloas every node is pending, so a node and a block are the same thing.

An ancestor walk follows the parent of each block back to a slot.

A parent at a slot no lower than its child cannot happen in a store that the handlers build.

The walk fails there, so that it always ends.

Gloas changes the store and the walk, and those rules are not yet specified here.

So the store and the walk fail from Gloas on, rather than apply the earlier rule.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

/-- The status of the payload of a node: pending, then empty or full from Gloas. -/
inductive PayloadStatus where
  /-- The block is known without its payload. -/
  | empty
  /-- The block and its payload are known. -/
  | full
  /-- The node stands for the block, whatever its payload. -/
  | pending
  deriving DecidableEq, Repr, Inhabited

/-- The number of a payload status, which breaks a tie between two nodes of one block. -/
def PayloadStatus.code : PayloadStatus → UInt8
  | .empty => 0
  | .full => 1
  | .pending => 2

/-- A node of the fork choice: a block root and the status of its payload. -/
structure ForkChoiceNode where
  /-- The root of the block. -/
  root : Root
  /-- The status of the payload of the block. -/
  payloadStatus : PayloadStatus := .pending
  deriving DecidableEq, Repr, Inhabited

/-- The latest vote of a validator: its epoch and the root of the block it votes for. -/
structure LatestMessage where
  /-- The epoch of the vote. -/
  epoch : Epoch
  /-- The root of the block of the vote. -/
  root : Root
  deriving DecidableEq, Repr

/-- The order of checkpoints by epoch, then by root, which keys the checkpoint states. -/
def Checkpoint.compare (a b : Checkpoint) : Ordering :=
  (Ord.compare a.epoch b.epoch).then (Ord.compare a.root b.root)

/-- An error of the fork choice. -/
inductive ForkChoiceError where
  /-- The anchor block does not commit to the anchor state. -/
  | anchorStateMismatch
  /-- No block of the store has the root. -/
  | unknownBlock (root : Root)
  /-- The store holds no state for the checkpoint. -/
  | unknownCheckpointState (checkpoint : Checkpoint)
  /-- The store holds no state after the block with the root. -/
  | unknownBlockState (root : Root)
  /-- The store holds no unrealized justified checkpoint for the block with the root. -/
  | unknownUnrealizedJustification (root : Root)
  /-- A block of the store has a parent at a slot no lower than its own. -/
  | parentSlotNotLower (root : Root)
  /-- A time or a slot leaves the 64-bit range. -/
  | arith (error : ArithError)
  /-- A root cannot be computed. -/
  | ssz (error : Err)
  /-- A state accessor fails. -/
  | accessor (error : AccessorError)
  /-- The state transition rejects a block, or a state or an attestation cannot be checked. -/
  | transition (error : TransitionError)
  /-- The store holds no timeliness for the block with the root. -/
  | unknownBlockTimeliness (root : Root)
  /-- A block is from a slot after the current one. -/
  | futureBlock (slot : Slot)
  /-- A block is not after the first slot of the finalized epoch. -/
  | blockNotAfterFinalized (slot : Slot)
  /-- The chain of a block does not hold the finalized block. -/
  | notDescendantOfFinalized (root : Root)
  /-- The target of an attestation is neither in the current epoch nor in the previous one. -/
  | targetEpochNotRecent (epoch : Epoch)
  /-- The target epoch of an attestation is not the epoch of its slot. -/
  | targetEpochMismatch (epoch : Epoch)
  /-- An attestation votes for a block from a slot after its own. -/
  | futureVote (root : Root)
  /-- The target of an attestation is not the checkpoint block of the chain of its vote. -/
  | targetNotCheckpointBlock (root : Root)
  /-- An attestation is from the current slot or a later one. -/
  | attestationNotYetDue (slot : Slot)
  /-- An indexed attestation is not valid in the state of its target. -/
  | invalidIndexedAttestation
  /-- The two attestations of an attester slashing are not slashable together. -/
  | notSlashable
  /-- A tick does not move the clock to a later slot. -/
  | tickNotAdvancing (slot : Slot)
  /-- The rule of this fork is not yet specified here. -/
  | forkNotYetSpecified (fork : Fork)
  deriving Repr

variable (preset : Preset) (fork : Fork)

/-- The store of the fork choice at one fork. -/
structure Store where
  /-- The time, in milliseconds since the Unix epoch. -/
  timeMs : UInt64
  /-- The time of genesis, in milliseconds since the Unix epoch. -/
  genesisTimeMs : UInt64
  /-- The justified checkpoint, from which LMD-GHOST starts. -/
  justifiedCheckpoint : Checkpoint
  /-- The finalized checkpoint, with which every viable block agrees. -/
  finalizedCheckpoint : Checkpoint
  /-- The greatest justified checkpoint, counting votes that no epoch has processed yet. -/
  unrealizedJustifiedCheckpoint : Checkpoint
  /-- The greatest finalized checkpoint, counting votes that no epoch has processed yet. -/
  unrealizedFinalizedCheckpoint : Checkpoint
  /-- The root of the timely block of the current slot, or zero. -/
  proposerBoostRoot : Root
  /-- The validators known to have voted for two blocks at one target. -/
  equivocatingIndices : List ValidatorIndex
  /-- The known blocks, by root. -/
  blocks : Std.TreeMap Root (BeaconBlock preset fork)
  /-- The state after each known block, by root. -/
  blockStates : Std.TreeMap Root (BeaconState preset fork)
  /-- Whether each block arrived on time in its slot. -/
  blockTimeliness : Std.TreeMap Root Bool
  /-- The state at each checkpoint, with the checkpoint's epoch processed. -/
  checkpointStates : Std.TreeMap Checkpoint (BeaconState preset fork) Checkpoint.compare
  /-- The latest vote of each validator. -/
  latestMessages : Std.TreeMap ValidatorIndex LatestMessage
  /-- The unrealized justified checkpoint of each block. -/
  unrealizedJustifications : Std.TreeMap Root Checkpoint

variable {preset fork}

/-- The store that starts from an anchor block and the state after it.

The anchor is justified and finalized at the epoch of its state.

From Gloas the store is not yet specified here, so it fails. -/
def getForkchoiceStore (config : Config) (anchorState : BeaconState preset fork)
    (anchorBlock : BeaconBlock preset fork) : Except ForkChoiceError (Store preset fork) := do
  if .glamsterdam ≤ fork then throw (.forkNotYetSpecified fork)
  let stateRoot ← (SszType.hashTreeRoot anchorState).mapError .ssz
  if anchorBlock.stateRoot ≠ stateRoot then throw .anchorStateMismatch
  let anchorRoot ← (SszType.hashTreeRoot anchorBlock).mapError .ssz
  let anchorEpoch := getCurrentEpoch anchorState
  let checkpoint : Checkpoint := ⟨anchorEpoch, anchorRoot⟩
  let genesisTimeMs := secondsToMilliseconds anchorState.genesisTime
  let timeMs ← (computeTimeAtSlotMs config genesisTimeMs anchorState.slot).mapError .arith
  return {
    timeMs, genesisTimeMs
    justifiedCheckpoint := checkpoint
    finalizedCheckpoint := checkpoint
    unrealizedJustifiedCheckpoint := checkpoint
    unrealizedFinalizedCheckpoint := checkpoint
    proposerBoostRoot := Vector.replicate 32 0
    equivocatingIndices := []
    blocks := Std.TreeMap.empty.insert anchorRoot anchorBlock
    blockStates := Std.TreeMap.empty.insert anchorRoot anchorState
    blockTimeliness := ∅
    checkpointStates := Std.TreeMap.empty.insert checkpoint anchorState
    latestMessages := ∅
    unrealizedJustifications := Std.TreeMap.empty.insert anchorRoot checkpoint }

namespace Store

variable (config : Config) (store : Store preset fork)

/-- The current slot: the slot at the time of the store. -/
def getCurrentSlot : Except ForkChoiceError Slot :=
  (computeSlotAtTimeMs config store.genesisTimeMs store.timeMs).mapError .arith

/-- The epoch of the current slot. -/
def getCurrentStoreEpoch : Except ForkChoiceError Epoch :=
  return computeEpochAtSlot preset (← store.getCurrentSlot config)

/-- The time since the start of the current slot, in milliseconds. -/
def getTimeIntoSlotMs : Except ForkChoiceError UInt64 := do
  let start ← (computeTimeAtSlotMs config store.genesisTimeMs
    (← store.getCurrentSlot config)).mapError .arith
  return store.timeMs - start

/-- The block of a root, or an error when the store holds none. -/
def block (root : Root) : Except ForkChoiceError (BeaconBlock preset fork) :=
  match store.blocks[root]? with
  | some block => return block
  | none => throw (.unknownBlock root)

/-- The ancestor of a node at a slot: the node itself, or its latest ancestor at or below the slot.

Before Gloas the walk follows parent roots, and every node is pending.

From Gloas the walk is not yet specified here, so it fails. -/
def getAncestor (node : ForkChoiceNode) (slot : Slot) : Except ForkChoiceError ForkChoiceNode :=
  if .glamsterdam ≤ fork then throw (.forkNotYetSpecified fork) else
  match _found : store.blocks[node.root]? with
  | none => throw (.unknownBlock node.root)
  | some block =>
    if block.slot ≤ slot then pure node
    else
      match _parentFound : store.blocks[block.parentRoot]? with
      | none => throw (.unknownBlock block.parentRoot)
      | some parent =>
        if _lower : parent.slot < block.slot then
          getAncestor ⟨block.parentRoot, .pending⟩ slot
        else throw (.parentSlotNotLower node.root)
termination_by (store.blocks[node.root]?.map (·.slot.toNat)).getD 0
decreasing_by
  simp only [_found, _parentFound, Option.map_some, Option.getD_some]
  exact UInt64.lt_iff_toNat_lt.mp _lower

/-- Whether a node descends from another: its ancestor at the other's slot is that node. -/
def isAncestor (node ancestor : ForkChoiceNode) : Except ForkChoiceError Bool := do
  let ancestorBlock ← store.block ancestor.root
  return (← store.getAncestor node ancestorBlock.slot) == ancestor

/-- The checkpoint block of an epoch in the chain of a block: its ancestor at the epoch's start. -/
def getCheckpointBlock (root : Root) (epoch : Epoch) : Except ForkChoiceError Root := do
  let start ← (computeStartSlotAtEpoch preset epoch).mapError .arith
  return (← store.getAncestor ⟨root, .pending⟩ start).root

end Store

end EthLib.Consensus
