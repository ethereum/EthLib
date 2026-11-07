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

From Gloas a node also says whether the payload of its block is known.

The walk gives each parent the status of its payload as its child builds on it.

From Gloas the store also holds the payloads it has verified and the votes of the payload committee.
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

/-- The latest vote of a validator: when it votes and the root of the block it votes for.

Before Gloas the vote has its target epoch.

From Gloas it has its slot instead, and whether it votes for the payload of the block. -/
structure LatestMessage (fork : Fork) where
  /-- The target epoch of the vote, before Gloas. -/
  epoch : Until .glamsterdam fork Epoch
  /-- The slot of the vote, from Gloas. -/
  slot : Since .glamsterdam fork Slot
  /-- The root of the block of the vote. -/
  root : Root
  /-- Whether the vote says that the payload of the block is present, from Gloas. -/
  payloadPresent : Since .glamsterdam fork Bool

/-- The epoch of a vote: its target epoch before Gloas, the epoch of its slot from Gloas. -/
def getLatestMessageEpoch (preset : Preset) {fork : Fork} (message : LatestMessage fork) : Epoch :=
  if gloas : .glamsterdam ≤ fork then computeEpochAtSlot preset (message.slot gloas)
  else message.epoch (Nat.lt_of_not_le gloas)

/-- The number that orders the votes of one validator: its epoch before Gloas, its slot from Gloas.

A vote replaces an earlier one of the validator only when this number grows. -/
def LatestMessage.rank {fork : Fork} (message : LatestMessage fork) : UInt64 :=
  if gloas : .glamsterdam ≤ fork then message.slot gloas
  else message.epoch (Nat.lt_of_not_le gloas)

/-- The vote of an attestation.

Before Gloas it has the target epoch.

From Gloas it has the slot, and it votes for the payload when the committee index is 1. -/
def LatestMessage.ofAttestation {preset : Preset} {fork : Fork}
    (attestation : Attestation preset fork) : LatestMessage fork where
  epoch := fun _ => attestation.data.target.epoch
  slot := fun _ => attestation.data.slot
  root := attestation.data.beaconBlockRoot
  payloadPresent := fun _ => attestation.data.index == 1

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
  /-- The proposer asks for its head while that head still holds the boost. -/
  | boostNotWornOff (root : Root)
  /-- A tick does not move the clock to a later slot. -/
  | tickNotAdvancing (slot : Slot)
  /-- The rule of this fork is not yet specified here. -/
  | forkNotYetSpecified (fork : Fork)
  /-- The node does not know the proof-of-work block of the hash. -/
  | unknownPowBlock (hash : Hash32)
  /-- The proof-of-work block of the hash is not terminal. -/
  | notTerminalPowBlock (hash : Hash32)
  /-- A block uses the configured terminal block hash before the epoch that activates it. -/
  | terminalBlockHashNotActive (epoch : Epoch)
  /-- The payload of a block does not follow the configured terminal block hash. -/
  | notTerminalBlockHash (hash : Hash32)
  /-- The node does not hold the blobs of the block with the root. -/
  | blobsUnavailable (root : Root)
  /-- A blob, a commitment or a proof is not a valid input of KZG. -/
  | kzg (error : Cryptography.Kzg.KzgError)
  /-- The proofs do not show that the blobs of the block with the root match its commitments. -/
  | blobsNotMatching (root : Root)
  /-- The node cannot get every column that it samples for the block with the root. -/
  | columnsUnavailable (root : Root)
  /-- A column of the block with the root has a wrong shape, or its proofs do not match. -/
  | invalidColumns (root : Root)
  /-- The store holds no votes of the payload committee for the block with the root. -/
  | unknownPayloadVotes (root : Root)
  /-- A choice between the full and the empty node is asked of the pending node of a block. -/
  | pendingNode (root : Root)
  /-- The block with the root is not from the slot before the current one. -/
  | notPreviousSlot (root : Root)
  deriving Repr

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

A new constructor takes a new code, so that each code keeps its meaning. -/
def ForkChoiceError.code : ForkChoiceError → UInt32
  | .anchorStateMismatch => 1
  | .unknownBlock _ => 2
  | .unknownCheckpointState _ => 3
  | .unknownBlockState _ => 4
  | .unknownUnrealizedJustification _ => 5
  | .parentSlotNotLower _ => 6
  | .arith _ => 7
  | .ssz _ => 8
  | .accessor _ => 9
  | .transition _ => 10
  | .unknownBlockTimeliness _ => 11
  | .futureBlock _ => 12
  | .blockNotAfterFinalized _ => 13
  | .notDescendantOfFinalized _ => 14
  | .targetEpochNotRecent _ => 15
  | .targetEpochMismatch _ => 16
  | .futureVote _ => 17
  | .targetNotCheckpointBlock _ => 18
  | .attestationNotYetDue _ => 19
  | .invalidIndexedAttestation => 20
  | .notSlashable => 21
  | .boostNotWornOff _ => 22
  | .tickNotAdvancing _ => 23
  | .forkNotYetSpecified _ => 24
  | .unknownPowBlock _ => 25
  | .notTerminalPowBlock _ => 26
  | .terminalBlockHashNotActive _ => 27
  | .notTerminalBlockHash _ => 28
  | .blobsUnavailable _ => 29
  | .kzg _ => 30
  | .blobsNotMatching _ => 31
  | .columnsUnavailable _ => 32
  | .invalidColumns _ => 33
  | .unknownPayloadVotes _ => 34
  | .pendingNode _ => 35
  | .notPreviousSlot _ => 36

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
  /-- Whether each block arrived in its slot before the attestation deadline. -/
  blockTimeliness : Std.TreeMap Root Bool
  /-- Whether each block arrived in its slot before the deadline of the payload committee. -/
  ptcTimeliness : Since .glamsterdam fork (Std.TreeMap Root Bool)
  /-- The state at each checkpoint, with the checkpoint's epoch processed. -/
  checkpointStates : Std.TreeMap Checkpoint (BeaconState preset fork) Checkpoint.compare
  /-- The latest vote of each validator. -/
  latestMessages : Std.TreeMap ValidatorIndex (LatestMessage fork)
  /-- The unrealized justified checkpoint of each block. -/
  unrealizedJustifications : Std.TreeMap Root Checkpoint
  /-- The verified payload of each block whose payload has arrived. -/
  payloads : Since .glamsterdam fork (Std.TreeMap Root (ExecutionPayloadEnvelope preset fork))
  /-- The vote of each member of the payload committee on whether the payload came on time. -/
  payloadTimelinessVote :
    Since .glamsterdam fork (Std.TreeMap Root (Vector (Option Bool) preset.PTC_SIZE.toNat))
  /-- The vote of each member of the payload committee on whether the blob data is available. -/
  payloadDataAvailabilityVote :
    Since .glamsterdam fork (Std.TreeMap Root (Vector (Option Bool) preset.PTC_SIZE.toNat))

variable {preset fork}

/-- The store that starts from an anchor block and the state after it.

The anchor is justified and finalized at the epoch of its state.

From Gloas the anchor is timely for both deadlines, and has no payload and no committee vote yet. -/
def getForkchoiceStore (config : Config) (anchorState : BeaconState preset fork)
    (anchorBlock : BeaconBlock preset fork) : Except ForkChoiceError (Store preset fork) := do
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
    blockTimeliness := if .glamsterdam ≤ fork then Std.TreeMap.empty.insert anchorRoot true else ∅
    ptcTimeliness := fun _ => Std.TreeMap.empty.insert anchorRoot true
    checkpointStates := Std.TreeMap.empty.insert checkpoint anchorState
    latestMessages := ∅
    unrealizedJustifications := Std.TreeMap.empty.insert anchorRoot checkpoint
    payloads := fun _ => ∅
    payloadTimelinessVote := fun _ =>
      Std.TreeMap.empty.insert anchorRoot (Vector.replicate _ none)
    payloadDataAvailabilityVote := fun _ =>
      Std.TreeMap.empty.insert anchorRoot (Vector.replicate _ none) }

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

/-- Whether the store holds the verified payload of the block with a root, from Gloas. -/
def isPayloadVerified (gloas : .glamsterdam ≤ fork) (root : Root) : Bool :=
  (store.payloads gloas).contains root

/-- The status of the payload of a parent, as a child block builds on it.

Before Gloas a block has no separate payload, so the parent is pending.

From Gloas the parent is full when the child's bid builds on the block hash of the parent's bid.

Otherwise the child builds on the parent without its payload, so the parent is empty. -/
def parentPayloadStatus (block parent : BeaconBlock preset fork) : PayloadStatus :=
  if gloas : .glamsterdam ≤ fork then
    if (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash =
        (parent.body.signedExecutionPayloadBid gloas).message.blockHash then .full
    else .empty
  else .pending

/-- The status of the payload of the parent of a block, which the store must hold. -/
def getParentPayloadStatus (block : BeaconBlock preset fork) :
    Except ForkChoiceError PayloadStatus :=
  return parentPayloadStatus block (← store.block block.parentRoot)

/-- Whether a block builds on the full parent: its parent with its payload. -/
def isParentNodeFull (block : BeaconBlock preset fork) : Except ForkChoiceError Bool :=
  return (← store.getParentPayloadStatus block) == .full

/-- The ancestor of a node at a slot: the node itself, or its latest ancestor at or below the slot.

The walk follows parent roots.

Each parent node gets the status of its payload as its child builds on it.

Before Gloas that status is pending, so every node of the walk is pending. -/
def getAncestor (node : ForkChoiceNode) (slot : Slot) : Except ForkChoiceError ForkChoiceNode :=
  match _found : store.blocks[node.root]? with
  | none => throw (.unknownBlock node.root)
  | some block =>
    if block.slot ≤ slot then pure node
    else
      match _parentFound : store.blocks[block.parentRoot]? with
      | none => throw (.unknownBlock block.parentRoot)
      | some parent =>
        if _lower : parent.slot < block.slot then
          getAncestor ⟨block.parentRoot, parentPayloadStatus block parent⟩ slot
        else throw (.parentSlotNotLower node.root)
termination_by (store.blocks[node.root]?.map (·.slot.toNat)).getD 0
decreasing_by
  simp only [_found, _parentFound, Option.map_some, Option.getD_some]
  exact UInt64.lt_iff_toNat_lt.mp _lower

/-- Whether a node descends from another: its ancestor at the other's slot is that node.

From Gloas the ancestor has the same root, and the same payload status or a pending one.

A pending ancestor stands for its block, so both of its payload statuses descend from it. -/
def isAncestor (node ancestor : ForkChoiceNode) : Except ForkChoiceError Bool := do
  let ancestorBlock ← store.block ancestor.root
  let found ← store.getAncestor node ancestorBlock.slot
  if .glamsterdam ≤ fork then
    return found.root == ancestor.root &&
      (found.payloadStatus == ancestor.payloadStatus || ancestor.payloadStatus == .pending)
  else return found == ancestor

/-- The checkpoint block of an epoch in the chain of a block: its ancestor at the epoch's start. -/
def getCheckpointBlock (root : Root) (epoch : Epoch) : Except ForkChoiceError Root := do
  let start ← (computeStartSlotAtEpoch preset epoch).mapError .arith
  return (← store.getAncestor ⟨root, .pending⟩ start).root

end Store

end EthLib.Consensus
