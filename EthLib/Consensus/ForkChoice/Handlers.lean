module

public import EthLib.Consensus.ForkChoice.Head
public import EthLib.Consensus.Transition.EpochJustification
public import EthLib.Consensus.Transition.StateTransition

/-!
# `Consensus.ForkChoice.Handlers`

The handlers of the fork choice: a tick of the clock, a block, an attestation and a slashing.

Each handler returns the new store, or an error that leaves the store as it was.

A tick moves the clock one slot at a time.

A new slot drops the proposer boost, and a new epoch realizes the checkpoints seen so far.

A block must extend the finalized block and pass the state transition.

It boosts its chain when it arrives on time, first in its slot, with the head's proposer shuffling.

Each block pulls its justification up to the end of its epoch, as if that epoch were processed.

An attestation updates the latest vote of each of its validators, if the vote is newer.

An attester slashing marks the validators in both of its attestations as equivocators.

So far a block runs at Phase 0 only.

From Altair the pull-up of the justification is not yet specified here, so a new block fails.

From Bellatrix a block also checks its payload, which is not yet specified here either.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- The number of slots between the start of the epoch of a slot and the slot. -/
def computeSlotsSinceEpochStart (preset : Preset) (slot : Slot) : Except ArithError Slot := do
  return slot - (← computeStartSlotAtEpoch preset (computeEpochAtSlot preset slot))

/-- The first slot whose state fixes the proposer shuffling of an epoch. -/
def computeShufflingLookaheadStartSlot (preset : Preset) (epoch : Epoch) : Except ArithError Slot :=
  computeStartSlotAtEpoch preset (saturatingSub epoch preset.MIN_SEED_LOOKAHEAD)

/-- The slot of the block whose root fixes the proposer shuffling of an epoch. -/
def computeShufflingDependentSlot (preset : Preset) (epoch : Epoch) : Except ArithError Slot := do
  return saturatingSub (← computeShufflingLookaheadStartSlot preset epoch) 1

/-- The latest votes after one more vote of a validator.

An equivocator keeps no vote, and a vote replaces another only with a later epoch. -/
def recordVote (equivocating : List ValidatorIndex) (message : LatestMessage)
    (messages : Std.TreeMap ValidatorIndex LatestMessage) (index : ValidatorIndex) :
    Std.TreeMap ValidatorIndex LatestMessage :=
  if equivocating.contains index then messages
  else match messages[index]? with
    | some old => if old.epoch < message.epoch then messages.insert index message else messages
    | none => messages.insert index message

namespace Store

variable (config : Config) (store : Store preset fork)

/-- The state after a known block, or an error when the store holds none. -/
def blockState (root : Root) : Except ForkChoiceError (BeaconState preset fork) :=
  match store.blockStates[root]? with
  | some state => return state
  | none => throw (.unknownBlockState root)

/-- The store with each checkpoint replaced when the new one has a greater epoch. -/
def updateCheckpoints (justified finalized : Checkpoint) : Store preset fork :=
  let store := if store.justifiedCheckpoint.epoch < justified.epoch then
    { store with justifiedCheckpoint := justified } else store
  if store.finalizedCheckpoint.epoch < finalized.epoch then
    { store with finalizedCheckpoint := finalized } else store

/-- The store with each unrealized checkpoint replaced when the new one has a greater epoch. -/
def updateUnrealizedCheckpoints (justified finalized : Checkpoint) : Store preset fork :=
  let store := if store.unrealizedJustifiedCheckpoint.epoch < justified.epoch then
    { store with unrealizedJustifiedCheckpoint := justified } else store
  if store.unrealizedFinalizedCheckpoint.epoch < finalized.epoch then
    { store with unrealizedFinalizedCheckpoint := finalized } else store

/-- The store with the checkpoints that a block would reach at the end of its epoch.

The state after the block runs the justification and finalization of an epoch.

A block of an earlier epoch also moves the checkpoints of the store. -/
def computePulledUpTip (blockRoot : Root) : Except ForkChoiceError (Store preset fork) := do
  let state ← store.blockState blockRoot
  let state ← (processJustificationAndFinalization state).mapError .transition
  let store := { store with
    unrealizedJustifications :=
      store.unrealizedJustifications.insert blockRoot state.currentJustifiedCheckpoint }
  let store :=
    store.updateUnrealizedCheckpoints state.currentJustifiedCheckpoint state.finalizedCheckpoint
  let blockEpoch := computeEpochAtSlot preset (← store.block blockRoot).slot
  if blockEpoch < (← store.getCurrentStoreEpoch config) then
    return store.updateCheckpoints state.currentJustifiedCheckpoint state.finalizedCheckpoint
  return store

/-- The store at a later time in the same or the next slot.

A new slot drops the proposer boost.

A new epoch makes the unrealized checkpoints the checkpoints of the store. -/
def onTickPerSlot (timeMs : UInt64) : Except ForkChoiceError (Store preset fork) := do
  let previousSlot ← store.getCurrentSlot config
  let store := { store with timeMs }
  let currentSlot ← store.getCurrentSlot config
  let store := if previousSlot < currentSlot then
    { store with proposerBoostRoot := Vector.replicate 32 0 } else store
  if previousSlot < currentSlot ∧
      (← (computeSlotsSinceEpochStart preset currentSlot).mapError .arith) = 0 then
    return store.updateCheckpoints store.unrealizedJustifiedCheckpoint
      store.unrealizedFinalizedCheckpoint
  return store

/-- How far the clock of the store is from a slot, which each step of a catch-up lowers. -/
def slotsBefore (slot : Slot) : Nat :=
  match store.getCurrentSlot config with
  | .ok current => slot.toNat - current.toNat
  | .error _ => 0

/-- The store ticked at the start of each slot up to a slot.

A tick that does not move the clock to a later slot is an error, so that the loop ends.

That cannot happen, since the start of a slot falls in that slot. -/
def catchUp (start : Store preset fork) (tickSlot : Slot) :
    Except ForkChoiceError (Store preset fork) := do
  let current ← start.getCurrentSlot config
  if current < tickSlot then
    let next ← (addChecked current 1).mapError .arith
    let nextTimeMs ← (computeTimeAtSlotMs config start.genesisTimeMs next).mapError .arith
    let ticked ← start.onTickPerSlot config nextTimeMs
    if _closer : ticked.slotsBefore config tickSlot < start.slotsBefore config tickSlot then
      catchUp ticked tickSlot
    else throw (.tickNotAdvancing current)
  else return start
termination_by start.slotsBefore config tickSlot

/-- The store at a time: each slot passed is ticked at its start, then the time is set. -/
def onTick (timeMs : UInt64) : Except ForkChoiceError (Store preset fork) := do
  let tickSlot ← (computeSlotAtTimeMs config store.genesisTimeMs timeMs).mapError .arith
  (← catchUp config store tickSlot).onTickPerSlot config timeMs

/-- Check that the target of an attestation is in the current epoch or the one before. -/
def validateTargetEpochAgainstCurrentTime (attestation : Attestation preset fork) :
    Except ForkChoiceError Unit := do
  let target := attestation.data.target
  let currentEpoch ← store.getCurrentStoreEpoch config
  let previousEpoch := saturatingSub currentEpoch 1
  unless target.epoch = currentEpoch ∨ target.epoch = previousEpoch do
    throw (.targetEpochNotRecent target.epoch)

/-- Check that an attestation can count in the fork choice now.

An attestation from a block skips the check of its epoch against the clock.

Its target must be the checkpoint block of the chain of its vote, in the epoch of its slot.

Both blocks must be known, and the vote must not be for a block after the attestation.

It counts only from the slot after its own. -/
def validateOnAttestation (attestation : Attestation preset fork) (isFromBlock : Bool) :
    Except ForkChoiceError Unit := do
  let target := attestation.data.target
  unless isFromBlock do store.validateTargetEpochAgainstCurrentTime config attestation
  if target.epoch ≠ computeEpochAtSlot preset attestation.data.slot then
    throw (.targetEpochMismatch target.epoch)
  discard <| store.block target.root
  let voted ← store.block attestation.data.beaconBlockRoot
  if attestation.data.slot < voted.slot then
    throw (.futureVote attestation.data.beaconBlockRoot)
  if target.root ≠ (← store.getCheckpointBlock attestation.data.beaconBlockRoot target.epoch) then
    throw (.targetNotCheckpointBlock target.root)
  let due ← (addChecked attestation.data.slot 1).mapError .arith
  if (← store.getCurrentSlot config) < due then throw (.attestationNotYetDue attestation.data.slot)

/-- The state of a checkpoint: the state of its block, advanced to the start of its epoch. -/
def computeCheckpointState (target : Checkpoint) :
    Except ForkChoiceError (BeaconState preset fork) := do
  let base ← store.blockState target.root
  let start ← (computeStartSlotAtEpoch preset target.epoch).mapError .arith
  if base.slot < start then (processSlots config base start).mapError .transition
  else pure base

/-- The store with the state of a checkpoint, unless it holds one already. -/
def storeTargetCheckpointState (target : Checkpoint) :
    Except ForkChoiceError (Store preset fork) := do
  if store.checkpointStates.contains target then return store
  let state ← store.computeCheckpointState config target
  return { store with checkpointStates := store.checkpointStates.insert target state }

/-- The store with the vote of an attestation as the latest vote of its validators.

An equivocator keeps no vote, and a vote replaces another only with a later target epoch. -/
def updateLatestMessages (attestingIndices : List ValidatorIndex)
    (attestation : Attestation preset fork) : Store preset fork :=
  let message : LatestMessage := ⟨attestation.data.target.epoch, attestation.data.beaconBlockRoot⟩
  let latestMessages :=
    attestingIndices.foldl (recordVote store.equivocatingIndices message) store.latestMessages
  { store with latestMessages }

/-- The store after an attestation, from the wire or from a block.

The attestation must be valid in the state of its target, with its signature. -/
def onAttestation (checks : SignatureChecks) (attestation : Attestation preset fork)
    (isFromBlock : Bool) : Except ForkChoiceError (Store preset fork) := do
  store.validateOnAttestation config attestation isFromBlock
  let store ← store.storeTargetCheckpointState config attestation.data.target
  let targetState ← store.checkpointState attestation.data.target
  let indexed ← (getIndexedAttestation targetState attestation).mapError .accessor
  unless ← (isValidIndexedAttestation config checks targetState indexed).mapError .transition do
    throw .invalidIndexedAttestation
  return store.updateLatestMessages indexed.attestingIndices.data.toList attestation

/-- Check an attester slashing: its two votes are slashable together.

Both attestations must be valid in the state of the justified block. -/
def validateOnAttesterSlashing (checks : SignatureChecks)
    (slashing : AttesterSlashing preset fork) :
    Except ForkChoiceError Unit := do
  unless isSlashableAttestationData slashing.attestation1.data slashing.attestation2.data do
    throw .notSlashable
  let state ← store.blockState store.justifiedCheckpoint.root
  unless ← (isValidIndexedAttestation config checks state slashing.attestation1).mapError
      .transition do
    throw .invalidIndexedAttestation
  unless ← (isValidIndexedAttestation config checks state slashing.attestation2).mapError
      .transition do
    throw .invalidIndexedAttestation

/-- The store with the validators in both attestations of a slashing among the equivocators. -/
def addEquivocators (slashing : AttesterSlashing preset fork) : Store preset fork :=
  let second := slashing.attestation2.attestingIndices.data.toList
  let indices := slashing.attestation1.attestingIndices.data.toList.filter (· ∈ second)
  let equivocatingIndices := indices.foldl (init := store.equivocatingIndices) fun known i =>
    if known.contains i then known else known ++ [i]
  { store with equivocatingIndices }

/-- The store after a valid attester slashing: the validators in both attestations equivocate. -/
def onAttesterSlashing (checks : SignatureChecks) (slashing : AttesterSlashing preset fork) :
    Except ForkChoiceError (Store preset fork) := do
  store.validateOnAttesterSlashing config checks slashing
  return store.addEquivocators slashing

/-- The store with whether a block arrived in its own slot, before the attestations are due. -/
def recordBlockTimeliness (root : Root) : Except ForkChoiceError (Store preset fork) := do
  let block ← store.block root
  let timeIntoSlotMs ← store.getTimeIntoSlotMs config
  let attestationThresholdMs ← (getAttestationDueMs config fork).mapError .arith
  let isTimely := (← store.getCurrentSlot config) = block.slot ∧
    timeIntoSlotMs < attestationThresholdMs
  return { store with blockTimeliness := store.blockTimeliness.insert root (decide isTimely) }

/-- The root that fixes the proposer shuffling of an epoch, in the chain of a block. -/
def getShufflingDependentRoot (root : Root) (epoch : Epoch) : Except ForkChoiceError Root := do
  let slot ← (computeShufflingDependentSlot preset epoch).mapError .arith
  return (← store.getAncestor ⟨root, .pending⟩ slot).root

/-- The store with a new block boosted when the boost applies.

The block must be timely and first in its slot, and agree with the head on the proposer shuffling.
-/
def updateProposerBoostRoot (head root : Root) : Except ForkChoiceError (Store preset fork) := do
  let isFirstBlock := store.proposerBoostRoot = Vector.replicate 32 0
  let isTimely ← match store.blockTimeliness[root]? with
    | some timely => pure timely
    | none => throw (.unknownBlockTimeliness root)
  let epoch ← store.getCurrentStoreEpoch config
  let headDependentRoot ← store.getShufflingDependentRoot head epoch
  let blockDependentRoot ← store.getShufflingDependentRoot root epoch
  if isTimely ∧ isFirstBlock ∧ headDependentRoot = blockDependentRoot then
    return { store with proposerBoostRoot := root }
  return store

/-- Check a new signed block, and return the state after it.

The parent must be known, and the block must not be from the future.

The block must be after the finalized slot, and its chain must hold the finalized block.

The state transition must accept the block, with its signatures and its state root. -/
def validateOnBlock (checks : SignatureChecks) (signed : SignedBeaconBlock preset fork)
    (blockRoot : Root) : Except ForkChoiceError (BeaconState preset fork) := do
  let block := signed.message
  let preState ← store.blockState block.parentRoot
  if (← store.getCurrentSlot config) < block.slot then throw (.futureBlock block.slot)
  let finalizedSlot ←
    (computeStartSlotAtEpoch preset store.finalizedCheckpoint.epoch).mapError .arith
  if block.slot ≤ finalizedSlot then throw (.blockNotAfterFinalized block.slot)
  let finalizedCheckpointBlock ←
    store.getCheckpointBlock block.parentRoot store.finalizedCheckpoint.epoch
  if store.finalizedCheckpoint.root ≠ finalizedCheckpointBlock then
    throw (.notDescendantOfFinalized blockRoot)
  (stateTransition config checks preState signed true).mapError .transition

/-- The store with a new block, the state after it, and the updates that the block brings.

Those are its timeliness, the boost and the checkpoints. -/
def addBlock (checks : SignatureChecks) (signed : SignedBeaconBlock preset fork)
    (blockRoot : Root) : Except ForkChoiceError (Store preset fork) := do
  let state ← store.validateOnBlock config checks signed blockRoot
  let head ← store.getHead config
  let store := { store with
    blocks := store.blocks.insert blockRoot signed.message
    blockStates := store.blockStates.insert blockRoot state }
  let store ← store.recordBlockTimeliness config blockRoot
  let store ← store.updateProposerBoostRoot config head.root blockRoot
  let store := store.updateCheckpoints state.currentJustifiedCheckpoint state.finalizedCheckpoint
  store.computePulledUpTip config blockRoot

/-- The store after a signed block: a known block changes nothing, and a new one is added.

From Altair the pull-up of the justification is not yet specified here, so a new block fails.

From Bellatrix the rule also checks the payload, and it fails there as not yet specified. -/
def onBlock (checks : SignatureChecks) (signed : SignedBeaconBlock preset fork) :
    Except ForkChoiceError (Store preset fork) := do
  if .bellatrix ≤ fork then throw (.forkNotYetSpecified fork)
  let blockRoot ← (SszType.hashTreeRoot signed.message).mapError .ssz
  if store.blocks.contains blockRoot then pure store
  else store.addBlock config checks signed blockRoot

end Store

end EthLib.Consensus
