module

public import EthLib.Consensus.DataAvailability.Column
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

A node also runs the attestations and the attester slashings of a block through their handlers.

The execution layer judges the payload of a block, and an argument stands for it.

At Bellatrix the first payload must follow a terminal block of proof of work, as EIP-3675 defines.

At Deneb and Electra the node must hold the blobs of a block, and they must match its commitments.

From Fulu the node must get the columns of data that it samples, and each must be valid.

From Gloas a block is not yet specified here.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Kzg

variable {preset : Preset} {fork : Fork}

/-- A block of the proof-of-work chain, with the total difficulty of its chain. -/
structure PowBlock where
  /-- The hash of the block. -/
  blockHash : Hash32
  /-- The hash of its parent. -/
  parentHash : Hash32
  /-- The total difficulty of the chain up to the block. -/
  totalDifficulty : U256
  deriving DecidableEq, Repr

instance : SszType PowBlock :=
  .container ["block_hash", "parent_hash", "total_difficulty"]
    (fun b => (b.blockHash, b.parentHash, b.totalDifficulty))
    (fun (blockHash, parentHash, totalDifficulty) => ⟨blockHash, parentHash, totalDifficulty⟩)

/-- What a node asks outside the beacon chain to judge a block. -/
structure BlockSources (preset : Preset) (fork : Fork) where
  /-- The execution layer, which judges the payload. -/
  engine : ExecutionEngine preset fork
  /-- The proof-of-work block of a hash, if the node knows it. -/
  powBlock : Hash32 → Option PowBlock
  /-- The blobs of the block with a root and their proofs, if the node holds them all. -/
  blobsAndProofs : Root → Option (Array Blob × Array KZGProof)
  /-- The columns that the node samples for the block with a root, if it can get them all. -/
  columns : Root → Option (Array (DataColumnSidecar preset fork))
  /-- The trusted setup of KZG, with which the node checks the blobs and the columns. -/
  setup : TrustedSetup

/-- Whether a proof-of-work block is terminal, by the definition of EIP-3675.

Its total difficulty reaches the terminal total difficulty, and that of its parent does not.

The source is [EIP-3675](https://eips.ethereum.org/EIPS/eip-3675#definitions). -/
def isValidTerminalPowBlock (config : Config) (block parent : PowBlock) : Bool :=
  decide (config.TERMINAL_TOTAL_DIFFICULTY ≤ block.totalDifficulty) &&
    decide (parent.totalDifficulty < config.TERMINAL_TOTAL_DIFFICULTY)

/-- Check that the first payload of the chain follows a terminal block of proof of work.

A configured terminal block hash replaces the test, from its activation epoch on.

Otherwise the parent of the payload and its own parent must be known, and the first terminal. -/
def validateMergeBlock (config : Config) (powBlock : Hash32 → Option PowBlock)
    (block : BeaconBlock preset fork) (bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam) :
    Except ForkChoiceError Unit := do
  let parentHash := (block.body.executionPayload bellatrix).parentHash
  if config.TERMINAL_BLOCK_HASH ≠ Vector.replicate 32 0 then
    let epoch := computeEpochAtSlot preset block.slot
    if epoch < config.TERMINAL_BLOCK_HASH_ACTIVATION_EPOCH then
      throw (.terminalBlockHashNotActive epoch)
    if parentHash ≠ config.TERMINAL_BLOCK_HASH then throw (.notTerminalBlockHash parentHash)
    return
  let some terminal := powBlock parentHash | throw (.unknownPowBlock parentHash)
  let some parent := powBlock terminal.parentHash | throw (.unknownPowBlock terminal.parentHash)
  unless isValidTerminalPowBlock config terminal parent do throw (.notTerminalPowBlock parentHash)

/-- From Deneb: whether the data of a block is available, as the node must check.

At Deneb and Electra the node must hold the blobs of the block and a proof for each.

Each proof must show that its blob matches the commitment at its position, as [EIP-4844] asks.

From Fulu the node must get every column that it samples, as [EIP-7594] asks.

Each column must have a valid shape, and the proofs of its cells must match its commitments.

[EIP-4844]: https://eips.ethereum.org/EIPS/eip-4844#consensus-layer-validation
[EIP-7594]: https://eips.ethereum.org/EIPS/eip-7594#specification -/
def isDataAvailable (config : Config) (sources : BlockSources preset fork)
    (block : BeaconBlock preset fork) (root : Root)
    (range : .dencun ≤ fork ∧ fork < .glamsterdam) : Except ForkChoiceError Bool := do
  if .fusaka ≤ fork then
    let some sidecars := sources.columns root | throw (.columnsUnavailable root)
    -- Before Gloas a column carries its commitments, so the bid of the block is never read.
    let noBid : Since .glamsterdam fork (BlobKZGCommitments preset fork) :=
      fun gloas => absurd gloas (not_glamsterdam_le range.2)
    sidecars.allM fun sidecar =>
      if verifyDataColumnSidecar preset config sidecar noBid then
        (verifyDataColumnSidecarKzgProofs sources.setup sidecar noBid).mapError .kzg
      else pure false
  else
    let some (blobs, proofs) := sources.blobsAndProofs root | throw (.blobsUnavailable root)
    (verifyBlobKzgProofBatch sources.setup blobs (block.body.blobKzgCommitments range).data
      proofs).mapError .kzg

/-- Check that the data of a block is available.

Before Deneb a block has no blobs, and the check passes.

From Gloas the data travels apart from the block, which is not yet specified here, so it fails. -/
def validateDataAvailability (config : Config) (sources : BlockSources preset fork)
    (block : BeaconBlock preset fork) (blockRoot : Root) : Except ForkChoiceError Unit := do
  if gloas : .glamsterdam ≤ fork then throw (.forkNotYetSpecified fork)
  else if deneb : .dencun ≤ fork then
    unless ← isDataAvailable config sources block blockRoot ⟨deneb, Nat.lt_of_not_le gloas⟩ do
      throw (if .fusaka ≤ fork then .invalidColumns blockRoot else .blobsNotMatching blockRoot)

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

An equivocator keeps no vote.

A vote replaces another only with a later epoch before Gloas, and a later slot from Gloas. -/
def recordVote (equivocating : List ValidatorIndex) (message : LatestMessage fork)
    (messages : Std.TreeMap ValidatorIndex (LatestMessage fork)) (index : ValidatorIndex) :
    Std.TreeMap ValidatorIndex (LatestMessage fork) :=
  if equivocating.contains index then messages
  else match messages[index]? with
    | some old => if old.rank < message.rank then messages.insert index message else messages
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

It counts only from the slot after its own.

From Gloas the check also reads the committee index and the payload.

That rule is not yet specified here.

So it fails from Gloas on, rather than apply the earlier rule. -/
def validateOnAttestation (attestation : Attestation preset fork) (isFromBlock : Bool) :
    Except ForkChoiceError Unit := do
  if .glamsterdam ≤ fork then throw (.forkNotYetSpecified fork)
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
def computeCheckpointState (checks : SignatureChecks) (target : Checkpoint) :
    Except ForkChoiceError (BeaconState preset fork) := do
  let base ← store.blockState target.root
  let start ← (computeStartSlotAtEpoch preset target.epoch).mapError .arith
  if base.slot < start then (processSlots config checks base start).mapError .transition
  else pure base

/-- The store with the state of a checkpoint, unless it holds one already. -/
def storeTargetCheckpointState (checks : SignatureChecks) (target : Checkpoint) :
    Except ForkChoiceError (Store preset fork) := do
  if store.checkpointStates.contains target then return store
  let state ← store.computeCheckpointState config checks target
  return { store with checkpointStates := store.checkpointStates.insert target state }

/-- The store with the vote of an attestation as the latest vote of its validators.

An equivocator keeps no vote.

A vote replaces another only with a later target epoch before Gloas, and a later slot from Gloas. -/
def updateLatestMessages (attestingIndices : List ValidatorIndex)
    (attestation : Attestation preset fork) : Store preset fork :=
  let message := LatestMessage.ofAttestation attestation
  let latestMessages :=
    attestingIndices.foldl (recordVote store.equivocatingIndices message) store.latestMessages
  { store with latestMessages }

/-- The store after an attestation, from the wire or from a block.

The attestation must be valid in the state of its target, with its signature. -/
def onAttestation (checks : SignatureChecks) (attestation : Attestation preset fork)
    (isFromBlock : Bool) : Except ForkChoiceError (Store preset fork) := do
  store.validateOnAttestation config attestation isFromBlock
  let store ← store.storeTargetCheckpointState config checks attestation.data.target
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

From Deneb its data must be available.

The state transition must accept the block, with its signatures and its state root.

At Bellatrix the block with the first payload of the chain must follow a terminal block. -/
def validateOnBlock (checks : SignatureChecks) (sources : BlockSources preset fork)
    (signed : SignedBeaconBlock preset fork) (blockRoot : Root) :
    Except ForkChoiceError (BeaconState preset fork) := do
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
  validateDataAvailability config sources block blockRoot
  let state ←
    (stateTransition config checks sources.engine preState signed true).mapError .transition
  if bellatrix : fork = .bellatrix then
    have range : .bellatrix ≤ fork ∧ fork < .glamsterdam := by subst bellatrix; decide
    if isMergeTransitionBlock preState block.body range then
      validateMergeBlock config sources.powBlock block range
  return state

/-- The store with a new block, the state after it, and the updates that the block brings.

Those are its timeliness, the boost and the checkpoints. -/
def addBlock (checks : SignatureChecks) (sources : BlockSources preset fork)
    (signed : SignedBeaconBlock preset fork) (blockRoot : Root) :
    Except ForkChoiceError (Store preset fork) := do
  let state ← store.validateOnBlock config checks sources signed blockRoot
  let head ← store.getHead config
  let store := { store with
    blocks := store.blocks.insert blockRoot signed.message
    blockStates := store.blockStates.insert blockRoot state }
  let store ← store.recordBlockTimeliness config blockRoot
  let store ← store.updateProposerBoostRoot config head.root blockRoot
  let store := store.updateCheckpoints state.currentJustifiedCheckpoint state.finalizedCheckpoint
  store.computePulledUpTip config blockRoot

/-- The store after a signed block: a known block changes nothing, and a new one is added.

From Gloas the rule changes, and it fails there as not yet specified. -/
def onBlock (checks : SignatureChecks) (sources : BlockSources preset fork)
    (signed : SignedBeaconBlock preset fork) : Except ForkChoiceError (Store preset fork) := do
  if .glamsterdam ≤ fork then throw (.forkNotYetSpecified fork)
  let blockRoot ← (SszType.hashTreeRoot signed.message).mapError .ssz
  if store.blocks.contains blockRoot then pure store
  else store.addBlock config checks sources signed blockRoot

/-- The store after a signed block and the votes that it carries.

The block comes first, then its attestations, then its attester slashings.

The attestations come from a block, so the clock does not bound their epoch. -/
def onBlockWithVotes (checks : SignatureChecks) (sources : BlockSources preset fork)
    (signed : SignedBeaconBlock preset fork) : Except ForkChoiceError (Store preset fork) := do
  let store ← store.onBlock config checks sources signed
  let store ← signed.message.body.attestations.data.foldlM
    (fun store attestation => store.onAttestation config checks attestation true) store
  signed.message.body.attesterSlashings.data.foldlM
    (fun store slashing => store.onAttesterSlashing config checks slashing) store

end Store

end EthLib.Consensus
