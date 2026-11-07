module

public import EthLib.Consensus.Containers.PowBlock
public import EthLib.Consensus.DataAvailability.Column
public import EthLib.Consensus.ForkChoice.Head
public import EthLib.Consensus.InclusionListCommittee
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

From Gloas an attestation also votes on the payload of its block, through its index.

From Gloas a member of the payload committee votes on whether a payload came on time.

It also votes on whether the blob data of the payload is available.

Its vote counts for the block of its slot, from the wire or from a later block.

From Gloas the payload of a block comes later, in an envelope, with the data of its blobs.

The node checks that data and the envelope against the state after the block, then keeps it.

A block that builds on the payload of its parent needs that payload kept first.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Kzg

variable {preset : Preset} {fork : Fork}

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
  /-- From Heze: whether the execution layer finds that a payload satisfies some transactions.

  The transactions are those of the timely inclusion lists of the slot before the payload's. -/
  inclusionListSatisfied : ExecutionPayload preset fork → List InclusionListTransaction → Bool

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

/-- From Fulu: whether the node gets every column that it samples for a block, each valid.

Each column must have a valid shape, and the proofs of its cells must match the commitments.

From Gloas the commitments are those of the bid of the block, and before they are in each column.
-/
def columnsAvailable (config : Config) (sources : BlockSources preset fork) (root : Root)
    (bidCommitments : Since .glamsterdam fork (BlobKZGCommitments preset fork)) :
    Except ForkChoiceError Bool := do
  let some sidecars := sources.columns root | throw (.columnsUnavailable root)
  sidecars.allM fun sidecar =>
    if verifyDataColumnSidecar preset config sidecar bidCommitments then
      (verifyDataColumnSidecarKzgProofs sources.setup sidecar bidCommitments).mapError .kzg
    else pure false

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
    -- Before Gloas a column carries its commitments, so the bid of the block is never read.
    columnsAvailable config sources root fun gloas => absurd gloas (not_glamsterdam_le range.2)
  else
    let some (blobs, proofs) := sources.blobsAndProofs root | throw (.blobsUnavailable root)
    (verifyBlobKzgProofBatch sources.setup blobs (block.body.blobKzgCommitments range).data
      proofs).mapError .kzg

/-- Check that the data of a block is available.

Before Deneb a block has no blobs, and the check passes.

From Gloas the data comes with the payload, so the check of the block passes. -/
def validateDataAvailability (config : Config) (sources : BlockSources preset fork)
    (block : BeaconBlock preset fork) (blockRoot : Root) : Except ForkChoiceError Unit := do
  if gloas : .glamsterdam ≤ fork then pure ()
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

/-- The positions of a validator in a payload committee, in committee order.

A validator may hold several positions, since the committee may draw it more than once. -/
def ptcPositions (committee : PayloadTimelinessCommittee preset)
    (validator : ValidatorIndex) : List (Fin preset.PTC_SIZE.toNat) :=
  (List.finRange _).filter (committee[·] = validator)

/-- The votes of a payload committee on one payload, with a value at the given positions. -/
def setPtcVotes {n : Nat} (votes : Vector (Option Bool) n) (positions : List (Fin n))
    (value : Bool) : Vector (Option Bool) n :=
  positions.foldl (fun votes position => votes.set position.val (some value) position.isLt) votes

/-- The state of a dependent block at the first slot of a lookahead.

A state at or after that slot is kept as it is. -/
def lookaheadState (config : Config) (checks : SignatureChecks) (state : BeaconState preset fork)
    (start : Slot) : Except ForkChoiceError (BeaconState preset fork) :=
  if state.slot < start then (processSlots config checks state start).mapError .transition
  else pure state

namespace Store

variable (config : Config) (store : Store preset fork)

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

/-- Check the vote of an attestation on the payload of its block, from Gloas.

The index of the attestation is that vote: 1 when the payload is present, else 0.

It must be 0 in the slot of the block, and 1 needs the payload verified in the store. -/
def validatePayloadVote (gloas : .glamsterdam ≤ fork) (attestation : Attestation preset fork)
    (voted : BeaconBlock preset fork) : Except ForkChoiceError Unit :=
  let index := attestation.data.index
  if index ≠ 0 ∧ index ≠ 1 then throw (.invalidAttestationIndex index)
  else if voted.slot = attestation.data.slot ∧ index ≠ 0 then
    throw (.sameSlotPayloadVote attestation.data.beaconBlockRoot)
  else if index = 1 ∧ !store.isPayloadVerified gloas attestation.data.beaconBlockRoot then
    throw (.payloadNotVerified attestation.data.beaconBlockRoot)
  else pure ()

/-- Check that an attestation can count in the fork choice now.

An attestation from a block skips the check of its epoch against the clock.

Its target must be the checkpoint block of the chain of its vote, in the epoch of its slot.

Both blocks must be known, and the vote must not be for a block after the attestation.

It counts only from the slot after its own.

From Gloas the index of an attestation says whether the payload of its block is present.

It must be 0 or 1, and 0 in the slot of the block.

A vote for the payload needs the payload, verified in the store. -/
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
  if gloas : .glamsterdam ≤ fork then store.validatePayloadVote gloas attestation voted
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

/-- Check a vote of the payload committee from the wire: it is for the current slot, and signed.

The signature is checked as an indexed vote with the validator as its only signer. -/
def validatePtcMessage (checks : SignatureChecks) (state : BeaconState preset fork)
    (message : PayloadAttestationMessage) (bound : 0 < preset.PTC_SIZE.toNat) :
    Except ForkChoiceError Unit := do
  if message.data.slot ≠ (← store.getCurrentSlot config) then
    throw (.ptcVoteNotCurrent message.data.slot)
  let indexed : IndexedPayloadAttestation preset :=
    ⟨⟨#[message.validatorIndex], by simpa using Nat.succ_le_of_lt bound⟩, message.data,
      message.signature⟩
  unless ← (isValidIndexedPayloadAttestation config checks state indexed).mapError .transition do
    throw .invalidPayloadAttestation

/-- The store with both votes of a payload vote at the given positions, for its block.

The store must hold votes for that block. -/
def recordPtcVotes (gloas : .glamsterdam ≤ fork) (data : PayloadAttestationData)
    (positions : List (Fin preset.PTC_SIZE.toNat)) :
    Except ForkChoiceError (Store preset fork) := do
  let timeliness ← ptcVotes (store.payloadTimelinessVote gloas) data.beaconBlockRoot
  let availability ← ptcVotes (store.payloadDataAvailabilityVote gloas) data.beaconBlockRoot
  -- The new maps are built here, once, so that a read of a field does not insert again.
  let timelinessVotes := (store.payloadTimelinessVote gloas).insert
    data.beaconBlockRoot (setPtcVotes timeliness positions data.payloadPresent)
  let availabilityVotes := (store.payloadDataAvailabilityVote gloas).insert
    data.beaconBlockRoot (setPtcVotes availability positions data.blobDataAvailable)
  return { store with
    payloadTimelinessVote := fun _ => timelinessVotes
    payloadDataAvailabilityVote := fun _ => availabilityVotes }

/-- The store after a vote of a member of the payload committee, from Gloas.

The store must hold the state after the block that the vote names.

A vote for another slot than that block's changes nothing.

The validator must be in the committee of that slot.

A vote from the wire must be for the current slot, with a valid signature.

A vote from a block skips both checks, since the block checked it.

The vote then sets both votes of the validator, at each of its positions. -/
def onPayloadAttestationMessage (checks : SignatureChecks) (gloas : .glamsterdam ≤ fork)
    (message : PayloadAttestationMessage) (isFromBlock : Bool) :
    Except ForkChoiceError (Store preset fork) := do
  let state ← store.blockState message.data.beaconBlockRoot
  if message.data.slot ≠ state.slot then pure store else
  let ptc ← (getPtc config state gloas message.data.slot).mapError .accessor
  let positions := ptcPositions ptc message.validatorIndex
  let first ← positions.head?.elim (throw (.notInPtc message.validatorIndex)) pure
  let () ← if isFromBlock then pure () else
    store.validatePtcMessage config checks state message first.pos
  store.recordPtcVotes gloas message.data positions

/-- The store after the votes of the payload committee that a block carries, from Gloas.

Each signer of each aggregate votes in turn, as a vote from a block.

The state is the one after the block, and nothing changes at slot 0. -/
def notifyPtcMessages (checks : SignatureChecks) (gloas : .glamsterdam ≤ fork)
    (state : BeaconState preset fork) (attestations : List (PayloadAttestation preset)) :
    Except ForkChoiceError (Store preset fork) := do
  if state.slot = 0 then return store
  attestations.foldlM (init := store) fun store attestation => do
    let indexed ← (getIndexedPayloadAttestation config state gloas attestation).mapError .accessor
    indexed.attestingIndices.data.toList.foldlM (init := store) fun store index =>
      store.onPayloadAttestationMessage config checks gloas
        ⟨index, attestation.data, Vector.replicate 96 0⟩ true

/-- The store with whether a block arrived in its own slot, before the attestations are due.

From Gloas it also records whether the block came before the votes of the payload committee. -/
def recordBlockTimeliness (root : Root) : Except ForkChoiceError (Store preset fork) := do
  let block ← store.block root
  let timeIntoSlotMs ← store.getTimeIntoSlotMs config
  let attestationThresholdMs ← (getAttestationDueMs config fork).mapError .arith
  let isCurrentSlot := (← store.getCurrentSlot config) = block.slot
  let isTimely := isCurrentSlot ∧ timeIntoSlotMs < attestationThresholdMs
  let store := { store with blockTimeliness := store.blockTimeliness.insert root (decide isTimely) }
  if gloas : .glamsterdam ≤ fork then
    let ptcThresholdMs ← (getPayloadAttestationDueMs config).mapError .arith
    let isPtcTimely := isCurrentSlot ∧ timeIntoSlotMs < ptcThresholdMs
    let ptcTimeliness := (store.ptcTimeliness gloas).insert root (decide isPtcTimely)
    return { store with ptcTimeliness := fun _ => ptcTimeliness }
  else return store

/-- The root that fixes the proposer shuffling of an epoch, in the chain of a block. -/
def getShufflingDependentRoot (root : Root) (epoch : Epoch) : Except ForkChoiceError Root := do
  let slot ← (computeShufflingDependentSlot preset epoch).mapError .arith
  return (← store.getAncestor ⟨root, .pending⟩ slot).root

/-- From Gloas: whether a block may be the last block at or before a slot, on some branch.

It may be when it is the head of the fork choice.

It may also be when a known block after the slot has it as parent.

Every other block gives false. -/
def isValidDependentRoot (root : Root) (dependentSlot : Slot) : Except ForkChoiceError Bool := do
  if root = (← store.getHead config).root then return true
  return store.blocks.toList.any fun (_, block) =>
    block.parentRoot = root ∧ dependentSlot < block.slot

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

/-- From Gloas: check that the payload of the parent of a block is kept when the block builds on it.

Before Gloas a block holds its own payload, and the check passes. -/
def validateParentPayload (block : BeaconBlock preset fork) : Except ForkChoiceError Unit :=
  if gloas : .glamsterdam ≤ fork then do
    let full ← store.isParentNodeFull block
    if full ∧ !store.isPayloadVerified gloas block.parentRoot then
      throw (.payloadNotVerified block.parentRoot)
  else pure ()

/-- Check a new signed block, and return the state after it.

The state after the parent must be known.

From Gloas, a block that builds on the payload of its parent needs that payload kept.

The block must not be from the future.

The block must be after the finalized slot, and its chain must hold the finalized block.

At Deneb, Electra and Fulu its data must be available.

The state transition must accept the block, with its signatures and its state root.

At Bellatrix the block with the first payload of the chain must follow a terminal block. -/
def validateOnBlock (checks : SignatureChecks) (sources : BlockSources preset fork)
    (signed : SignedBeaconBlock preset fork) (blockRoot : Root) :
    Except ForkChoiceError (BeaconState preset fork) := do
  let block := signed.message
  let preState ← store.blockState block.parentRoot
  store.validateParentPayload block
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

/-- From Gloas: the store with no vote yet of the payload committee on a new block.

The votes of the committee that the block carries then go through their handler.

They name the parent of the block, and the state after the block finds their members.

Before Gloas the store is unchanged. -/
def recordBlockPtcVotes (checks : SignatureChecks) (signed : SignedBeaconBlock preset fork)
    (blockRoot : Root) (state : BeaconState preset fork) :
    Except ForkChoiceError (Store preset fork) :=
  if gloas : .glamsterdam ≤ fork then
    let noVotes := Vector.replicate preset.PTC_SIZE.toNat none
    let timelinessVotes := (store.payloadTimelinessVote gloas).insert blockRoot noVotes
    let availabilityVotes := (store.payloadDataAvailabilityVote gloas).insert blockRoot noVotes
    let store := { store with
      payloadTimelinessVote := fun _ => timelinessVotes
      payloadDataAvailabilityVote := fun _ => availabilityVotes }
    store.notifyPtcMessages config checks gloas state
      (signed.message.body.payloadAttestations gloas).data.toList
  else pure store

/-- The store with a new block, the state after it, and the updates that the block brings.

From Gloas those start with the votes of the payload committee.

Then come its timeliness, the boost and the checkpoints. -/
def addBlock (checks : SignatureChecks) (sources : BlockSources preset fork)
    (signed : SignedBeaconBlock preset fork) (blockRoot : Root) :
    Except ForkChoiceError (Store preset fork) := do
  let state ← store.validateOnBlock config checks sources signed blockRoot
  let head ← store.getHead config
  let store := { store with
    blocks := store.blocks.insert blockRoot signed.message
    blockStates := store.blockStates.insert blockRoot state }
  let store ← store.recordBlockPtcVotes config checks signed blockRoot state
  let store ← store.recordBlockTimeliness config blockRoot
  let store ← store.updateProposerBoostRoot config head.root blockRoot
  let store := store.updateCheckpoints state.currentJustifiedCheckpoint state.finalizedCheckpoint
  store.computePulledUpTip config blockRoot

/-- The store after a signed block: a known block changes nothing, and a new one is added. -/
def onBlock (checks : SignatureChecks) (sources : BlockSources preset fork)
    (signed : SignedBeaconBlock preset fork) : Except ForkChoiceError (Store preset fork) := do
  let blockRoot ← (SszType.hashTreeRoot signed.message).mapError .ssz
  if store.blocks.contains blockRoot then pure store
  else store.addBlock config checks sources signed blockRoot

/-- The store after a signed block and the votes that it carries.

The block comes first, then its attestations, then its attester slashings.

The attestations come from a block, so the clock does not bound their epoch.

From Gloas the block itself passes on the votes of the payload committee that it carries. -/
def onBlockWithVotes (checks : SignatureChecks) (sources : BlockSources preset fork)
    (signed : SignedBeaconBlock preset fork) : Except ForkChoiceError (Store preset fork) := do
  let store ← store.onBlock config checks sources signed
  let store ← signed.message.body.attestations.data.foldlM
    (fun store attestation => store.onAttestation config checks attestation true) store
  signed.message.body.attesterSlashings.data.foldlM
    (fun store slashing => store.onAttesterSlashing config checks slashing) store

/-- From Gloas: check that the node gets the data of the payload of a block.

Each column that it samples must be valid against the commitments of the bid of the block. -/
def validatePayloadData (config : Config) (sources : BlockSources preset fork) (root : Root)
    (bid : ExecutionPayloadBid preset fork) :
    Except ForkChoiceError Unit := do
  unless ← columnsAvailable config sources root (fun _ => bid.blobKzgCommitments) do
    throw (.invalidColumns root)

/-- From Heze: the store with the answer on whether the payload of a block satisfied its lists.

The lists are the timely ones of the slot before the block, for the dependent root on its chain.

The execution layer gives the answer from their transactions.

A block at slot 0 has no slot before it, and that is an error. -/
def recordPayloadInclusionListSatisfaction (sources : BlockSources preset fork)
    (heze : .hegota ≤ fork) (root : Root) (payload : ExecutionPayload preset fork) :
    Except ForkChoiceError (Store preset fork) := do
  let slot ← (subChecked (← store.block root).slot 1).mapError .arith
  let dependentRoot ← store.getShufflingDependentRoot root (computeEpochAtSlot preset slot)
  let transactions := (store.inclusionLists heze).transactions slot dependentRoot true
  let satisfaction := (store.payloadInclusionListSatisfaction heze).insert root
    (sources.inclusionListSatisfied payload transactions)
  return { store with payloadInclusionListSatisfaction := fun _ => satisfaction }

/-- The store before it keeps an envelope: from Heze, with the answer on its inclusion lists. -/
def recordEnvelope (sources : BlockSources preset fork) (root : Root)
    (payload : ExecutionPayload preset fork) : Except ForkChoiceError (Store preset fork) :=
  if heze : .hegota ≤ fork then
    store.recordPayloadInclusionListSatisfaction sources heze root payload
  else pure store

/-- The store after a signed envelope, from Gloas: the payload of its block is then verified.

The store must hold the state after the block that the envelope names.

The node must get the data of the payload, against the bid that the state after the block holds.

The envelope must pass its checks against that state.

From Heze the store then records whether the payload satisfied the inclusion lists of its slot.

The store then keeps the envelope, by the root of its block. -/
def onExecutionPayloadEnvelope (checks : SignatureChecks) (sources : BlockSources preset fork)
    (gloas : .glamsterdam ≤ fork) (signed : SignedExecutionPayloadEnvelope preset fork) :
    Except ForkChoiceError (Store preset fork) := do
  let root := signed.message.beaconBlockRoot
  let state ← store.blockState root
  validatePayloadData config sources root (state.latestExecutionPayloadBid gloas)
  (verifyExecutionPayloadEnvelope config checks sources.engine state gloas signed).mapError
    .transition
  let recorded ← store.recordEnvelope sources root signed.message.payload
  let payloads := (recorded.payloads gloas).insert root signed.message
  return { recorded with payloads := fun _ => payloads }

/-- From Heze: the checks of an inclusion list, which give whether it is timely.

The list must be for the current slot or a slot of the window before it.

Its transactions must have bytes, each one, and at most the limit in all.

Its dependent block must be known with its state, at or before the dependent slot of its epoch.

That block must be the head, or have a known child after that slot.

Its sender must sit on the committee of its slot in the state of that block.

That state is advanced to the first slot of the lookahead, when it is earlier.

The sender must have signed the list with its key in that state.

The list is timely when it arrives in its slot, before the inclusion list deadline. -/
def checkInclusionList (checks : SignatureChecks) (signed : SignedInclusionList) :
    Except ForkChoiceError Bool := do
  let list := signed.message
  let currentSlot ← store.getCurrentSlot config
  ensure (list.slot ≤ currentSlot) (.futureInclusionList list.slot)
  let lastSlot ← (addChecked list.slot config.MIN_SLOTS_FOR_INCLUSION_LISTS_REQUESTS).mapError
    .arith
  ensure (currentSlot ≤ lastSlot) (.inclusionListTooOld list.slot)
  let transactions := list.transactions.data.toList
  let size := (transactions.map (·.data.size)).sum
  ensure (0 < size ∧ size ≤ config.MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST.toNat)
    (.invalidInclusionListSize size)
  ensure (transactions.all (0 < ·.data.size)) .emptyInclusionListTransaction
  let block ← store.block list.dependentRoot
  let dependentState ← store.blockState list.dependentRoot
  let epoch := computeEpochAtSlot preset list.slot
  let dependentSlot ← (computeShufflingDependentSlot preset epoch).mapError .arith
  ensure (block.slot ≤ dependentSlot) (.dependentBlockTooLate list.dependentRoot)
  let possible ← store.isValidDependentRoot config list.dependentRoot dependentSlot
  ensure possible (.notPossibleDependentBlock list.dependentRoot)
  let start ← (computeShufflingLookaheadStartSlot preset epoch).mapError .arith
  let state ← lookaheadState config checks dependentState start
  let committee ← (getInclusionListCommittee state list.slot).mapError .accessor
  ensure (list.validatorIndex ∈ committee.toList)
    (.notInInclusionListCommittee list.validatorIndex)
  let valid ← (isValidInclusionListSignature config state signed).mapError .accessor
  ensure valid .invalidInclusionListSignature
  -- The time into the slot is read only for a list of the current slot.
  if list.slot = currentSlot then
    let due ← (getInclusionListDueMs config).mapError .arith
    let timeIntoSlot ← store.getTimeIntoSlotMs config
    return decide (timeIntoSlot < due)
  else return false

/-- From Heze: the store after an inclusion list that passes every check.

The store keeps the list with its timeliness.

A list that fails a check is an error, and the store does not change. -/
def onInclusionList (checks : SignatureChecks) (heze : .hegota ≤ fork)
    (signed : SignedInclusionList) : Except ForkChoiceError (Store preset fork) := do
  let timely ← store.checkInclusionList config checks signed
  let lists := (store.inclusionLists heze).process signed timely
  return { store with inclusionLists := fun _ => lists }

end Store

end EthLib.Consensus
