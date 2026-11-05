module

public import EthLib.Consensus.Containers.Block
public import EthLib.Consensus.LightClient.Sync
public import EthLib.Serialization.Ssz.Codec.Proof

/-!
# `Consensus.LightClient.FullNode`

A full node derives the data of the light client from its blocks and their post states.

A header of the light client comes from a block alone.

From Capella, it also carries the header of the execution payload, with its branch to the body root.

A bootstrap comes from a block and its post state, which proves the current sync committee.

An update comes from a block, its parent and the post state of the parent.

The block carries the signature of the sync committee on its parent, the attested block.

The state of the attested block proves the next sync committee and the finalized checkpoint.

The finality update and the optimistic update keep parts of an update.

These rules hold from Altair to Fulu, as the sync protocol does.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

open LightClientError (require liftRoot specifiedFork)

variable {preset : Preset} {fork : Fork}

/-- The branch that proves the node at a generalized index of a value, from the node up. -/
def computeMerkleProof {α : Type} [SszType α] (value : α) (gindex : Nat) :
    Except Err (List Bytes32) := do
  (← buildProof (SszType.desc α) (SszType.toValue value) gindex).mapM toChunk

/-- A branch as a vector of its length, or the error of a branch of another length. -/
def branchVector (depth : Nat) (branch : List Bytes32) : Except LightClientError
    (Vector Bytes32 depth) :=
  if h : branch.length = depth then .ok ⟨branch.toArray, by simpa using h⟩
  else .error (.ssz (.count depth branch.length))

/-- The light client header of a block.

From Capella, a block of a slot from Capella on also gives its execution payload header.

Its branch proves that header against the body root.

From Deneb, a block of a slot before Deneb gives zero blob gas in that header.

A block of a slot before Capella gives the empty header and a branch of zeros. -/
def blockToLightClientHeader (config : Config) (block : SignedBeaconBlock preset fork) :
    Except LightClientError (LightClientHeader preset fork) := do
  let ⟨range⟩ ← specifiedFork fork
  let message := block.message
  let epoch := computeEpochAtSlot preset message.slot
  let beacon : BeaconBlockHeader := ⟨message.slot, message.proposerIndex, message.parentRoot,
    message.stateRoot, ← liftRoot (SszType.hashTreeRoot message.body)⟩
  if before : ¬.shapella ≤ fork then
    return ⟨beacon, fun later => absurd later before, fun later => absurd later before⟩
  else if epoch < config.CAPELLA_FORK_EPOCH then
    return ⟨beacon, fun _ => ExecutionPayloadHeader.empty preset fork,
      fun _ => Vector.replicate _ zeroBytes32⟩
  else
    let payload := message.body.executionPayload
      ⟨Nat.le_trans (by decide) (Classical.not_not.mp before), range.2⟩
    let header ← liftRoot payload.header
    let header := if epoch < config.DENEB_FORK_EPOCH then
      { header with blobGasUsed := fun _ => 0, excessBlobGas := fun _ => 0 }
    else header
    let branch ← branchVector _
      (← liftRoot (computeMerkleProof message.body EXECUTION_PAYLOAD_GINDEX))
    return ⟨beacon, fun _ => header, fun _ => branch⟩

/-- The header of the block whose post state is given, with the root of that state. -/
def BeaconState.blockHeader (state : BeaconState preset fork) :
    Except LightClientError BeaconBlockHeader := do
  return { state.latestBlockHeader with stateRoot := ← liftRoot (SszType.hashTreeRoot state) }

/-- The bootstrap of a block, from its post state.

The state must be at the slot of the block, from Altair on, and must be the state of that block.

Its branch proves the current sync committee. -/
def createLightClientBootstrap (config : Config) (state : BeaconState preset fork)
    (block : SignedBeaconBlock preset fork) :
    Except LightClientError (LightClientBootstrap preset fork) := do
  let ⟨range⟩ ← specifiedFork fork
  require (computeEpochAtSlot preset state.slot ≥ config.ALTAIR_FORK_EPOCH) .beforeAltair
  require (state.slot = state.latestBlockHeader.slot) .stateNotAtBlock
  require ((← liftRoot (SszType.hashTreeRoot (← state.blockHeader))) =
    (← liftRoot (SszType.hashTreeRoot block.message))) .stateNotOfBlock
  let gindex ← currentSyncCommitteeGindexAtSlot (preset := preset) (fork := fork) config
    state.slot
  return {
    header := ← blockToLightClientHeader config block
    currentSyncCommittee := state.currentSyncCommittee range.1
    currentSyncCommitteeBranch := ← branchVector _ (← liftRoot (computeMerkleProof state gindex)) }

/-- The update that a block gives, from the block, its parent and their post states.

The block must carry the signature of at least the minimum of the sync committee.

Its parent is the attested block, and its post state proves what the update carries.

The next committee comes only when the committee of the attested period signs.

The finalized header comes when the finalized block is known, and is zero for the genesis. -/
def createLightClientUpdate (config : Config) (state : BeaconState preset fork)
    (block : SignedBeaconBlock preset fork) (attestedState : BeaconState preset fork)
    (attestedBlock : SignedBeaconBlock preset fork)
    (finalizedBlock : Option (SignedBeaconBlock preset fork)) :
    Except LightClientError (LightClientUpdate preset fork) := do
  let ⟨range⟩ ← specifiedFork fork
  require (computeEpochAtSlot preset attestedState.slot ≥ config.ALTAIR_FORK_EPOCH) .beforeAltair
  let aggregate := block.message.body.syncAggregate range.1
  require (aggregate.participants ≥ preset.MIN_SYNC_COMMITTEE_PARTICIPANTS.toNat)
    .tooFewParticipants
  require (state.slot = state.latestBlockHeader.slot) .stateNotAtBlock
  require ((← liftRoot (SszType.hashTreeRoot (← state.blockHeader))) =
    (← liftRoot (SszType.hashTreeRoot block.message))) .stateNotOfBlock
  let period := computeSyncCommitteePeriodAtSlot preset
  require (attestedState.slot = attestedState.latestBlockHeader.slot) .stateNotAtBlock
  let attestedRoot ← liftRoot (SszType.hashTreeRoot (← attestedState.blockHeader))
  require (attestedRoot = (← liftRoot (SszType.hashTreeRoot attestedBlock.message)) ∧
    attestedRoot = block.message.parentRoot) .stateNotOfBlock
  let empty := LightClientHeader.empty preset fork
  let (nextSyncCommittee, nextSyncCommitteeBranch) ←
    if period attestedBlock.message.slot = period block.message.slot then do
      let gindex ← nextSyncCommitteeGindexAtSlot (preset := preset) (fork := fork) config
        attestedState.slot
      pure (attestedState.nextSyncCommittee range.1,
        ← branchVector _ (← liftRoot (computeMerkleProof attestedState gindex)))
    else pure (SyncCommittee.empty preset, Vector.replicate _ zeroBytes32)
  let (finalizedHeader, finalityBranch) ← match finalizedBlock with
    | none => pure (empty, Vector.replicate _ zeroBytes32)
    | some finalized => do
      let finalizedRoot := attestedState.finalizedCheckpoint.root
      let header ← if finalized.message.slot ≠ GENESIS_SLOT then do
          let header ← blockToLightClientHeader config finalized
          require ((← liftRoot (SszType.hashTreeRoot header.beacon)) = finalizedRoot)
            .finalizedNotOfState
          pure header
        else do
          require (finalizedRoot = zeroBytes32) .finalizedNotOfState
          pure empty
      let gindex ← finalizedRootGindexAtSlot (preset := preset) (fork := fork) config
        attestedState.slot
      pure (header, ← branchVector _ (← liftRoot (computeMerkleProof attestedState gindex)))
  return {
    attestedHeader := ← blockToLightClientHeader config attestedBlock
    nextSyncCommittee
    nextSyncCommitteeBranch
    finalizedHeader
    finalityBranch
    syncAggregate := aggregate
    signatureSlot := block.message.slot }

/-- The finality update that an update gives: its headers, its finality branch and signature. -/
def createLightClientFinalityUpdate (update : LightClientUpdate preset fork) :
    LightClientFinalityUpdate preset fork where
  attestedHeader := update.attestedHeader
  finalizedHeader := update.finalizedHeader
  finalityBranch := update.finalityBranch
  syncAggregate := update.syncAggregate
  signatureSlot := update.signatureSlot

/-- The optimistic update that an update gives: its attested header and signature. -/
def createLightClientOptimisticUpdate (update : LightClientUpdate preset fork) :
    LightClientOptimisticUpdate preset fork where
  attestedHeader := update.attestedHeader
  syncAggregate := update.syncAggregate
  signatureSlot := update.signatureSlot

end EthLib.Consensus
