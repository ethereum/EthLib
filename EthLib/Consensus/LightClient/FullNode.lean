module

public import EthLib.Consensus.Containers.Block
public import EthLib.Consensus.LightClient.Branch
public import EthLib.Consensus.LightClient.Upgrade

/-!
# `Consensus.LightClient.FullNode`

A full node derives the data of the light client from its blocks and their post states.

A header of the light client comes from a block alone.

From Capella, it also carries the header of the execution payload, with its branch to the body root.

From Gloas, it carries the parent execution block hash from the bid instead, with its branch.

A bootstrap comes from a block and its post state, which proves the current sync committee.

An update comes from a block, its parent and the post state of the parent.

The block carries the signature of the sync committee on its parent, the attested block.

The state of the attested block proves the next sync committee and the finalized checkpoint.

The finality update and the optimistic update keep parts of an update.

These rules hold from Altair, as the sync protocol does.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

open LightClientError (liftRoot specifiedFork)

variable {preset : Preset} {fork : Fork}

/-- The light client header of a block. -/
def blockToLightClientHeader (config : Config) (block : SignedBeaconBlock preset fork) :
    Except LightClientError (LightClientHeader preset fork) := do
  -- The fork is from Altair, the first with a light client.
  let _ ← specifiedFork fork
  let message := block.message
  -- Let `e` be the epoch of the slot of the block.
  let epoch := computeEpochAtSlot preset message.slot
  -- The beacon header of the block, with the root of its body.
  let beacon : BeaconBlockHeader := ⟨message.slot, message.proposerIndex, message.parentRoot,
    message.stateRoot, ← liftRoot (SszType.hashTreeRoot message.body)⟩
  if gloas : .glamsterdam ≤ fork then
    -- From Gloas, the parent block hash of the bid of the block.
    --
    -- Its branch proves it at `EXECUTION_BLOCK_HASH_GINDEX_GLOAS` of the body.
    let bid := (message.body.signedExecutionPayloadBid gloas).message
    let branch ← branchVector _
      (← liftRoot (computeMerkleProof message.body EXECUTION_BLOCK_HASH_GINDEX_GLOAS))
    return ⟨beacon, fun during => absurd gloas (Nat.not_le_of_lt during.2),
      fun _ => bid.parentBlockHash, fun _ => branch⟩
  else if before : ¬.shapella ≤ fork then
    -- Before Capella, the beacon header alone.
    return ⟨beacon, fun during => absurd during.1 before, fun later => absurd later gloas,
      fun later => absurd later before⟩
  else if epoch < config.CAPELLA_FORK_EPOCH then
    -- From Capella to Fulu, a block with `e < CAPELLA_FORK_EPOCH` gives the empty execution header.
    --
    -- Its branch is all zeros.
    return ⟨beacon, fun _ => ExecutionPayloadHeader.empty preset fork,
      fun later => absurd later gloas, fun _ => Vector.replicate _ zeroBytes32⟩
  else
    -- Otherwise the header of the execution payload of the block.
    let payload := message.body.executionPayload
      ⟨Nat.le_trans (by decide) (Classical.not_not.mp before), Nat.lt_of_not_le gloas⟩
    let header ← liftRoot payload.header
    -- A block with `e < DENEB_FORK_EPOCH` gives 0 blob gas used and 0 excess blob gas.
    --
    -- These two fields exist from Deneb only.
    let header := if epoch < config.DENEB_FORK_EPOCH then
      { header with blobGasUsed := fun _ => 0, excessBlobGas := fun _ => 0 }
    else header
    -- The branch proves the payload at `EXECUTION_PAYLOAD_GINDEX` of the body.
    let branch ← branchVector _
      (← liftRoot (computeMerkleProof message.body EXECUTION_PAYLOAD_GINDEX))
    return ⟨beacon, fun _ => header, fun later => absurd later gloas, fun _ => branch⟩

/-- The header of the block whose post state is given, with the root of that state. -/
def BeaconState.blockHeader (state : BeaconState preset fork) :
    Except LightClientError BeaconBlockHeader := do
  -- The latest block header, with the root of the state as its state root.
  return { state.latestBlockHeader with stateRoot := ← liftRoot (SszType.hashTreeRoot state) }

/-- The bootstrap of a block, from its post state. -/
def createLightClientBootstrap (config : Config) (state : BeaconState preset fork)
    (block : SignedBeaconBlock preset fork) :
    Except LightClientError (LightClientBootstrap preset fork) := do
  -- The fork is from Altair.
  let ⟨altair⟩ ← specifiedFork fork
  -- The epoch of the slot of the state is at least `ALTAIR_FORK_EPOCH`.
  ensure (computeEpochAtSlot preset state.slot ≥ config.ALTAIR_FORK_EPOCH)
    (.beforeAltair (computeEpochAtSlot preset state.slot) config.ALTAIR_FORK_EPOCH)
  -- The state is at the slot of its latest block header.
  ensure (state.slot = state.latestBlockHeader.slot)
    (.stateNotAtBlock state.slot state.latestBlockHeader.slot)
  -- That header, with the root of the state, has the root of the block.
  let stateBlockRoot ← liftRoot (SszType.hashTreeRoot (← state.blockHeader))
  let blockRoot ← liftRoot (SszType.hashTreeRoot block.message)
  ensure (stateBlockRoot = blockRoot) (.stateNotOfBlock stateBlockRoot blockRoot)
  -- The index of the current sync committee, at the fork of the slot of the state.
  let gindex ← currentSyncCommitteeGindexAtSlot (preset := preset) (fork := fork) config
    state.slot
  -- The header of the block, and the current sync committee of the state with its branch.
  return {
    header := ← blockToLightClientHeader config block
    currentSyncCommittee := (state.currentSyncCommittee altair).value
    currentSyncCommitteeBranch := ← branchVector _ (← liftRoot (computeMerkleProof state gindex)) }

/-- The update that a block gives, from the block, its parent and their post states.

The update is of the fork of the attested block, which the block may follow across a fork epoch.
-/
def createLightClientUpdate (config : Config) {signatureFork finalizedFork : Fork}
    (state : BeaconState preset signatureFork) (block : SignedBeaconBlock preset signatureFork)
    (attestedState : BeaconState preset fork) (attestedBlock : SignedBeaconBlock preset fork)
    (finalizedBlock : Option (SignedBeaconBlock preset finalizedFork))
    (finalizedEarlier : finalizedFork ≤ fork) :
    Except LightClientError (LightClientUpdate preset fork) := do
  -- The forks of the attested block and of the block are from Altair.
  let ⟨altair⟩ ← specifiedFork fork
  let ⟨signatureAltair⟩ ← specifiedFork signatureFork
  -- The epoch of the slot of the attested state is at least `ALTAIR_FORK_EPOCH`.
  ensure (computeEpochAtSlot preset attestedState.slot ≥ config.ALTAIR_FORK_EPOCH)
    (.beforeAltair (computeEpochAtSlot preset attestedState.slot) config.ALTAIR_FORK_EPOCH)
  -- The sync aggregate of the block has at least `MIN_SYNC_COMMITTEE_PARTICIPANTS` participants.
  let aggregate := block.message.body.syncAggregate signatureAltair
  ensure (aggregate.participants ≥ preset.MIN_SYNC_COMMITTEE_PARTICIPANTS.toNat)
    (.tooFewParticipants aggregate.participants preset.MIN_SYNC_COMMITTEE_PARTICIPANTS.toNat)
  -- The state is at the slot of its latest block header.
  ensure (state.slot = state.latestBlockHeader.slot)
    (.stateNotAtBlock state.slot state.latestBlockHeader.slot)
  -- That header, with the root of the state, has the root of the block.
  let stateBlockRoot ← liftRoot (SszType.hashTreeRoot (← state.blockHeader))
  let blockRoot ← liftRoot (SszType.hashTreeRoot block.message)
  ensure (stateBlockRoot = blockRoot) (.stateNotOfBlock stateBlockRoot blockRoot)
  -- Let `p(s)` be the sync committee period of the slot `s`.
  let period := computeSyncCommitteePeriodAtSlot preset
  -- The attested state is at the slot of its latest block header.
  ensure (attestedState.slot = attestedState.latestBlockHeader.slot)
    (.stateNotAtBlock attestedState.slot attestedState.latestBlockHeader.slot)
  -- That header, with the root of the attested state, has the root of the attested block.
  let attestedRoot ← liftRoot (SszType.hashTreeRoot (← attestedState.blockHeader))
  let attestedBlockRoot ← liftRoot (SszType.hashTreeRoot attestedBlock.message)
  ensure (attestedRoot = attestedBlockRoot) (.stateNotOfBlock attestedRoot attestedBlockRoot)
  -- That root is the parent root of the block.
  ensure (attestedRoot = block.message.parentRoot)
    (.stateNotOfBlock attestedRoot block.message.parentRoot)
  let empty := LightClientHeader.empty preset fork
  -- Let `a` be the slot of the attested block, and `b` the slot of the block.
  --
  -- For `p(a) = p(b)`, the next sync committee of the attested state, with its branch.
  --
  -- The next committee is of use only when the committee of the attested period signs.
  --
  -- Otherwise the empty committee and a branch of zeros.
  let (nextSyncCommittee, nextSyncCommitteeBranch) ←
    if period attestedBlock.message.slot = period block.message.slot then do
      -- The index of the next sync committee, at the fork of the slot of the state.
      let gindex ← nextSyncCommitteeGindexAtSlot (preset := preset) (fork := fork) config
        attestedState.slot
      pure ((attestedState.nextSyncCommittee altair).value,
        ← branchVector _ (← liftRoot (computeMerkleProof attestedState gindex)))
    else pure (SyncCommittee.empty preset, Vector.replicate _ zeroBytes32)
  -- Without the finalized block, the empty header and a branch of zeros.
  let (finalizedHeader, finalityBranch) ← match finalizedBlock with
    | none => pure (empty, Vector.replicate _ zeroBytes32)
    | some finalized => do
      -- Let `r` be the root of the finalized checkpoint of the attested state.
      let finalizedRoot := attestedState.finalizedCheckpoint.root
      -- A finalized block after the genesis slot gives its header.
      --
      -- The beacon header in it has the root `r`.
      let header ← if finalized.message.slot ≠ GENESIS_SLOT then do
          let header ← blockToLightClientHeader config finalized
          let headerRoot ← liftRoot (SszType.hashTreeRoot header.beacon)
          ensure (headerRoot = finalizedRoot) (.finalizedNotOfState finalizedRoot headerRoot)
          -- A block of an earlier fork has its header made at that fork, then upgraded.
          --
          -- The upgrade keeps the beacon header, so the root checked before it stays the same.
          header.upgrade config fork finalizedEarlier
        else do
          -- At the genesis slot, `r` must be 32 zero bytes, and the header stays empty.
          ensure (finalizedRoot = zeroBytes32) (.finalizedNotOfState finalizedRoot zeroBytes32)
          pure empty
      -- The branch proves `r` in the attested state, at the index of the fork of its slot.
      let gindex ← finalizedRootGindexAtSlot (preset := preset) (fork := fork) config
        attestedState.slot
      pure (header, ← branchVector _ (← liftRoot (computeMerkleProof attestedState gindex)))
  -- The header of the attested block, and the sync aggregate and the slot of the block.
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
