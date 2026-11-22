module

public import EthLib.Base.Except
public import EthLib.Base.Hex
public import EthLib.Consensus.ForkSchedule
public import EthLib.Consensus.LightClient.Containers
public import EthLib.Consensus.Signing
public import EthLib.Consensus.Time
public import EthLib.Consensus.Transition.Basic
public import EthLib.Serialization.Ssz.Merkle.Branch

/-!
# `Consensus.LightClient.Sync`

From Altair, a light client keeps a store, which it starts from a bootstrap and moves by updates.

The bootstrap names a header that the client trusts, and proves the sync committee of its period.

An update carries a header signed by the sync committee, and what the state of that header proves.

It may prove the next sync committee, and it may prove a finalized header.

The client checks the update against the committees that it knows, then applies it.

A header becomes finalized once at least two thirds of the committee sign an update that proves it.

When no such update comes for a whole period, the client may force the best update it has seen.

The rules depend on the fork of the store, and on the fork of each header's slot.

The configuration gives the fork of a slot.

From Gloas, a header proves the parent execution block hash instead of an execution header.

A header of Gloas form can stand for a block of an earlier slot.

Its branch then climbs from the block hash through the execution header of that block.

Before Altair there is no light client, so every check of a store, a header or an update fails.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

/-- Why a light client refuses a bootstrap or an update. -/
inductive LightClientError where
  /-- A root could not be computed. -/
  | ssz (error : Err)
  /-- A header fails the checks of the fork of its slot, which the error gives. -/
  | invalidHeader (slot : Slot)
  /-- The header of a bootstrap is not the block that the client trusts.

  The error gives the root of the trusted block, then the root of the header. -/
  | untrustedHeader (trusted header : Root)
  /-- The branch of the current sync committee does not reach the state root.

  The error gives the generalized index of the committee and the state root. -/
  | invalidCurrentSyncCommitteeBranch (gindex : Nat) (stateRoot : Root)
  /-- Fewer members than the minimum signed the update.

  The error gives the number of signers and the minimum. -/
  | tooFewParticipants (count minimum : Nat)
  /-- The slots of the update are not ordered: now, signature, attested header, finalized header.

  The error gives the four slots in that order. -/
  | slotsOutOfOrder (currentSlot signatureSlot attestedSlot finalizedSlot : Slot)
  /-- The update is signed in a period whose committee the store does not know.

  The error gives the period of the signature and the period of the store.

  It also says whether the store knows the next committee. -/
  | unknownSignaturePeriod (signaturePeriod storePeriod : UInt64) (nextKnown : Bool)
  /-- The update brings neither a newer header nor the next sync committee.

  The error gives the slot of the attested header and the finalized slot of the store. -/
  | irrelevantUpdate (attestedSlot storeFinalizedSlot : Slot)
  /-- An update that must carry the zero finalized header carries another one.

  The error gives the slot of that header. -/
  | unexpectedFinalizedHeader (slot : Slot)
  /-- The finality branch does not reach the state root of the attested header.

  The error gives the generalized index of the finalized root and the state root. -/
  | invalidFinalityBranch (gindex : Nat) (stateRoot : Root)
  /-- An update without a committee branch carries a next sync committee.

  The error gives the aggregate key of that committee. -/
  | unexpectedNextSyncCommittee (aggregatePubkey : BLSPubkey)
  /-- The next sync committee of the update differs from the one that the store knows.

  The error gives the aggregate key of the store's committee, then that of the update's. -/
  | conflictingNextSyncCommittee (storeAggregatePubkey updateAggregatePubkey : BLSPubkey)
  /-- The branch of the next sync committee does not reach the state root of the attested header.

  The error gives the generalized index of the committee and the state root. -/
  | invalidNextSyncCommitteeBranch (gindex : Nat) (stateRoot : Root)
  /-- The sync committee signature does not verify against the root that the error gives. -/
  | invalidSignature (signingRoot : Root)
  /-- The finalized header of an update lies outside the period of the store.

  The error gives the period of that header and the period of the store. -/
  | finalizedPeriodMismatch (finalizedPeriod storePeriod : UInt64)
  /-- The slot after which an update is forced leaves the 64-bit range.

  The error gives the finalized slot of the store and the timeout added to it. -/
  | slotOverflow (finalizedSlot timeout : Slot)
  /-- The fork has no light client: it comes before Altair. -/
  | forkNotSpecified (fork : Fork)
  /-- A full node derives data from a state before Altair.

  The error gives the epoch of the state and the epoch of Altair. -/
  | beforeAltair (epoch altairEpoch : Epoch)
  /-- A full node derives data from a state that is not at the slot of its latest block.

  The error gives the slot of the state and the slot of its latest block header. -/
  | stateNotAtBlock (stateSlot blockSlot : Slot)
  /-- A full node derives data from a state that is not the post state of the block.

  The error gives the root of the block that the state holds, then the root it must equal.

  That root is the root of the block, or the parent root of the block that signs an update. -/
  | stateNotOfBlock (stateBlockRoot blockRoot : Root)
  /-- The finalized block that a full node gives is not the finalized block of the state.

  The error gives the finalized root of the state, then the root of the given block.

  For a block at the genesis slot the second root is zero. -/
  | finalizedNotOfState (stateFinalizedRoot blockRoot : Root)
  deriving DecidableEq, Repr

namespace LightClientError

/-- The code of an error: one per constructor, from 1. -/
def code : LightClientError → UInt32
  | .ssz _ => 1
  | .invalidHeader _ => 2
  | .untrustedHeader .. => 3
  | .invalidCurrentSyncCommitteeBranch .. => 4
  | .tooFewParticipants .. => 5
  | .slotsOutOfOrder .. => 6
  | .unknownSignaturePeriod .. => 7
  | .irrelevantUpdate .. => 8
  | .unexpectedFinalizedHeader _ => 9
  | .invalidFinalityBranch .. => 10
  | .unexpectedNextSyncCommittee _ => 11
  | .conflictingNextSyncCommittee .. => 12
  | .invalidNextSyncCommitteeBranch .. => 13
  | .invalidSignature _ => 14
  | .finalizedPeriodMismatch .. => 15
  | .slotOverflow .. => 16
  | .forkNotSpecified _ => 17
  | .beforeAltair .. => 18
  | .stateNotAtBlock .. => 19
  | .stateNotOfBlock .. => 20
  | .finalizedNotOfState .. => 21

/-- The message of an error, with the values that its check compared. -/
instance : ToString LightClientError where
  toString
    | .ssz error => s!"a root cannot be computed: {reprStr error}"
    | .invalidHeader slot => s!"the header at slot {slot} is not valid for the fork of its slot"
    | .untrustedHeader trusted header =>
      s!"expected trusted block root {hexString trusted.toList}, " ++
        s!"got header root {hexString header.toList}"
    | .invalidCurrentSyncCommitteeBranch gindex stateRoot =>
      s!"the current sync committee branch at generalized index {gindex} " ++
        s!"does not reach state root {hexString stateRoot.toList}"
    | .tooFewParticipants count minimum =>
      s!"{count} sync committee participants, expected at least {minimum}"
    | .slotsOutOfOrder current signature attested finalized =>
      s!"expected current slot {current} >= signature slot {signature} > " ++
        s!"attested slot {attested} >= finalized slot {finalized}"
    | .unknownSignaturePeriod signature store nextKnown =>
      s!"signature period {signature} has no known committee: store period {store}, " ++
        s!"next committee known: {nextKnown}"
    | .irrelevantUpdate attested storeFinalized =>
      s!"attested slot {attested} is not after the store's finalized slot {storeFinalized}, " ++
        "and the update brings no next sync committee that the store lacks"
    | .unexpectedFinalizedHeader slot =>
      s!"expected the zero finalized header, got a header at slot {slot}"
    | .invalidFinalityBranch gindex stateRoot =>
      s!"the finality branch at generalized index {gindex} " ++
        s!"does not reach state root {hexString stateRoot.toList}"
    | .unexpectedNextSyncCommittee key =>
      s!"expected the zero next sync committee, got another with aggregate key " ++
        hexString key.toList
    | .conflictingNextSyncCommittee store update =>
      s!"the next sync committee differs from the store's: aggregate keys " ++
        s!"{hexString store.toList} in the store and {hexString update.toList} in the update"
    | .invalidNextSyncCommitteeBranch gindex stateRoot =>
      s!"the next sync committee branch at generalized index {gindex} " ++
        s!"does not reach state root {hexString stateRoot.toList}"
    | .invalidSignature signingRoot =>
      s!"the sync committee signature does not verify for signing root " ++
        hexString signingRoot.toList
    | .finalizedPeriodMismatch finalized store =>
      s!"finalized period {finalized}, expected the store period {store}"
    | .slotOverflow finalized timeout =>
      s!"finalized slot {finalized} plus timeout {timeout} leaves the 64-bit range"
    | .forkNotSpecified fork => s!"fork {fork.name} has no light client"
    | .beforeAltair epoch altair => s!"state epoch {epoch} is before the Altair epoch {altair}"
    | .stateNotAtBlock stateSlot blockSlot =>
      s!"state slot {stateSlot}, expected the slot of its latest block {blockSlot}"
    | .stateNotOfBlock stateBlock block =>
      s!"the block root of the state {hexString stateBlock.toList} " ++
        s!"differs from the root it must equal {hexString block.toList}"
    | .finalizedNotOfState stateFinalized block =>
      s!"the finalized root of the state {hexString stateFinalized.toList} differs from " ++
        s!"{hexString block.toList}, the root of the given block, or zero at the genesis slot"

end LightClientError

/-- A root, or the error of the light client when it cannot be computed. -/
def LightClientError.liftRoot {α : Type} (result : Except Err α) : Except LightClientError α :=
  result.mapError .ssz

/-- The forks that have a light client: from Altair on. -/
def LightClientError.requireFork (fork : Fork) : Except LightClientError Unit :=
  if .altair ≤ fork then .ok () else .error (.forkNotSpecified fork)

/-- The proof that a fork has a light client, or the error that it has none. -/
def LightClientError.specifiedFork (fork : Fork) :
    Except LightClientError (PLift (.altair ≤ fork)) :=
  if h : .altair ≤ fork then .ok ⟨h⟩ else .error (.forkNotSpecified fork)

open Base (ensure)
open LightClientError (liftRoot requireFork)

/-- Whether two values have the same SSZ value, field by field. -/
def sameSszValue {α : Type} [SszType α] (a b : α) : Bool :=
  SszType.toValue a == SszType.toValue b

/-- The 32 zero bytes. -/
def zeroBytes32 : Bytes32 := Vector.replicate 32 0

/-- The execution payload header of Capella with the fields that a later header shares. -/
def ExecutionPayloadHeader.toCapella {preset : Preset} {fork : Fork} (capella : .shapella ≤ fork)
    (header : ExecutionPayloadHeader preset fork) : ExecutionPayloadHeader preset .shapella where
  parentHash := header.parentHash
  feeRecipient := header.feeRecipient
  stateRoot := header.stateRoot
  receiptsRoot := header.receiptsRoot
  logsBloom := header.logsBloom
  prevRandao := header.prevRandao
  blockNumber := header.blockNumber
  gasLimit := header.gasLimit
  gasUsed := header.gasUsed
  timestamp := header.timestamp
  extraData := header.extraData
  baseFeePerGas := header.baseFeePerGas
  blockHash := header.blockHash
  transactionsRoot := header.transactionsRoot
  withdrawalsRoot := fun _ => header.withdrawalsRoot capella
  blobGasUsed := fun deneb => absurd deneb (by decide)
  excessBlobGas := fun deneb => absurd deneb (by decide)

/-- The header whose fields are all zero, which stands for no header. -/
def LightClientHeader.empty (preset : Preset) (fork : Fork) : LightClientHeader preset fork where
  beacon := ⟨0, 0, zeroBytes32, zeroBytes32, zeroBytes32⟩
  execution := fun _ => ExecutionPayloadHeader.empty preset fork
  executionBlockHash := fun _ => zeroBytes32
  executionBranch := fun _ => Vector.replicate _ zeroBytes32

variable {preset : Preset} {fork : Fork}

/-- The root of the execution payload header of a block, from the block hash in a Gloas header.

The header is of a slot from Capella to Fulu, whose header fork is given. -/
def rebuildLcExecutionRoot (slot : Slot) (blockHash : Hash32) (branch : List Bytes32)
    (payloadFork : Fork) : Except LightClientError Root := do
  -- At the genesis slot, the root of the empty execution payload header of the header fork.
  if slot = GENESIS_SLOT then
    return ← liftRoot (SszType.hashTreeRoot (ExecutionPayloadHeader.empty preset payloadFork))
  -- Let `g` be the generalized index of the block hash in that execution payload header.
  let gindex := payloadHeaderBlockHashGindex payloadFork
  -- The inner part of the branch drops its last `floor(log2(EXECUTION_PAYLOAD_GINDEX))` nodes.
  --
  -- Those nodes climb from the execution payload up to the body root.
  let inner := branch.take (branch.length - Nat.log2 EXECUTION_PAYLOAD_GINDEX)
  -- Let `d = floor(log2(g))`.
  --
  -- The block hash climbs by the last `d` nodes of the inner part, from position `g mod 2^d`.
  liftRoot (computeMerkleBranchRoot blockHash (inner.drop (inner.length - Nat.log2 gindex))
    (Nat.log2 gindex) (← liftRoot (getSubtreeIndex gindex)))

/-- The root of the execution data that a light client header carries, zero before Capella. -/
def getLcExecutionRoot (config : Config) (header : LightClientHeader preset fork) :
    Except LightClientError Root := do
  -- The fork is Altair or later, the first with a light client; an earlier fork fails.
  requireFork fork
  -- Let `e` be the epoch of the slot of the header.
  let epoch := computeEpochAtSlot preset header.beacon.slot
  -- From Gloas, the header carries a block hash and its branch.
  if gloas : .glamsterdam ≤ fork then
    let blockHash := header.executionBlockHash gloas
    let branch := (header.executionBranch (Nat.le_trans (by decide) gloas)).toList
    -- For `GLOAS_FORK_EPOCH ≤ e`, the root is the block hash.
    if config.GLOAS_FORK_EPOCH ≤ epoch then return blockHash
    -- For `DENEB_FORK_EPOCH ≤ e`, the root of the Deneb execution payload header, rebuilt.
    else if config.DENEB_FORK_EPOCH ≤ epoch then
      rebuildLcExecutionRoot (preset := preset) header.beacon.slot blockHash branch .dencun
    -- For `CAPELLA_FORK_EPOCH ≤ e`, the root of the Capella execution payload header, rebuilt.
    else if config.CAPELLA_FORK_EPOCH ≤ epoch then
      rebuildLcExecutionRoot (preset := preset) header.beacon.slot blockHash branch .shapella
    -- For an earlier slot, the root is zero.
    else return zeroBytes32
  -- From Capella to Fulu, the header carries an execution payload header.
  else if capella : .shapella ≤ fork then
    let execution := header.execution ⟨capella, Nat.lt_of_not_le gloas⟩
    -- From Deneb, for `DENEB_FORK_EPOCH ≤ e`, the root of the execution payload header.
    if .dencun ≤ fork ∧ config.DENEB_FORK_EPOCH ≤ epoch then
      liftRoot (SszType.hashTreeRoot execution)
    -- For `CAPELLA_FORK_EPOCH ≤ e`, the root of the header cut to the fields of Capella.
    --
    -- A Capella header has only those fields, so for it the root is that of the header itself.
    else if config.CAPELLA_FORK_EPOCH ≤ epoch then
      liftRoot (SszType.hashTreeRoot (execution.toCapella capella))
    -- For an earlier slot, the root is zero.
    else return zeroBytes32
  -- Before Capella, the root is zero.
  else return zeroBytes32

/-- Whether a light client header is valid for the fork of its slot.

A header of a fork before Capella is always valid. -/
def isValidLightClientHeader (config : Config) (header : LightClientHeader preset fork) :
    Except LightClientError Bool := do
  -- The fork is Altair or later, the first with a light client; an earlier fork fails.
  requireFork fork
  -- Let `e` be the epoch of the slot of the header.
  let epoch := computeEpochAtSlot preset header.beacon.slot
  -- From Gloas, the header carries a block hash `h` and its branch.
  if gloas : .glamsterdam ≤ fork then
    let blockHash := header.executionBlockHash gloas
    let branch := (header.executionBranch (Nat.le_trans (by decide) gloas)).toList
    -- Let `d = floor(log2(g))` for the generalized index `g`.
    --
    -- The nodes of the branch before its last `d` are zero.
    --
    -- `h` climbs to the body root by those last `d` nodes, from the generalized index `g`.
    let climbs (gindex : Nat) : Except LightClientError Bool :=
      liftRoot (isValidNormalizedMerkleBranch blockHash branch gindex header.beacon.bodyRoot)
    -- For `GLOAS_FORK_EPOCH ≤ e`, `g` is `EXECUTION_BLOCK_HASH_GINDEX_GLOAS`.
    if config.GLOAS_FORK_EPOCH ≤ epoch then climbs EXECUTION_BLOCK_HASH_GINDEX_GLOAS
    -- For `DENEB_FORK_EPOCH ≤ e`, `g` is `EXECUTION_BLOCK_HASH_GINDEX_DENEB`.
    else if config.DENEB_FORK_EPOCH ≤ epoch then climbs EXECUTION_BLOCK_HASH_GINDEX_DENEB
    -- For `CAPELLA_FORK_EPOCH ≤ e`, `g` is `EXECUTION_BLOCK_HASH_GINDEX`.
    else if config.CAPELLA_FORK_EPOCH ≤ epoch then climbs EXECUTION_BLOCK_HASH_GINDEX
    -- For an earlier slot, `h` and each node of the branch are zero.
    else return blockHash == zeroBytes32 && branch.all (· == zeroBytes32)
  -- From Capella to Fulu, the header carries an execution payload header and its branch.
  else if capella : .shapella ≤ fork then
    let execution := header.execution ⟨capella, Nat.lt_of_not_le gloas⟩
    let branch := header.executionBranch capella
    -- From Deneb, for `e < DENEB_FORK_EPOCH`, the blob gas used and the excess blob gas are 0.
    if deneb : .dencun ≤ fork then
      if epoch < config.DENEB_FORK_EPOCH ∧
          (execution.blobGasUsed deneb ≠ 0 ∨ execution.excessBlobGas deneb ≠ 0) then
        return false
    -- For `e < CAPELLA_FORK_EPOCH`, the execution payload header is empty, and the branch zero.
    if epoch < config.CAPELLA_FORK_EPOCH then
      return sameSszValue execution (ExecutionPayloadHeader.empty preset fork) &&
        branch == Vector.replicate _ zeroBytes32
    -- Otherwise the execution root of the header climbs to the body root by the branch.
    --
    -- It climbs from generalized index `EXECUTION_PAYLOAD_GINDEX`.
    let leaf ← getLcExecutionRoot config header
    return isValidMerkleBranch leaf branch.toList (Nat.log2 EXECUTION_PAYLOAD_GINDEX)
      (← liftRoot (getSubtreeIndex EXECUTION_PAYLOAD_GINDEX)) header.beacon.bodyRoot
  -- Before Capella, every header is valid.
  else return true

/-- The fork whose state layout holds at a slot, for a light client from Altair. -/
def stateForkAtSlot (config : Config) (slot : Slot) : Except LightClientError Fork := do
  -- The fork is Altair or later, the first with a light client; an earlier fork fails.
  requireFork fork
  -- Let `e` be the epoch of the slot.
  let epoch := computeEpochAtSlot preset slot
  -- A client from Gloas reads the layout of Gloas for `GLOAS_FORK_EPOCH ≤ e`.
  if .glamsterdam ≤ fork ∧ config.GLOAS_FORK_EPOCH ≤ epoch then return .glamsterdam
  -- A client from Electra reads the layout of Electra for `ELECTRA_FORK_EPOCH ≤ e`.
  if .pectra ≤ fork ∧ config.ELECTRA_FORK_EPOCH ≤ epoch then return .pectra
  -- Otherwise, and for every slot of a client before Electra, the layout of Altair holds.
  return .altair

/-- The generalized index of the finalized root, in the state at a slot. -/
def finalizedRootGindexAtSlot (config : Config) (slot : Slot) : Except LightClientError Nat :=
  -- The index in the state layout that holds at the slot.
  finalizedRootGindex <$> stateForkAtSlot (preset := preset) (fork := fork) config slot

/-- The generalized index of the current sync committee, in the state at a slot. -/
def currentSyncCommitteeGindexAtSlot (config : Config) (slot : Slot) :
    Except LightClientError Nat :=
  -- The index in the state layout that holds at the slot.
  currentSyncCommitteeGindex <$> stateForkAtSlot (preset := preset) (fork := fork) config slot

/-- The generalized index of the next sync committee, in the state at a slot. -/
def nextSyncCommitteeGindexAtSlot (config : Config) (slot : Slot) : Except LightClientError Nat :=
  -- The index in the state layout that holds at the slot.
  nextSyncCommitteeGindex <$> stateForkAtSlot (preset := preset) (fork := fork) config slot

/-- Whether an update proves the next sync committee: its committee branch is not all zero. -/
def LightClientUpdate.isSyncCommitteeUpdate (update : LightClientUpdate preset fork) : Bool :=
  update.nextSyncCommitteeBranch != Vector.replicate _ zeroBytes32

/-- Whether an update proves a finalized header: its finality branch is not all zero. -/
def LightClientUpdate.isFinalityUpdate (update : LightClientUpdate preset fork) : Bool :=
  update.finalityBranch != Vector.replicate _ zeroBytes32

/-- The number of members of the sync committee that signed. -/
def SyncAggregate.participants (aggregate : SyncAggregate preset) : Nat :=
  aggregate.syncCommitteeBits.bits.toList.count true

/-- Whether a new update is better than an old one, for a forced update. -/
def isBetterUpdate (newUpdate oldUpdate : LightClientUpdate preset fork) : Bool := Id.run do
  -- Let `n` be `SYNC_COMMITTEE_SIZE`, the length of the bits of each update.
  let maxActive := preset.SYNC_COMMITTEE_SIZE.toNat
  -- The numbers of signers of the new and the old update.
  let newActive := newUpdate.syncAggregate.participants
  let oldActive := oldUpdate.syncAggregate.participants
  -- An update with `k` signers has a supermajority when `3k ≥ 2n`.
  let newSupermajority := newActive * 3 ≥ maxActive * 2
  let oldSupermajority := oldActive * 3 ≥ maxActive * 2
  -- The update with a supermajority ranks first.
  if newSupermajority ≠ oldSupermajority then return newSupermajority
  -- Without a supermajority, the update with more signers ranks first.
  if !newSupermajority ∧ newActive ≠ oldActive then return newActive > oldActive
  -- Then the relevant update ranks first.
  --
  -- A relevant update proves a next committee, and its attested and signature slots share a period.
  let period := computeSyncCommitteePeriodAtSlot preset
  let relevant (update : LightClientUpdate preset fork) : Bool :=
    update.isSyncCommitteeUpdate &&
      period update.attestedHeader.beacon.slot == period update.signatureSlot
  if relevant newUpdate ≠ relevant oldUpdate then return relevant newUpdate
  -- Then the update that proves a finalized header ranks first.
  let newFinality := newUpdate.isFinalityUpdate
  if newFinality ≠ oldUpdate.isFinalityUpdate then return newFinality
  -- When both prove one, the one whose finalized header is in its attested period ranks first.
  if newFinality then
    let committeeFinality (update : LightClientUpdate preset fork) : Bool :=
      period update.finalizedHeader.beacon.slot == period update.attestedHeader.beacon.slot
    if committeeFinality newUpdate ≠ committeeFinality oldUpdate then
      return committeeFinality newUpdate
  -- Then more signers break the tie.
  if newActive ≠ oldActive then return newActive > oldActive
  -- Then an earlier attested slot.
  if newUpdate.attestedHeader.beacon.slot ≠ oldUpdate.attestedHeader.beacon.slot then
    return newUpdate.attestedHeader.beacon.slot < oldUpdate.attestedHeader.beacon.slot
  -- Then an earlier signature slot.
  return newUpdate.signatureSlot < oldUpdate.signatureSlot

namespace LightClientStore

/-- Whether the store knows the next sync committee: its next committee is not all zero. -/
def isNextSyncCommitteeKnown (store : LightClientStore preset fork) : Bool :=
  store.nextSyncCommittee != SyncCommittee.empty preset

/-- Half of the most signers seen in the current or the previous period, rounded down. -/
def safetyThreshold (store : LightClientStore preset fork) : UInt64 :=
  -- `floor(max(p, c) / 2)`, for the most signers `p` of the previous period and `c` of the current.
  max store.previousMaxActiveParticipants store.currentMaxActiveParticipants / 2

end LightClientStore

/-- The store of a light client that trusts a block, from a bootstrap for that block. -/
def initializeLightClientStore (config : Config) (trustedBlockRoot : Root)
    (bootstrap : LightClientBootstrap preset fork) :
    Except LightClientError (LightClientStore preset fork) := do
  -- The fork is Altair or later, the first with a light client; an earlier fork fails.
  requireFork fork
  -- The header is valid for the fork of its slot.
  ensure (← isValidLightClientHeader config bootstrap.header)
    (.invalidHeader bootstrap.header.beacon.slot)
  -- The root of its beacon header is the trusted block root.
  let headerRoot ← liftRoot (SszType.hashTreeRoot bootstrap.header.beacon)
  ensure (headerRoot = trustedBlockRoot) (.untrustedHeader trustedBlockRoot headerRoot)
  -- The current committee climbs to the state root of the header by its normalized branch.
  --
  -- Before Electra the branch has exactly the depth, so this check is the plain one.
  --
  -- Its generalized index is that of the state layout at the slot of the header.
  let leaf ← liftRoot (SszType.hashTreeRoot bootstrap.currentSyncCommittee)
  let gindex ← currentSyncCommitteeGindexAtSlot (preset := preset) (fork := fork) config
    bootstrap.header.beacon.slot
  ensure (← liftRoot (isValidNormalizedMerkleBranch leaf
      bootstrap.currentSyncCommitteeBranch.toList gindex bootstrap.header.beacon.stateRoot))
    (.invalidCurrentSyncCommitteeBranch gindex bootstrap.header.beacon.stateRoot)
  -- The header is both finalized and optimistic, and the committee is the current one.
  --
  -- The next committee is unknown, there is no best update, and both maxima of signers are 0.
  return {
    finalizedHeader := bootstrap.header
    currentSyncCommittee := bootstrap.currentSyncCommittee
    nextSyncCommittee := SyncCommittee.empty preset
    bestValidUpdate := none
    optimisticHeader := bootstrap.header
    previousMaxActiveParticipants := 0
    currentMaxActiveParticipants := 0 }

/-- The keys of the members of a committee whose bit is set, in committee order. -/
def SyncCommittee.participantKeys (committee : SyncCommittee preset)
    (aggregate : SyncAggregate preset) : Array BLSPubkey :=
  ((aggregate.syncCommitteeBits.bits.toList.zip committee.pubkeys.toList).filterMap
    fun (bit, key) => if bit then some key else none).toArray

/-- The finality check of an update, which reads no store.

The finalized root of the genesis slot is zero. -/
def validateFinality (config : Config) (update : LightClientUpdate preset fork) :
    Except LightClientError Unit := do
  -- An update that proves no finalized header carries the empty header.
  if !update.isFinalityUpdate then
    ensure (sameSszValue update.finalizedHeader (LightClientHeader.empty preset fork))
      (.unexpectedFinalizedHeader update.finalizedHeader.beacon.slot)
  else
    -- At the genesis slot, the finalized header is the empty one, and its root is zero.
    let finalizedRoot ← if update.finalizedHeader.beacon.slot = GENESIS_SLOT then do
        ensure (sameSszValue update.finalizedHeader (LightClientHeader.empty preset fork))
          (.unexpectedFinalizedHeader update.finalizedHeader.beacon.slot)
        pure zeroBytes32
      -- At another slot, the finalized header is valid for the fork of its slot.
      --
      -- Its root is that of its beacon header.
      else do
        ensure (← isValidLightClientHeader config update.finalizedHeader)
          (.invalidHeader update.finalizedHeader.beacon.slot)
        liftRoot (SszType.hashTreeRoot update.finalizedHeader.beacon)
    -- The root climbs to the attested state root by the normalized finality branch.
    --
    -- Its generalized index is that of the state layout at the attested slot.
    let gindex ← finalizedRootGindexAtSlot (preset := preset) (fork := fork) config
      update.attestedHeader.beacon.slot
    ensure (← liftRoot (isValidNormalizedMerkleBranch finalizedRoot update.finalityBranch.toList
        gindex update.attestedHeader.beacon.stateRoot))
      (.invalidFinalityBranch gindex update.attestedHeader.beacon.stateRoot)

/-- The branch check of the next sync committee of an update, against the attested state root. -/
def validateNextSyncCommitteeBranch (config : Config) (update : LightClientUpdate preset fork) :
    Except LightClientError Unit := do
  -- The next committee climbs to the attested state root by its normalized branch.
  --
  -- Its generalized index is that of the state layout at the attested slot.
  let leaf ← liftRoot (SszType.hashTreeRoot update.nextSyncCommittee)
  let gindex ← nextSyncCommitteeGindexAtSlot (preset := preset) (fork := fork) config
    update.attestedHeader.beacon.slot
  ensure (← liftRoot (isValidNormalizedMerkleBranch leaf update.nextSyncCommitteeBranch.toList
      gindex update.attestedHeader.beacon.stateRoot))
    (.invalidNextSyncCommitteeBranch gindex update.attestedHeader.beacon.stateRoot)

/-- The committee that signs an update, by the period of its signature slot. -/
def LightClientStore.signatureCommittee (store : LightClientStore preset fork)
    (update : LightClientUpdate preset fork) : SyncCommittee preset :=
  let period := computeSyncCommitteePeriodAtSlot preset
  -- The current committee, when the signature slot is in the period of the finalized header.
  if period update.signatureSlot = period store.finalizedHeader.beacon.slot then
    store.currentSyncCommittee
  -- Otherwise the next committee.
  else store.nextSyncCommittee

/-- The root that the sync committee signs for an update. -/
def syncCommitteeSigningRoot (config : Config) (update : LightClientUpdate preset fork)
    (genesisValidatorsRoot : Root) : Except LightClientError Root := do
  -- Let `s` be the signature slot.
  --
  -- The fork version is that of the epoch of slot `s - 1`, or of slot 0 when `s` is 0.
  let forkVersionSlot := if update.signatureSlot = 0 then 0 else update.signatureSlot - 1
  let forkVersion := config.computeForkVersion (computeEpochAtSlot preset forkVersionSlot)
  -- The domain of the sync committee, at that version and the genesis validators root.
  let domain ← liftRoot
    (computeDomain config DOMAIN_SYNC_COMMITTEE forkVersion genesisValidatorsRoot)
  -- The signing root of the attested beacon header, in that domain.
  liftRoot (computeSigningRoot update.attestedHeader.beacon domain)

/-- The checks of an update against a store, at a slot of the local clock. -/
def validateLightClientUpdate (config : Config) (checks : SignatureChecks)
    (store : LightClientStore preset fork) (update : LightClientUpdate preset fork)
    (currentSlot : Slot) (genesisValidatorsRoot : Root) : Except LightClientError Unit := do
  -- The fork is Altair or later, the first with a light client; an earlier fork fails.
  requireFork fork
  -- At least `MIN_SYNC_COMMITTEE_PARTICIPANTS` members of the committee sign.
  let aggregate := update.syncAggregate
  ensure (aggregate.participants ≥ preset.MIN_SYNC_COMMITTEE_PARTICIPANTS.toNat)
    (.tooFewParticipants aggregate.participants preset.MIN_SYNC_COMMITTEE_PARTICIPANTS.toNat)
  -- The attested header is valid for the fork of its slot.
  ensure (← isValidLightClientHeader config update.attestedHeader)
    (.invalidHeader update.attestedHeader.beacon.slot)
  -- Let `a` be the attested slot, `f` the finalized slot and `s` the signature slot.
  --
  -- `c ≥ s > a ≥ f`, for the current slot `c`.
  let attestedSlot := update.attestedHeader.beacon.slot
  let finalizedSlot := update.finalizedHeader.beacon.slot
  ensure (currentSlot ≥ update.signatureSlot ∧ update.signatureSlot > attestedSlot ∧
    attestedSlot ≥ finalizedSlot)
    (.slotsOutOfOrder currentSlot update.signatureSlot attestedSlot finalizedSlot)
  -- Let `p` be the period of the finalized header of the store, and `q` the period of `s`.
  let period := computeSyncCommitteePeriodAtSlot preset
  let storePeriod := period store.finalizedHeader.beacon.slot
  let signaturePeriod := period update.signatureSlot
  -- When the store knows the next committee, `q` is `p` or `p + 1`.
  if store.isNextSyncCommitteeKnown then
    ensure (signaturePeriod = storePeriod ∨ signaturePeriod = storePeriod + 1)
      (.unknownSignaturePeriod signaturePeriod storePeriod true)
  -- Otherwise `q = p`.
  else
    ensure (signaturePeriod = storePeriod)
      (.unknownSignaturePeriod signaturePeriod storePeriod false)
  -- The update is relevant: `a` is after the finalized slot of the store.
  --
  -- Or the store lacks the next committee, and the update proves one, with `a` in period `p`.
  let attestedPeriod := period attestedSlot
  let hasNextSyncCommittee := !store.isNextSyncCommitteeKnown &&
    (update.isSyncCommitteeUpdate && attestedPeriod == storePeriod)
  ensure (attestedSlot > store.finalizedHeader.beacon.slot ∨ hasNextSyncCommittee)
    (.irrelevantUpdate attestedSlot store.finalizedHeader.beacon.slot)
  -- The finality branch proves the finalized header against the attested state root.
  --
  -- An update that proves no finalized header carries the empty one.
  validateFinality config update
  -- An update that proves no next committee carries the empty committee.
  if !update.isSyncCommitteeUpdate then
    ensure (update.nextSyncCommittee = SyncCommittee.empty preset)
      (.unexpectedNextSyncCommittee update.nextSyncCommittee.aggregatePubkey)
  else
    -- With `a` in period `p`, the next committee that the store knows is that of the update.
    if attestedPeriod = storePeriod ∧ store.isNextSyncCommitteeKnown then
      ensure (update.nextSyncCommittee = store.nextSyncCommittee)
        (.conflictingNextSyncCommittee store.nextSyncCommittee.aggregatePubkey
          update.nextSyncCommittee.aggregatePubkey)
    -- The next committee climbs to the attested state root by its branch.
    validateNextSyncCommitteeBranch config update
  -- The keys of the signers, in the current committee for `q = p`, and else in the next one.
  let keys := (store.signatureCommittee update).participantKeys aggregate
  -- The root of the attested beacon header, at the fork version of slot `max(s, 1) - 1`.
  let signingRoot ← syncCommitteeSigningRoot config update genesisValidatorsRoot
  -- The aggregate signature verifies for those keys and that root.
  ensure (checks.fastAggregateVerify keys (packBytes signingRoot)
    aggregate.syncCommitteeSignature = true) (.invalidSignature signingRoot)

/-- The store after it applies an update that it has checked. -/
def applyLightClientUpdate (store : LightClientStore preset fork)
    (update : LightClientUpdate preset fork) :
    Except LightClientError (LightClientStore preset fork) := do
  -- The fork is Altair or later, the first with a light client; an earlier fork fails.
  requireFork fork
  -- Let `p` be the period of the finalized header of the store, and `q` that of the update's.
  let period := computeSyncCommitteePeriodAtSlot preset
  let storePeriod := period store.finalizedHeader.beacon.slot
  let finalizedPeriod := period update.finalizedHeader.beacon.slot
  -- When the store lacks the next committee, `q = p`.
  --
  -- The committee of the update becomes the next committee.
  let store ← if !store.isNextSyncCommitteeKnown then do
      ensure (finalizedPeriod = storePeriod)
        (.finalizedPeriodMismatch finalizedPeriod storePeriod)
      pure { store with nextSyncCommittee := update.nextSyncCommittee }
    -- When `q = p + 1`, the next committee becomes the current one.
    --
    -- The committee of the update becomes the next committee.
    --
    -- The current maximum of signers becomes the previous one, and the current one restarts at 0.
    else if finalizedPeriod = storePeriod + 1 then
      pure { store with
        currentSyncCommittee := store.nextSyncCommittee
        nextSyncCommittee := update.nextSyncCommittee
        previousMaxActiveParticipants := store.currentMaxActiveParticipants
        currentMaxActiveParticipants := 0 }
    -- Otherwise the committees stay.
    else pure store
  -- A newer finalized header of the update replaces that of the store.
  if update.finalizedHeader.beacon.slot > store.finalizedHeader.beacon.slot then
    let store := { store with finalizedHeader := update.finalizedHeader }
    -- It also replaces the optimistic header, if it is newer than that one.
    if store.finalizedHeader.beacon.slot > store.optimisticHeader.beacon.slot then
      return { store with optimisticHeader := store.finalizedHeader }
    return store
  return store

/-- The store after a forced update, when no finalized header came for a whole period.

The slot after which the update is forced is a 64-bit sum, which fails when it overflows. -/
def processLightClientStoreForceUpdate (store : LightClientStore preset fork)
    (currentSlot : Slot) : Except LightClientError (LightClientStore preset fork) := do
  -- The fork is Altair or later, the first with a light client; an earlier fork fails.
  requireFork fork
  -- Let `t = x + UPDATE_TIMEOUT`, for the finalized slot `x` of the store, with `t < 2^64`.
  let timeout := store.finalizedHeader.beacon.slot.toNat + preset.UPDATE_TIMEOUT.toNat
  ensure (timeout < 2 ^ 64)
    (.slotOverflow store.finalizedHeader.beacon.slot preset.UPDATE_TIMEOUT)
  -- The best update that the store kept is forced once the current slot is after `t`.
  match store.bestValidUpdate with
  | some best =>
    if currentSlot.toNat > timeout then
      -- If its finalized slot is at most `x`, its attested header becomes its finalized header.
      let best := if best.finalizedHeader.beacon.slot ≤ store.finalizedHeader.beacon.slot then
        { best with finalizedHeader := best.attestedHeader }
      else best
      -- It is applied, then dropped.
      let store ← applyLightClientUpdate store best
      return { store with bestValidUpdate := none }
    else return store
  | none => return store

/-- The store after an update, which it checks first. -/
def processLightClientUpdate (config : Config) (checks : SignatureChecks)
    (store : LightClientStore preset fork) (update : LightClientUpdate preset fork)
    (currentSlot : Slot) (genesisValidatorsRoot : Root) :
    Except LightClientError (LightClientStore preset fork) := do
  -- The update passes the checks against the store, at the current slot.
  validateLightClientUpdate config checks store update currentSlot genesisValidatorsRoot
  -- Let `k` be the number of signers of the update.
  let active := update.syncAggregate.participants
  -- The update becomes the best update when the store keeps none, or a worse one.
  let store := match store.bestValidUpdate with
    | some best => if isBetterUpdate update best then { store with bestValidUpdate := update }
      else store
    | none => { store with bestValidUpdate := update }
  -- The most signers `c` of the current period become `max(c, k)`.
  let store := { store with
    currentMaxActiveParticipants := max store.currentMaxActiveParticipants active.toUInt64 }
  -- The attested header becomes the optimistic header when `k` exceeds the safety threshold.
  --
  -- The threshold reads the most signers just updated.
  --
  -- The attested header must also be newer than the optimistic header.
  let store := if active > store.safetyThreshold.toNat ∧
      update.attestedHeader.beacon.slot > store.optimisticHeader.beacon.slot then
    { store with optimisticHeader := update.attestedHeader }
  else store
  -- The update finalizes the next committee when the store lacks it and the update proves it.
  --
  -- The update must also prove a finalized header in the period of its attested header.
  let period := computeSyncCommitteePeriodAtSlot preset
  let finalizedNextSyncCommittee := !store.isNextSyncCommitteeKnown &&
    update.isSyncCommitteeUpdate && update.isFinalityUpdate &&
    period update.finalizedHeader.beacon.slot == period update.attestedHeader.beacon.slot
  -- Let `n` be `SYNC_COMMITTEE_SIZE`, the length of the bits.
  --
  -- With `3k ≥ 2n`, the update is applied if it finalizes a header newer than that of the store.
  --
  -- It is also applied if it finalizes the next committee.
  if active * 3 ≥ preset.SYNC_COMMITTEE_SIZE.toNat * 2 ∧
      (update.finalizedHeader.beacon.slot > store.finalizedHeader.beacon.slot ∨
        finalizedNextSyncCommittee) then
    let store ← applyLightClientUpdate store update
    -- The best update is then dropped.
    return { store with bestValidUpdate := none }
  return store

/-- The update that a finality update stands for: no next committee, and zero for its branch. -/
def LightClientFinalityUpdate.toUpdate (update : LightClientFinalityUpdate preset fork) :
    LightClientUpdate preset fork where
  attestedHeader := update.attestedHeader
  nextSyncCommittee := SyncCommittee.empty preset
  nextSyncCommitteeBranch := Vector.replicate _ zeroBytes32
  finalizedHeader := update.finalizedHeader
  finalityBranch := update.finalityBranch
  syncAggregate := update.syncAggregate
  signatureSlot := update.signatureSlot

/-- The update that an optimistic update stands for: no next committee, no finalized header. -/
def LightClientOptimisticUpdate.toUpdate (update : LightClientOptimisticUpdate preset fork) :
    LightClientUpdate preset fork where
  attestedHeader := update.attestedHeader
  nextSyncCommittee := SyncCommittee.empty preset
  nextSyncCommitteeBranch := Vector.replicate _ zeroBytes32
  finalizedHeader := LightClientHeader.empty preset fork
  finalityBranch := Vector.replicate _ zeroBytes32
  syncAggregate := update.syncAggregate
  signatureSlot := update.signatureSlot

/-- The store after a finality update, processed as the update that it stands for. -/
def processLightClientFinalityUpdate (config : Config) (checks : SignatureChecks)
    (store : LightClientStore preset fork) (update : LightClientFinalityUpdate preset fork)
    (currentSlot : Slot) (genesisValidatorsRoot : Root) :
    Except LightClientError (LightClientStore preset fork) :=
  processLightClientUpdate config checks store update.toUpdate currentSlot genesisValidatorsRoot

/-- The store after an optimistic update, processed as the update that it stands for. -/
def processLightClientOptimisticUpdate (config : Config) (checks : SignatureChecks)
    (store : LightClientStore preset fork) (update : LightClientOptimisticUpdate preset fork)
    (currentSlot : Slot) (genesisValidatorsRoot : Root) :
    Except LightClientError (LightClientStore preset fork) :=
  processLightClientUpdate config checks store update.toUpdate currentSlot genesisValidatorsRoot

end EthLib.Consensus
