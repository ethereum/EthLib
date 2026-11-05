module

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

EthLib specifies the light client from Altair to Fulu.

Before Altair there is none, and the light client of Gloas changes rules that are not yet here.

So every check of a store, a header or an update fails outside that range.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

/-- Why a light client refuses a bootstrap or an update. -/
inductive LightClientError where
  /-- A root could not be computed. -/
  | ssz (error : Err)
  /-- A header fails the checks of its fork. -/
  | invalidHeader
  /-- The header of a bootstrap is not the block that the client trusts. -/
  | untrustedHeader
  /-- The branch of the current sync committee does not reach the state root. -/
  | invalidCurrentSyncCommitteeBranch
  /-- Fewer members than the minimum signed the update. -/
  | tooFewParticipants
  /-- The slots of the update are not ordered: now, signature, attested header, finalized header. -/
  | slotsOutOfOrder
  /-- The update is signed in a period whose committee the store does not know. -/
  | unknownSignaturePeriod
  /-- The update brings neither a newer header nor the next sync committee. -/
  | irrelevantUpdate
  /-- An update without a finality branch carries a finalized header. -/
  | unexpectedFinalizedHeader
  /-- The finality branch does not reach the state root of the attested header. -/
  | invalidFinalityBranch
  /-- An update without a committee branch carries a next sync committee. -/
  | unexpectedNextSyncCommittee
  /-- The next sync committee of the update differs from the one that the store knows. -/
  | conflictingNextSyncCommittee
  /-- The branch of the next sync committee does not reach the state root of the attested header. -/
  | invalidNextSyncCommitteeBranch
  /-- The sync committee signature does not verify. -/
  | invalidSignature
  /-- The finalized header of an update lies outside the period of the store. -/
  | finalizedPeriodMismatch
  /-- The slot after which an update is forced leaves the 64-bit range. -/
  | slotOverflow
  /-- The fork has no light client, before Altair, or its light client is not yet specified. -/
  | forkNotSpecified (fork : Fork)
  /-- A full node derives data from a state before Altair. -/
  | beforeAltair
  /-- A full node derives data from a state that is not at the slot of its latest block. -/
  | stateNotAtBlock
  /-- A full node derives data from a state that is not the post state of the block. -/
  | stateNotOfBlock
  /-- The finalized block that a full node gives is not the finalized block of the state. -/
  | finalizedNotOfState
  deriving DecidableEq, Repr

namespace LightClientError

/-- The code of an error: one per constructor, from 1. -/
def code : LightClientError → UInt32
  | .ssz _ => 1
  | .invalidHeader => 2
  | .untrustedHeader => 3
  | .invalidCurrentSyncCommitteeBranch => 4
  | .tooFewParticipants => 5
  | .slotsOutOfOrder => 6
  | .unknownSignaturePeriod => 7
  | .irrelevantUpdate => 8
  | .unexpectedFinalizedHeader => 9
  | .invalidFinalityBranch => 10
  | .unexpectedNextSyncCommittee => 11
  | .conflictingNextSyncCommittee => 12
  | .invalidNextSyncCommitteeBranch => 13
  | .invalidSignature => 14
  | .finalizedPeriodMismatch => 15
  | .slotOverflow => 16
  | .forkNotSpecified _ => 17
  | .beforeAltair => 18
  | .stateNotAtBlock => 19
  | .stateNotOfBlock => 20
  | .finalizedNotOfState => 21

end LightClientError

/-- A check that holds, or the error that its failure raises. -/
def LightClientError.require (condition : Prop) [Decidable condition] (error : LightClientError) :
    Except LightClientError Unit :=
  if condition then .ok () else .error error

/-- A root, or the error of the light client when it cannot be computed. -/
def LightClientError.liftRoot {α : Type} (result : Except Err α) : Except LightClientError α :=
  result.mapError .ssz

/-- The forks whose light client EthLib specifies: from Altair to Fulu.

Gloas changes the generalized indices and the checks of a header, which are not yet specified. -/
def LightClientError.requireFork (fork : Fork) : Except LightClientError Unit :=
  if .altair ≤ fork ∧ fork < .glamsterdam then .ok () else .error (.forkNotSpecified fork)

/-- The proof that a fork has a specified light client, or the error that it has none. -/
def LightClientError.specifiedFork (fork : Fork) :
    Except LightClientError (PLift (.altair ≤ fork ∧ fork < .glamsterdam)) :=
  if h : .altair ≤ fork ∧ fork < .glamsterdam then .ok ⟨h⟩ else .error (.forkNotSpecified fork)

open LightClientError (require liftRoot requireFork)

/-- Whether two values have the same SSZ value, field by field. -/
def sameSszValue {α : Type} [SszType α] (a b : α) : Bool :=
  SszType.toValue a == SszType.toValue b

/-- The 32 zero bytes. -/
def zeroBytes32 : Bytes32 := Vector.replicate 32 0

/-- The sync committee whose keys are all zero, which stands for an unknown committee. -/
def SyncCommittee.empty (preset : Preset) : SyncCommittee preset :=
  ⟨Vector.replicate _ (Vector.replicate 48 0), Vector.replicate 48 0⟩

/-- The execution payload header whose fields are all zero or empty. -/
def ExecutionPayloadHeader.empty (preset : Preset) (fork : Fork) :
    ExecutionPayloadHeader preset fork where
  parentHash := zeroBytes32
  feeRecipient := Vector.replicate 20 0
  stateRoot := zeroBytes32
  receiptsRoot := zeroBytes32
  logsBloom := Vector.replicate _ 0
  prevRandao := zeroBytes32
  blockNumber := 0
  gasLimit := 0
  gasUsed := 0
  timestamp := 0
  extraData := ⟨#[], Nat.zero_le _⟩
  baseFeePerGas := 0
  blockHash := zeroBytes32
  transactionsRoot := zeroBytes32
  withdrawalsRoot := fun _ => zeroBytes32
  blobGasUsed := fun _ => 0
  excessBlobGas := fun _ => 0

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
  executionBranch := fun _ => Vector.replicate _ zeroBytes32

variable {preset : Preset} {fork : Fork}

/-- From Capella: the root of the execution payload header that a light client header carries.

From Deneb, a header of an earlier fork drops the fields of Deneb before it is hashed.

Before Capella, and for a header of a slot before Capella, the root is zero. -/
def getLcExecutionRoot (config : Config) (header : LightClientHeader preset fork) :
    Except LightClientError Root := do
  requireFork fork
  let epoch := computeEpochAtSlot preset header.beacon.slot
  if capella : .shapella ≤ fork then
    let execution := header.execution capella
    if .dencun ≤ fork ∧ config.DENEB_FORK_EPOCH ≤ epoch then
      liftRoot (SszType.hashTreeRoot execution)
    else if config.CAPELLA_FORK_EPOCH ≤ epoch then
      liftRoot (SszType.hashTreeRoot (execution.toCapella capella))
    else return zeroBytes32
  else return zeroBytes32

/-- Whether a light client header is valid for the fork of its slot.

From Capella, its execution header must climb to the body root by its branch.

For a slot before Capella, the execution header and its branch must be zero instead.

From Deneb, a header of a slot before Deneb must use no blob gas. -/
def isValidLightClientHeader (config : Config) (header : LightClientHeader preset fork) :
    Except LightClientError Bool := do
  requireFork fork
  if capella : .shapella ≤ fork then
    let epoch := computeEpochAtSlot preset header.beacon.slot
    let execution := header.execution capella
    let branch := header.executionBranch capella
    if deneb : .dencun ≤ fork then
      if epoch < config.DENEB_FORK_EPOCH ∧
          (execution.blobGasUsed deneb ≠ 0 ∨ execution.excessBlobGas deneb ≠ 0) then
        return false
    if epoch < config.CAPELLA_FORK_EPOCH then
      return sameSszValue execution (ExecutionPayloadHeader.empty preset fork) &&
        branch == Vector.replicate _ zeroBytes32
    let leaf ← getLcExecutionRoot config header
    return isValidMerkleBranch leaf branch.toList (Nat.log2 EXECUTION_PAYLOAD_GINDEX)
      (← liftRoot (getSubtreeIndex EXECUTION_PAYLOAD_GINDEX)) header.beacon.bodyRoot
  else return true

/-- The fork whose state layout holds at a slot, for a light client from Altair to Fulu.

From Electra, the layout of Electra holds from its first epoch.

A client before Electra reads every state with the layout of Altair. -/
def stateForkAtSlot (config : Config) (slot : Slot) : Except LightClientError Fork := do
  requireFork fork
  if .pectra ≤ fork ∧ config.ELECTRA_FORK_EPOCH ≤ computeEpochAtSlot preset slot then
    return .pectra
  return .altair

/-- The generalized index of the finalized root, in the state at a slot. -/
def finalizedRootGindexAtSlot (config : Config) (slot : Slot) : Except LightClientError Nat :=
  finalizedRootGindex <$> stateForkAtSlot (preset := preset) (fork := fork) config slot

/-- The generalized index of the current sync committee, in the state at a slot. -/
def currentSyncCommitteeGindexAtSlot (config : Config) (slot : Slot) :
    Except LightClientError Nat :=
  currentSyncCommitteeGindex <$> stateForkAtSlot (preset := preset) (fork := fork) config slot

/-- The generalized index of the next sync committee, in the state at a slot. -/
def nextSyncCommitteeGindexAtSlot (config : Config) (slot : Slot) : Except LightClientError Nat :=
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

/-- Whether a new update is better than an old one, for a forced update.

More signers rank first, up to two thirds of the committee.

Then come, in order, a next committee for the attested period and a finalized header.

Then comes a finalized header in the attested period.

Then more signers, an earlier attested slot, and an earlier signature slot break the tie. -/
def isBetterUpdate (newUpdate oldUpdate : LightClientUpdate preset fork) : Bool := Id.run do
  let maxActive := preset.SYNC_COMMITTEE_SIZE.toNat
  let newActive := newUpdate.syncAggregate.participants
  let oldActive := oldUpdate.syncAggregate.participants
  let newSupermajority := newActive * 3 ≥ maxActive * 2
  let oldSupermajority := oldActive * 3 ≥ maxActive * 2
  if newSupermajority ≠ oldSupermajority then return newSupermajority
  if !newSupermajority ∧ newActive ≠ oldActive then return newActive > oldActive
  let period := computeSyncCommitteePeriodAtSlot preset
  let relevant (update : LightClientUpdate preset fork) : Bool :=
    update.isSyncCommitteeUpdate &&
      period update.attestedHeader.beacon.slot == period update.signatureSlot
  if relevant newUpdate ≠ relevant oldUpdate then return relevant newUpdate
  let newFinality := newUpdate.isFinalityUpdate
  if newFinality ≠ oldUpdate.isFinalityUpdate then return newFinality
  if newFinality then
    let committeeFinality (update : LightClientUpdate preset fork) : Bool :=
      period update.finalizedHeader.beacon.slot == period update.attestedHeader.beacon.slot
    if committeeFinality newUpdate ≠ committeeFinality oldUpdate then
      return committeeFinality newUpdate
  if newActive ≠ oldActive then return newActive > oldActive
  if newUpdate.attestedHeader.beacon.slot ≠ oldUpdate.attestedHeader.beacon.slot then
    return newUpdate.attestedHeader.beacon.slot < oldUpdate.attestedHeader.beacon.slot
  return newUpdate.signatureSlot < oldUpdate.signatureSlot

namespace LightClientStore

/-- Whether the store knows the next sync committee: its next committee is not all zero. -/
def isNextSyncCommitteeKnown (store : LightClientStore preset fork) : Bool :=
  store.nextSyncCommittee != SyncCommittee.empty preset

/-- Half of the most signers seen in the current or the previous period, rounded down. -/
def safetyThreshold (store : LightClientStore preset fork) : UInt64 :=
  max store.previousMaxActiveParticipants store.currentMaxActiveParticipants / 2

end LightClientStore

/-- The store of a light client that trusts a block, from a bootstrap for that block.

The bootstrap's header must be that block, and its branch must prove the committee. -/
def initializeLightClientStore (config : Config) (trustedBlockRoot : Root)
    (bootstrap : LightClientBootstrap preset fork) :
    Except LightClientError (LightClientStore preset fork) := do
  requireFork fork
  require (← isValidLightClientHeader config bootstrap.header) .invalidHeader
  require ((← liftRoot (SszType.hashTreeRoot bootstrap.header.beacon)) = trustedBlockRoot)
    .untrustedHeader
  let leaf ← liftRoot (SszType.hashTreeRoot bootstrap.currentSyncCommittee)
  let gindex ← currentSyncCommitteeGindexAtSlot (preset := preset) (fork := fork) config
    bootstrap.header.beacon.slot
  require (← liftRoot (isValidNormalizedMerkleBranch leaf
      bootstrap.currentSyncCommitteeBranch.toList gindex bootstrap.header.beacon.stateRoot))
    .invalidCurrentSyncCommitteeBranch
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

An update that proves no finalized header must carry the zero header.

So must an update whose finalized slot is the genesis slot, whose root is zero.

Otherwise its finalized header must be valid for the fork of its slot.

In each case, the finality branch must prove the root against the attested state root. -/
def validateFinality (config : Config) (update : LightClientUpdate preset fork) :
    Except LightClientError Unit := do
  if !update.isFinalityUpdate then
    require (sameSszValue update.finalizedHeader (LightClientHeader.empty preset fork))
      .unexpectedFinalizedHeader
  else
    let finalizedRoot ← if update.finalizedHeader.beacon.slot = GENESIS_SLOT then do
        require (sameSszValue update.finalizedHeader (LightClientHeader.empty preset fork))
          .unexpectedFinalizedHeader
        pure zeroBytes32
      else do
        require (← isValidLightClientHeader config update.finalizedHeader)
          .invalidHeader
        liftRoot (SszType.hashTreeRoot update.finalizedHeader.beacon)
    require (← liftRoot (isValidNormalizedMerkleBranch finalizedRoot update.finalityBranch.toList
        (← finalizedRootGindexAtSlot (preset := preset) (fork := fork) config
          update.attestedHeader.beacon.slot)
        update.attestedHeader.beacon.stateRoot))
      .invalidFinalityBranch

/-- The branch check of the next sync committee of an update, against the attested state root. -/
def validateNextSyncCommitteeBranch (config : Config) (update : LightClientUpdate preset fork) :
    Except LightClientError Unit := do
  let leaf ← liftRoot (SszType.hashTreeRoot update.nextSyncCommittee)
  require (← liftRoot (isValidNormalizedMerkleBranch leaf update.nextSyncCommitteeBranch.toList
      (← nextSyncCommitteeGindexAtSlot (preset := preset) (fork := fork) config
        update.attestedHeader.beacon.slot)
      update.attestedHeader.beacon.stateRoot))
    .invalidNextSyncCommitteeBranch

/-- The checks of an update against a store, at a slot of the local clock.

At least the minimum of members must sign it, in a period whose committee the store knows.

It must bring a newer header or the next committee.

A finality branch or a committee branch that is not all zero must reach the attested state root.

Otherwise the finalized header or the next committee must be zero.

The members must sign the attested header at the fork of the slot before the signature slot. -/
def validateLightClientUpdate (config : Config) (checks : SignatureChecks)
    (store : LightClientStore preset fork) (update : LightClientUpdate preset fork)
    (currentSlot : Slot) (genesisValidatorsRoot : Root) : Except LightClientError Unit := do
  requireFork fork
  let aggregate := update.syncAggregate
  require (aggregate.participants ≥ preset.MIN_SYNC_COMMITTEE_PARTICIPANTS.toNat)
    .tooFewParticipants
  require (← isValidLightClientHeader config update.attestedHeader) .invalidHeader
  let attestedSlot := update.attestedHeader.beacon.slot
  let finalizedSlot := update.finalizedHeader.beacon.slot
  require (currentSlot ≥ update.signatureSlot ∧ update.signatureSlot > attestedSlot ∧
    attestedSlot ≥ finalizedSlot) .slotsOutOfOrder
  let period := computeSyncCommitteePeriodAtSlot preset
  let storePeriod := period store.finalizedHeader.beacon.slot
  let signaturePeriod := period update.signatureSlot
  if store.isNextSyncCommitteeKnown then
    require (signaturePeriod = storePeriod ∨ signaturePeriod = storePeriod + 1)
      .unknownSignaturePeriod
  else
    require (signaturePeriod = storePeriod) .unknownSignaturePeriod
  let attestedPeriod := period attestedSlot
  let hasNextSyncCommittee := !store.isNextSyncCommitteeKnown &&
    (update.isSyncCommitteeUpdate && attestedPeriod == storePeriod)
  require (attestedSlot > store.finalizedHeader.beacon.slot ∨ hasNextSyncCommittee)
    .irrelevantUpdate
  validateFinality config update
  if !update.isSyncCommitteeUpdate then
    require (update.nextSyncCommittee = SyncCommittee.empty preset) .unexpectedNextSyncCommittee
  else
    if attestedPeriod = storePeriod ∧ store.isNextSyncCommitteeKnown then
      require (update.nextSyncCommittee = store.nextSyncCommittee) .conflictingNextSyncCommittee
    validateNextSyncCommitteeBranch config update
  let committee := if signaturePeriod = storePeriod then store.currentSyncCommittee
    else store.nextSyncCommittee
  let keys := committee.participantKeys aggregate
  let forkVersionSlot := if update.signatureSlot = 0 then 0 else update.signatureSlot - 1
  let forkVersion := config.computeForkVersion (computeEpochAtSlot preset forkVersionSlot)
  let domain ← liftRoot
    (computeDomain config DOMAIN_SYNC_COMMITTEE forkVersion genesisValidatorsRoot)
  let signingRoot ← liftRoot (computeSigningRoot update.attestedHeader.beacon domain)
  require (checks.fastAggregateVerify (keys.map packBytes) (packBytes signingRoot)
    (packBytes aggregate.syncCommitteeSignature) = true) .invalidSignature

/-- The store after it applies an update that it has checked.

At a new period, the next committee becomes the current one.

A newer finalized header replaces the finalized header.

It also replaces the optimistic header, if it is newer than that one. -/
def applyLightClientUpdate (store : LightClientStore preset fork)
    (update : LightClientUpdate preset fork) :
    Except LightClientError (LightClientStore preset fork) := do
  requireFork fork
  let period := computeSyncCommitteePeriodAtSlot preset
  let storePeriod := period store.finalizedHeader.beacon.slot
  let finalizedPeriod := period update.finalizedHeader.beacon.slot
  let store ← if !store.isNextSyncCommitteeKnown then do
      require (finalizedPeriod = storePeriod) .finalizedPeriodMismatch
      pure { store with nextSyncCommittee := update.nextSyncCommittee }
    else if finalizedPeriod = storePeriod + 1 then
      pure { store with
        currentSyncCommittee := store.nextSyncCommittee
        nextSyncCommittee := update.nextSyncCommittee
        previousMaxActiveParticipants := store.currentMaxActiveParticipants
        currentMaxActiveParticipants := 0 }
    else pure store
  if update.finalizedHeader.beacon.slot > store.finalizedHeader.beacon.slot then
    let store := { store with finalizedHeader := update.finalizedHeader }
    if store.finalizedHeader.beacon.slot > store.optimisticHeader.beacon.slot then
      return { store with optimisticHeader := store.finalizedHeader }
    return store
  return store

/-- The store after a forced update, when no finalized header came for a whole period.

The best update that the store kept is applied, and dropped.

The slot after which the update is forced is a 64-bit sum, which fails when it overflows.

If it finalizes nothing newer, its attested header stands for its finalized header. -/
def processLightClientStoreForceUpdate (store : LightClientStore preset fork)
    (currentSlot : Slot) : Except LightClientError (LightClientStore preset fork) := do
  requireFork fork
  let timeout := store.finalizedHeader.beacon.slot.toNat + preset.UPDATE_TIMEOUT.toNat
  require (timeout < 2 ^ 64) .slotOverflow
  match store.bestValidUpdate with
  | some best =>
    if currentSlot.toNat > timeout then
      let best := if best.finalizedHeader.beacon.slot ≤ store.finalizedHeader.beacon.slot then
        { best with finalizedHeader := best.attestedHeader }
      else best
      let store ← applyLightClientUpdate store best
      return { store with bestValidUpdate := none }
    else return store
  | none => return store

/-- The store after an update, which it checks first.

The update becomes the best update if it is better than the one that the store kept.

Its attested header becomes the optimistic header if more than the safety threshold signed.

With two thirds of the committee, the update is applied if it finalizes a newer header.

It is also applied if it proves the first next committee, in the period of its finalized header. -/
def processLightClientUpdate (config : Config) (checks : SignatureChecks)
    (store : LightClientStore preset fork) (update : LightClientUpdate preset fork)
    (currentSlot : Slot) (genesisValidatorsRoot : Root) :
    Except LightClientError (LightClientStore preset fork) := do
  validateLightClientUpdate config checks store update currentSlot genesisValidatorsRoot
  let active := update.syncAggregate.participants
  let store := match store.bestValidUpdate with
    | some best => if isBetterUpdate update best then { store with bestValidUpdate := update }
      else store
    | none => { store with bestValidUpdate := update }
  let store := { store with
    currentMaxActiveParticipants := max store.currentMaxActiveParticipants active.toUInt64 }
  let store := if active > store.safetyThreshold.toNat ∧
      update.attestedHeader.beacon.slot > store.optimisticHeader.beacon.slot then
    { store with optimisticHeader := update.attestedHeader }
  else store
  let period := computeSyncCommitteePeriodAtSlot preset
  let finalizedNextSyncCommittee := !store.isNextSyncCommitteeKnown &&
    update.isSyncCommitteeUpdate && update.isFinalityUpdate &&
    period update.finalizedHeader.beacon.slot == period update.attestedHeader.beacon.slot
  if active * 3 ≥ preset.SYNC_COMMITTEE_SIZE.toNat * 2 ∧
      (update.finalizedHeader.beacon.slot > store.finalizedHeader.beacon.slot ∨
        finalizedNextSyncCommittee) then
    let store ← applyLightClientUpdate store update
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
