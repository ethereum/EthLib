module

public import EthLib.Consensus.LightClient.FullNode

/-!
# `Consensus.LightClient.Upgrade`

A store of a light client can still read data of an earlier fork.

It upgrades that data to its own fork first, and the data on the network keeps its own form.

Capella gives a header an execution payload header and its branch.

A header of an earlier fork has none, so it gets the empty header and a branch of zeros.

Deneb adds two fields to the execution payload header, which an earlier header sets to zero.

Electra deepens the state by one level, so each branch into the state gets one more node.

That node is zero and comes first, which the check of a normalized branch accepts.

Gloas replaces the execution header by its block hash, and deepens the state again.

The branch of the block hash then starts with its proof inside the execution header.

The old branch from the execution payload up to the body root follows it.

Zero nodes in front bring that branch to the depth of the block hash in a Gloas body.

The upgrade to Gloas reads the fork of the header's slot, so it needs the configuration.

An upgrade across several forks applies each of these steps in turn.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

open LightClientError (liftRoot)

variable {preset : Preset}

/-- A branch with zero nodes in front, up to the depth of a generalized index.

A branch that already reaches that depth stays as it is. -/
def normalizeMerkleBranch (branch : List Bytes32) (gindex : Nat) : List Bytes32 :=
  List.replicate (Nat.log2 gindex - branch.length) zeroBytes32 ++ branch

/-- A branch of a depth, with zero nodes in front up to the depth of a deeper index. -/
def normalizeBranch {depth : Nat} (branch : Vector Bytes32 depth) (gindex : Nat)
    (deeper : depth ≤ Nat.log2 gindex) : Vector Bytes32 (Nat.log2 gindex) :=
  ⟨(normalizeMerkleBranch branch.toList gindex).toArray, by
    simp [normalizeMerkleBranch]
    omega⟩

/-- The execution payload header of a later fork, with the fields of an earlier one.

A field that the earlier fork does not have is zero. -/
def ExecutionPayloadHeader.upgrade {pre : Fork} (post : Fork)
    (header : ExecutionPayloadHeader preset pre) : ExecutionPayloadHeader preset post where
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
  withdrawalsRoot := fun _ =>
    if capella : .shapella ≤ pre then header.withdrawalsRoot capella else zeroBytes32
  blobGasUsed := fun _ => if deneb : .dencun ≤ pre then header.blobGasUsed deneb else 0
  excessBlobGas := fun _ => if deneb : .dencun ≤ pre then header.excessBlobGas deneb else 0

/-- A light client header of a later fork before Gloas, with the fields of an earlier one.

A header before Capella has no execution data, so it gets the empty header and zero nodes. -/
def LightClientHeader.upgradeFields {pre : Fork} (post : Fork) (before : pre < .glamsterdam)
    (postBefore : post < .glamsterdam) (header : LightClientHeader preset pre) :
    LightClientHeader preset post where
  beacon := header.beacon
  execution := fun _ =>
    if capella : .shapella ≤ pre then (header.execution ⟨capella, before⟩).upgrade post
    else ExecutionPayloadHeader.empty preset post
  executionBlockHash := fun _ => zeroBytes32
  executionBranch := fun _ =>
    if capella : .shapella ≤ pre then
      (header.executionBranch capella).cast (by
        have early : ¬Fork.glamsterdam ≤ pre := Nat.not_le_of_lt before
        have postEarly : ¬Fork.glamsterdam ≤ post := Nat.not_le_of_lt postBefore
        simp [executionBranchGindex, early, postEarly])
    else Vector.replicate _ zeroBytes32

/-- The Gloas header of an Electra header, whose execution header gives the block hash.

The empty header stays empty, and a header of a slot before Capella gets zero for both.

Otherwise the branch is the proof of the block hash in the execution header, then the old branch.

A header of a slot before Deneb proves the hash in the execution header of Capella. -/
def LightClientHeader.toGloas (config : Config) {post : Fork} (gloas : .glamsterdam ≤ post)
    (header : LightClientHeader preset .pectra) :
    Except LightClientError (LightClientHeader preset post) := do
  if sameSszValue header (LightClientHeader.empty preset .pectra) then
    return LightClientHeader.empty preset post
  let epoch := computeEpochAtSlot preset header.beacon.slot
  let execution := header.execution ⟨by decide, by decide⟩
  let withProof (proof : List Bytes32) : Except LightClientError (LightClientHeader preset post) :=
    do
    let branch ← branchVector _ (normalizeMerkleBranch
      (proof ++ (header.executionBranch (by decide)).toList) EXECUTION_BLOCK_HASH_GINDEX_GLOAS)
    return ⟨header.beacon, fun during => absurd gloas (Nat.not_le_of_lt during.2),
      fun _ => execution.blockHash, fun _ => branch⟩
  if config.DENEB_FORK_EPOCH ≤ epoch then
    withProof (← liftRoot (computeMerkleProof execution (payloadHeaderBlockHashGindex .pectra)))
  else if config.CAPELLA_FORK_EPOCH ≤ epoch then
    withProof (← liftRoot (computeMerkleProof (execution.toCapella (by decide))
      (payloadHeaderBlockHashGindex .shapella)))
  else
    return ⟨header.beacon, fun during => absurd gloas (Nat.not_le_of_lt during.2),
      fun _ => zeroBytes32, fun _ => Vector.replicate _ zeroBytes32⟩

/-- A light client header of a later fork, with the beacon header of an earlier one.

Before Gloas, the fields of the earlier fork carry over, and new ones are zero.

From Gloas, a header of an earlier fork goes through Electra, then gets its block hash. -/
def LightClientHeader.upgrade (config : Config) {pre : Fork} (post : Fork) (later : pre ≤ post)
    (header : LightClientHeader preset pre) :
    Except LightClientError (LightClientHeader preset post) :=
  if gloas : .glamsterdam ≤ pre then
    return {
      beacon := header.beacon
      execution := fun during => absurd (Nat.le_trans gloas later) (Nat.not_le_of_lt during.2)
      executionBlockHash := fun _ => header.executionBlockHash gloas
      executionBranch := fun _ => header.executionBranch (Nat.le_trans (by decide) gloas) |>.cast
        (by
          have postGloas : Fork.glamsterdam ≤ post := Nat.le_trans gloas later
          simp [executionBranchGindex, gloas, postGloas]) }
  else if postGloas : .glamsterdam ≤ post then
    (header.upgradeFields .pectra (Nat.lt_of_not_le gloas) (by decide)).toGloas config postGloas
  else return header.upgradeFields post (Nat.lt_of_not_le gloas) (Nat.lt_of_not_le postGloas)

section Depths

variable {pre post : Fork}

/-- An index chosen by the fork among three, for Altair, Electra and Gloas, is no shallower later.

This holds when the indices of Altair, Electra and Gloas grow no shallower in that order. -/
theorem log2_byStateFork_le {altair electra gloas : Nat}
    (first : Nat.log2 altair ≤ Nat.log2 electra) (second : Nat.log2 electra ≤ Nat.log2 gloas)
    (later : pre ≤ post) :
    Nat.log2 (if .glamsterdam ≤ pre then gloas else if .pectra ≤ pre then electra else altair) ≤
      Nat.log2 (if .glamsterdam ≤ post then gloas else if .pectra ≤ post then electra
        else altair) := by
  by_cases preGloas : Fork.glamsterdam ≤ pre
  · simp [preGloas, show Fork.glamsterdam ≤ post from Nat.le_trans preGloas later]
  by_cases preElectra : Fork.pectra ≤ pre
  · have postElectra : Fork.pectra ≤ post := Nat.le_trans preElectra later
    simp only [preGloas, preElectra, postElectra, ↓reduceIte]
    split <;> omega
  · simp only [preGloas, preElectra, ↓reduceIte]
    split
    · omega
    · split <;> omega

/-- A later fork proves the finalized root at least as deep. -/
theorem finalizedRootGindex_depth_le (later : pre ≤ post) :
    Nat.log2 (finalizedRootGindex pre) ≤ Nat.log2 (finalizedRootGindex post) :=
  log2_byStateFork_le (by decide) (by decide) later

/-- A later fork proves the current sync committee at least as deep. -/
theorem currentSyncCommitteeGindex_depth_le (later : pre ≤ post) :
    Nat.log2 (currentSyncCommitteeGindex pre) ≤ Nat.log2 (currentSyncCommitteeGindex post) :=
  log2_byStateFork_le (by decide) (by decide) later

/-- A later fork proves the next sync committee at least as deep. -/
theorem nextSyncCommitteeGindex_depth_le (later : pre ≤ post) :
    Nat.log2 (nextSyncCommitteeGindex pre) ≤ Nat.log2 (nextSyncCommitteeGindex post) :=
  log2_byStateFork_le (by decide) (by decide) later

end Depths

/-- A bootstrap of a later fork: its header upgraded, and its branch normalized. -/
def LightClientBootstrap.upgrade (config : Config) {pre : Fork} (post : Fork)
    (later : pre ≤ post) (bootstrap : LightClientBootstrap preset pre) :
    Except LightClientError (LightClientBootstrap preset post) := do
  return {
    header := ← bootstrap.header.upgrade config post later
    currentSyncCommittee := bootstrap.currentSyncCommittee
    currentSyncCommitteeBranch := normalizeBranch bootstrap.currentSyncCommitteeBranch _
      (currentSyncCommitteeGindex_depth_le later) }

/-- An update of a later fork: its headers upgraded, and its branches normalized. -/
def LightClientUpdate.upgrade (config : Config) {pre : Fork} (post : Fork) (later : pre ≤ post)
    (update : LightClientUpdate preset pre) :
    Except LightClientError (LightClientUpdate preset post) := do
  return {
    attestedHeader := ← update.attestedHeader.upgrade config post later
    nextSyncCommittee := update.nextSyncCommittee
    nextSyncCommitteeBranch := normalizeBranch update.nextSyncCommitteeBranch _
      (nextSyncCommitteeGindex_depth_le later)
    finalizedHeader := ← update.finalizedHeader.upgrade config post later
    finalityBranch := normalizeBranch update.finalityBranch _ (finalizedRootGindex_depth_le later)
    syncAggregate := update.syncAggregate
    signatureSlot := update.signatureSlot }

/-- A finality update of a later fork: its headers upgraded, and its branch normalized. -/
def LightClientFinalityUpdate.upgrade (config : Config) {pre : Fork} (post : Fork)
    (later : pre ≤ post) (update : LightClientFinalityUpdate preset pre) :
    Except LightClientError (LightClientFinalityUpdate preset post) := do
  return {
    attestedHeader := ← update.attestedHeader.upgrade config post later
    finalizedHeader := ← update.finalizedHeader.upgrade config post later
    finalityBranch := normalizeBranch update.finalityBranch _ (finalizedRootGindex_depth_le later)
    syncAggregate := update.syncAggregate
    signatureSlot := update.signatureSlot }

/-- An optimistic update of a later fork, with its header upgraded. -/
def LightClientOptimisticUpdate.upgrade (config : Config) {pre : Fork} (post : Fork)
    (later : pre ≤ post) (update : LightClientOptimisticUpdate preset pre) :
    Except LightClientError (LightClientOptimisticUpdate preset post) := do
  return {
    attestedHeader := ← update.attestedHeader.upgrade config post later
    syncAggregate := update.syncAggregate
    signatureSlot := update.signatureSlot }

/-- A store of a later fork: its headers and its best update upgraded. -/
def LightClientStore.upgrade (config : Config) {pre : Fork} (post : Fork) (later : pre ≤ post)
    (store : LightClientStore preset pre) :
    Except LightClientError (LightClientStore preset post) := do
  return {
    finalizedHeader := ← store.finalizedHeader.upgrade config post later
    currentSyncCommittee := store.currentSyncCommittee
    nextSyncCommittee := store.nextSyncCommittee
    bestValidUpdate := ← store.bestValidUpdate.mapM (·.upgrade config post later)
    optimisticHeader := ← store.optimisticHeader.upgrade config post later
    previousMaxActiveParticipants := store.previousMaxActiveParticipants
    currentMaxActiveParticipants := store.currentMaxActiveParticipants }

end EthLib.Consensus
