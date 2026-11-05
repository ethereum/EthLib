module

public import EthLib.Consensus.LightClient.Sync

/-!
# `Consensus.LightClient.Upgrade`

A store of a light client can still read data of an earlier fork.

It upgrades that data to its own fork first, and the data on the network keeps its own form.

Capella gives a header an execution payload header and its branch.

A header of an earlier fork has none, so it gets the empty header and a branch of zeros.

Deneb adds two fields to the execution payload header, which an earlier header sets to zero.

Electra deepens the state by one level, so each branch into the state gets one more node.

That node is zero and comes first, which the check of a normalized branch accepts.

An upgrade across several forks applies each of these steps in turn.

These upgrades hold from Altair to Fulu.

The upgrade to Gloas is not yet specified.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

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

/-- A light client header of a later fork, with the beacon header of an earlier one.

A header before Capella has no execution data, so it gets the empty header and zero nodes. -/
def LightClientHeader.upgrade {pre : Fork} (post : Fork) (header : LightClientHeader preset pre) :
    LightClientHeader preset post where
  beacon := header.beacon
  execution := fun _ =>
    if capella : .shapella ≤ pre then (header.execution capella).upgrade post
    else ExecutionPayloadHeader.empty preset post
  executionBranch := fun _ =>
    if capella : .shapella ≤ pre then header.executionBranch capella
    else Vector.replicate _ zeroBytes32

section Depths

variable {pre post : Fork}

/-- A later fork proves the finalized root at least as deep. -/
theorem finalizedRootGindex_depth_le (later : pre ≤ post) :
    Nat.log2 (finalizedRootGindex pre) ≤ Nat.log2 (finalizedRootGindex post) := by
  unfold finalizedRootGindex
  by_cases electra : Fork.pectra ≤ pre
  · simp [electra, show Fork.pectra ≤ post from Nat.le_trans electra later]
  · simp only [electra, ↓reduceIte]
    split <;> decide

/-- A later fork proves the current sync committee at least as deep. -/
theorem currentSyncCommitteeGindex_depth_le (later : pre ≤ post) :
    Nat.log2 (currentSyncCommitteeGindex pre) ≤ Nat.log2 (currentSyncCommitteeGindex post) := by
  unfold currentSyncCommitteeGindex
  by_cases electra : Fork.pectra ≤ pre
  · simp [electra, show Fork.pectra ≤ post from Nat.le_trans electra later]
  · simp only [electra, ↓reduceIte]
    split <;> decide

/-- A later fork proves the next sync committee at least as deep. -/
theorem nextSyncCommitteeGindex_depth_le (later : pre ≤ post) :
    Nat.log2 (nextSyncCommitteeGindex pre) ≤ Nat.log2 (nextSyncCommitteeGindex post) := by
  unfold nextSyncCommitteeGindex
  by_cases electra : Fork.pectra ≤ pre
  · simp [electra, show Fork.pectra ≤ post from Nat.le_trans electra later]
  · simp only [electra, ↓reduceIte]
    split <;> decide

end Depths

/-- A bootstrap of a later fork: its header upgraded, and its branch normalized. -/
def LightClientBootstrap.upgrade {pre : Fork} (post : Fork) (later : pre ≤ post)
    (bootstrap : LightClientBootstrap preset pre) : LightClientBootstrap preset post where
  header := bootstrap.header.upgrade post
  currentSyncCommittee := bootstrap.currentSyncCommittee
  currentSyncCommitteeBranch := normalizeBranch bootstrap.currentSyncCommitteeBranch _
    (currentSyncCommitteeGindex_depth_le later)

/-- An update of a later fork: its headers upgraded, and its branches normalized. -/
def LightClientUpdate.upgrade {pre : Fork} (post : Fork) (later : pre ≤ post)
    (update : LightClientUpdate preset pre) : LightClientUpdate preset post where
  attestedHeader := update.attestedHeader.upgrade post
  nextSyncCommittee := update.nextSyncCommittee
  nextSyncCommitteeBranch := normalizeBranch update.nextSyncCommitteeBranch _
    (nextSyncCommitteeGindex_depth_le later)
  finalizedHeader := update.finalizedHeader.upgrade post
  finalityBranch := normalizeBranch update.finalityBranch _ (finalizedRootGindex_depth_le later)
  syncAggregate := update.syncAggregate
  signatureSlot := update.signatureSlot

/-- A finality update of a later fork: its headers upgraded, and its branch normalized. -/
def LightClientFinalityUpdate.upgrade {pre : Fork} (post : Fork) (later : pre ≤ post)
    (update : LightClientFinalityUpdate preset pre) : LightClientFinalityUpdate preset post where
  attestedHeader := update.attestedHeader.upgrade post
  finalizedHeader := update.finalizedHeader.upgrade post
  finalityBranch := normalizeBranch update.finalityBranch _ (finalizedRootGindex_depth_le later)
  syncAggregate := update.syncAggregate
  signatureSlot := update.signatureSlot

/-- An optimistic update of a later fork, with its header upgraded. -/
def LightClientOptimisticUpdate.upgrade {pre : Fork} (post : Fork)
    (update : LightClientOptimisticUpdate preset pre) :
    LightClientOptimisticUpdate preset post where
  attestedHeader := update.attestedHeader.upgrade post
  syncAggregate := update.syncAggregate
  signatureSlot := update.signatureSlot

/-- A store of a later fork: its headers and its best update upgraded. -/
def LightClientStore.upgrade {pre : Fork} (post : Fork) (later : pre ≤ post)
    (store : LightClientStore preset pre) : LightClientStore preset post where
  finalizedHeader := store.finalizedHeader.upgrade post
  currentSyncCommittee := store.currentSyncCommittee
  nextSyncCommittee := store.nextSyncCommittee
  bestValidUpdate := store.bestValidUpdate.map (·.upgrade post later)
  optimisticHeader := store.optimisticHeader.upgrade post
  previousMaxActiveParticipants := store.previousMaxActiveParticipants
  currentMaxActiveParticipants := store.currentMaxActiveParticipants

end EthLib.Consensus
