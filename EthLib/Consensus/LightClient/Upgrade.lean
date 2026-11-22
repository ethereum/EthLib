module

public import EthLib.Consensus.LightClient.Branch

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
  -- Let `d = floor(log2(g))` be the depth of the index `g`, and `n` the length of the branch.
  --
  -- The result is `max(d - n, 0)` zero nodes, then the branch.
  List.replicate (Nat.log2 gindex - branch.length) zeroBytes32 ++ branch

/-- A branch of a depth, with zero nodes in front up to the depth of a deeper index. -/
def normalizeBranch {depth : Nat} (branch : Vector Bytes32 depth) (gindex : Nat)
    (deeper : depth ≤ Nat.log2 gindex) : Vector Bytes32 (Nat.log2 gindex) :=
  -- The branch with zero nodes in front, of length exactly the depth of the index.
  ⟨(normalizeMerkleBranch branch.toList gindex).toArray, by
    simp [normalizeMerkleBranch]
    omega⟩

/-- A light client header of a later fork before Gloas, with the fields of an earlier one.

A header before Capella has no execution data, so it gets the empty header and zero nodes. -/
def LightClientHeader.upgradeFields {pre : Fork} (post : Fork) (before : pre < .glamsterdam)
    (postBefore : post < .glamsterdam) (header : LightClientHeader preset pre) :
    LightClientHeader preset post where
  -- The beacon header carries over.
  beacon := header.beacon
  -- From Capella, the execution header carries over, with 0 in each field that it lacks.
  --
  -- Before Capella, it is the empty execution header.
  execution := fun _ =>
    if capella : .shapella ≤ pre then (header.execution ⟨capella, before⟩).upgrade post
    else ExecutionPayloadHeader.empty preset post
  -- The block hash exists only from Gloas, and the later fork is before Gloas.
  executionBlockHash := fun _ => zeroBytes32
  -- From Capella, the branch carries over, since the body keeps its depth up to Fulu.
  --
  -- Before Capella, it is all zeros.
  executionBranch := fun _ =>
    if capella : .shapella ≤ pre then
      (header.executionBranch capella).cast (by
        have early : ¬Fork.glamsterdam ≤ pre := Nat.not_le_of_lt before
        have postEarly : ¬Fork.glamsterdam ≤ post := Nat.not_le_of_lt postBefore
        simp [executionBranchGindex, early, postEarly])
    else Vector.replicate _ zeroBytes32

/-- The Gloas header of an Electra header, whose execution header gives the block hash. -/
def LightClientHeader.toGloas (config : Config) {post : Fork} (gloas : .glamsterdam ≤ post)
    (header : LightClientHeader preset .pectra) :
    Except LightClientError (LightClientHeader preset post) := do
  -- The empty header gives the empty header.
  if sameSszValue header (LightClientHeader.empty preset .pectra) then
    return LightClientHeader.empty preset post
  -- Let `e` be the epoch of the slot of the beacon header.
  let epoch := computeEpochAtSlot preset header.beacon.slot
  let execution := header.execution ⟨by decide, by decide⟩
  -- The block hash comes from the execution header.
  --
  -- Its branch is the proof of the block hash in the execution header, then the old branch.
  --
  -- Zero nodes in front bring it to the depth of `EXECUTION_BLOCK_HASH_GINDEX_GLOAS`.
  let withProof (proof : List Bytes32) : Except LightClientError (LightClientHeader preset post) :=
    do
    let branch ← branchVector _ (normalizeMerkleBranch
      (proof ++ (header.executionBranch (by decide)).toList) EXECUTION_BLOCK_HASH_GINDEX_GLOAS)
    return ⟨header.beacon, fun during => absurd gloas (Nat.not_le_of_lt during.2),
      fun _ => execution.blockHash, fun _ => branch⟩
  -- For `DENEB_FORK_EPOCH ≤ e`, the proof is at generalized index 44 of the execution header.
  if config.DENEB_FORK_EPOCH ≤ epoch then
    withProof (← liftRoot (computeMerkleProof execution (payloadHeaderBlockHashGindex .pectra)))
  -- For `CAPELLA_FORK_EPOCH ≤ e < DENEB_FORK_EPOCH`, the old branch proves a header of Capella.
  --
  -- The proof is then at generalized index 28 of that header in the form of Capella.
  else if config.CAPELLA_FORK_EPOCH ≤ epoch then
    withProof (← liftRoot (computeMerkleProof (execution.toCapella (by decide))
      (payloadHeaderBlockHashGindex .shapella)))
  else
    -- For `e < CAPELLA_FORK_EPOCH`, the block hash and every node of the branch are zero.
    return ⟨header.beacon, fun during => absurd gloas (Nat.not_le_of_lt during.2),
      fun _ => zeroBytes32, fun _ => Vector.replicate _ zeroBytes32⟩

/-- A light client header of a later fork, with the beacon header of an earlier one. -/
def LightClientHeader.upgrade (config : Config) {pre : Fork} (post : Fork) (later : pre ≤ post)
    (header : LightClientHeader preset pre) :
    Except LightClientError (LightClientHeader preset post) :=
  -- A header from Gloas carries over: its beacon header, its block hash and its branch.
  if gloas : .glamsterdam ≤ pre then
    return {
      beacon := header.beacon
      execution := fun during => absurd (Nat.le_trans gloas later) (Nat.not_le_of_lt during.2)
      executionBlockHash := fun _ => header.executionBlockHash gloas
      executionBranch := fun _ => header.executionBranch (Nat.le_trans (by decide) gloas) |>.cast
        (by
          have postGloas : Fork.glamsterdam ≤ post := Nat.le_trans gloas later
          simp [executionBranchGindex, gloas, postGloas]) }
  -- To a fork from Gloas, an earlier header is brought to Electra first.
  --
  -- It then gets its block hash and the branch of that hash.
  else if postGloas : .glamsterdam ≤ post then
    (header.upgradeFields .pectra (Nat.lt_of_not_le gloas) (by decide)).toGloas config postGloas
  -- Before Gloas, the fields of the earlier fork carry over, and the new ones are zero.
  --
  -- The rule upgrades one fork at a time, and this is one step to the later fork.
  --
  -- Each step carries the fields over and zeroes the new ones, so one step gives the same header.
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
  -- The header is upgraded, and the current sync committee carries over.
  --
  -- Its branch gets zero nodes in front, up to the depth of its index at the later fork.
  --
  -- The rule adds those nodes one fork at a time, which gives the same branch.
  return {
    header := ← bootstrap.header.upgrade config post later
    currentSyncCommittee := bootstrap.currentSyncCommittee
    currentSyncCommitteeBranch := normalizeBranch bootstrap.currentSyncCommitteeBranch _
      (currentSyncCommitteeGindex_depth_le later) }

/-- An update of a later fork: its headers upgraded, and its branches normalized. -/
def LightClientUpdate.upgrade (config : Config) {pre : Fork} (post : Fork) (later : pre ≤ post)
    (update : LightClientUpdate preset pre) :
    Except LightClientError (LightClientUpdate preset post) := do
  -- The headers are upgraded.
  --
  -- The next sync committee, the sync aggregate and the signature slot carry over.
  --
  -- Each branch gets zero nodes in front, up to the depth of its index at the later fork.
  --
  -- The rule adds those nodes one fork at a time, which gives the same branches.
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
  -- The headers are upgraded, and the sync aggregate and the signature slot carry over.
  --
  -- The branch gets zero nodes in front, up to the depth of the index of the finalized root.
  --
  -- The rule adds those nodes one fork at a time, which gives the same branch.
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
  -- The attested header is upgraded, and the sync aggregate and the signature slot carry over.
  return {
    attestedHeader := ← update.attestedHeader.upgrade config post later
    syncAggregate := update.syncAggregate
    signatureSlot := update.signatureSlot }

/-- A store of a later fork: its headers and its best update upgraded. -/
def LightClientStore.upgrade (config : Config) {pre : Fork} (post : Fork) (later : pre ≤ post)
    (store : LightClientStore preset pre) :
    Except LightClientError (LightClientStore preset post) := do
  -- The finalized header, the best valid update and the optimistic header are upgraded.
  --
  -- An absent best valid update stays absent.
  --
  -- The sync committees and the counts of active participants carry over.
  return {
    finalizedHeader := ← store.finalizedHeader.upgrade config post later
    currentSyncCommittee := store.currentSyncCommittee
    nextSyncCommittee := store.nextSyncCommittee
    bestValidUpdate := ← store.bestValidUpdate.mapM (·.upgrade config post later)
    optimisticHeader := ← store.optimisticHeader.upgrade config post later
    previousMaxActiveParticipants := store.previousMaxActiveParticipants
    currentMaxActiveParticipants := store.currentMaxActiveParticipants }

end EthLib.Consensus
