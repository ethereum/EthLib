module

public import EthLib.Consensus.BeaconApi.LightClient
public import EthLib.Consensus.Proofs.Containers.Block
public import EthLib.Consensus.Proofs.Containers.State
public import EthLib.Consensus.Proofs.LightClient.Authenticate
public import EthLib.Consensus.Proofs.LightClient.Execution
public import EthLib.Consensus.Proofs.LightClient.FullNode
public import EthLib.Consensus.Proofs.LightClient.Upgrade

/-!
# Proofs: the bootstrap answer of the Beacon API

A bootstrap that the node serves for a block starts a light client that trusts that block.

The store must hold the block under its root, and the state that the block names by its root.

The schedule must put the forks in order.

The sizes of the preset that the block and the state hold must be nonzero.

The state type must be lawful.

The answer itself refuses a block of another fork than the fork of its slot.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- A fork that the schedule gives at an epoch has started by that epoch.

This holds for Capella, Deneb and Gloas, on a schedule in fork order. -/
theorem forkAtEpoch_started {config : Config} {epoch : Epoch}
    (scheduled : config.forkAtEpoch epoch = fork)
    (ordered : config.CAPELLA_FORK_EPOCH ≤ config.DENEB_FORK_EPOCH ∧
      config.DENEB_FORK_EPOCH ≤ config.ELECTRA_FORK_EPOCH ∧
      config.ELECTRA_FORK_EPOCH ≤ config.FULU_FORK_EPOCH ∧
      config.FULU_FORK_EPOCH ≤ config.GLOAS_FORK_EPOCH ∧
      config.GLOAS_FORK_EPOCH ≤ config.HEZE_FORK_EPOCH) :
    (.glamsterdam ≤ fork → config.GLOAS_FORK_EPOCH ≤ epoch) ∧
      (.dencun ≤ fork → config.DENEB_FORK_EPOCH ≤ epoch) ∧
      (.shapella ≤ fork → config.CAPELLA_FORK_EPOCH ≤ epoch) := by
  unfold Config.forkAtEpoch at scheduled
  have order : ∀ a b : Fork, (a ≤ b) = (a.ctorIdx ≤ b.ctorIdx) := fun _ _ => rfl
  split_ifs at scheduled <;> subst scheduled <;>
    simp only [order, Fork.ctorIdx, UInt64.le_iff_toNat_le, Nat.not_le] at * <;>
    omega

/-- A branch that a full node builds for a node below the root has one node per level. -/
theorem computeMerkleProof_length {α : Type} [SszType α] (value : α) {gindex : Nat}
    (named : 2 ≤ gindex) {proof : List Bytes32}
    (built : computeMerkleProof value gindex = .ok proof) : proof.length = Nat.log2 gindex := by
  have positive : Nat.log2 gindex ≠ 0 := Nat.ne_of_gt (log2_pos named)
  have measured : gindexLength gindex = .ok (Nat.log2 gindex) := by
    have indexed : ¬gindex < 1 := by omega
    simp [gindexLength, gindexDepth, indexed, positive, bind, Except.bind]
  simp only [computeMerkleProof, buildProof, getBranchIndices, getPathIndices, measured,
    bind_ok_iff, pure, Except.pure, Except.ok.injEq, exists_eq_left'] at built
  obtain ⟨nodes, read, chunked⟩ := built
  rw [Base.mapM_ok_length chunked, Base.mapM_ok_length read]
  simp

/-- A value stored with its root has the root of the bare value. -/
theorem hashTreeRoot_rooted {α : Type} [SszType α] (rooted : Rooted α) :
    SszType.hashTreeRoot rooted = SszType.hashTreeRoot rooted.value := by
  simp only [SszType.hashTreeRoot]
  rw [show SszType.root rooted = SszType.root rooted.value from rooted.built]

/-- The header of a block is valid for the fork of its slot, when the schedule gives that fork.

The schedule must put the forks from Capella to Heze in order. -/
theorem blockToLightClientHeader_valid [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat]
    [NeZero preset.PTC_SIZE.toNat] [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]
    {config : Config} {block : SignedBeaconBlock preset fork}
    {header : LightClientHeader preset fork}
    (made : blockToLightClientHeader config block = .ok header)
    (scheduled : config.forkAtEpoch (computeEpochAtSlot preset block.message.slot) = fork)
    (ordered : config.CAPELLA_FORK_EPOCH ≤ config.DENEB_FORK_EPOCH ∧
      config.DENEB_FORK_EPOCH ≤ config.ELECTRA_FORK_EPOCH ∧
      config.ELECTRA_FORK_EPOCH ≤ config.FULU_FORK_EPOCH ∧
      config.FULU_FORK_EPOCH ≤ config.GLOAS_FORK_EPOCH ∧
      config.GLOAS_FORK_EPOCH ≤ config.HEZE_FORK_EPOCH) :
    isValidLightClientHeader config header = .ok true := by
  obtain ⟨gloasStarted, denebStarted, capellaStarted⟩ := forkAtEpoch_started scheduled ordered
  unfold blockToLightClientHeader at made
  obtain ⟨⟨altair⟩, -, rest⟩ := bind_ok_iff.mp made
  obtain ⟨bodyRoot, bodyRooted, rest⟩ := bind_ok_iff.mp rest
  replace bodyRooted := LightClientError.liftRoot_ok.mp bodyRooted
  clear made
  by_cases gloas : Fork.glamsterdam ≤ fork
  · rw [dite_eq_left gloas] at rest
    obtain ⟨proof, proved, rest⟩ := bind_ok_iff.mp rest
    obtain ⟨branch, fits, rest⟩ := bind_ok_iff.mp rest
    cases rest
    replace proved := LightClientError.liftRoot_ok.mp proved
    obtain ⟨root', proof', rooted', proved', valid⟩ :=
      computeMerkleProof_isValidNormalizedMerkleBranch block.message.body (by decide)
        (BeaconBlockBody.nodeRoot_parentBlockHash gloas block.message.body)
    rw [bodyRooted, Except.ok.injEq] at rooted'
    rw [proved, Except.ok.injEq] at proved'
    subst rooted' proved'
    unfold isValidLightClientHeader
    simp only [LightClientError.requireFork, altair, ↓reduceIte, gloas, dite_true,
      gloasStarted gloas, branchVector_toList fits, valid, bind, Except.bind,
      LightClientError.liftRoot, Except.mapError]
  · rw [dite_eq_right gloas] at rest
    by_cases capella : Fork.shapella ≤ fork
    · rw [dite_eq_right (not_not.mpr capella)] at rest
      have started := capellaStarted capella
      rw [ite_eq_right (UInt64.not_lt.mpr started)] at rest
      obtain ⟨payloadHeader, made, rest⟩ := bind_ok_iff.mp rest
      obtain ⟨proof, proved, rest⟩ := bind_ok_iff.mp rest
      obtain ⟨branch, fits, rest⟩ := bind_ok_iff.mp rest
      cases rest
      clear rest
      have before : fork < .glamsterdam := Nat.lt_of_not_le gloas
      replace made := LightClientError.liftRoot_ok.mp made
      replace proved := LightClientError.liftRoot_ok.mp proved
      -- Before Deneb the fork is Capella, which has no blob gas fields to clear.
      have same : (if computeEpochAtSlot preset block.message.slot < config.DENEB_FORK_EPOCH then
          { payloadHeader with blobGasUsed := fun _ => 0, excessBlobGas := fun _ => 0 }
        else payloadHeader) = payloadHeader := by
        by_cases deneb : Fork.dencun ≤ fork
        · exact ite_eq_right (UInt64.not_lt.mpr (denebStarted deneb))
        · split
          · congr 1 <;> funext later <;> exact absurd later deneb
          · rfl
      simp only [same]
      obtain ⟨payloadRoot, payloadRooted⟩ := SszType.hashTreeRoot_total
        (block.message.body.executionPayload ⟨Nat.le_trans (by decide) capella, before⟩)
      obtain ⟨root', proof', rooted', built, climbs⟩ :=
        SszType.buildProof_isValidMerkleBranch block.message.body (by decide)
          (BeaconBlockBody.nodeRoot_executionPayload capella before block.message.body
            payloadRooted)
      rw [bodyRooted, Except.ok.injEq] at rooted'
      subst rooted'
      have proved' : computeMerkleProof block.message.body EXECUTION_PAYLOAD_GINDEX =
          .ok proof' := by
        simp only [computeMerkleProof, built, bind, Except.bind]
        exact mapM_toChunk_map_toArray proof'
      rw [proved, Except.ok.injEq] at proved'
      subst proved'
      obtain ⟨leaf, leafRooted, executionRoot⟩ := getLcExecutionRoot_execution (config := config)
        (header := ⟨⟨block.message.slot, block.message.proposerIndex, block.message.parentRoot,
          block.message.stateRoot, bodyRoot⟩, fun _ => payloadHeader,
          fun later => absurd later gloas, fun _ => branch⟩) capella before started denebStarted
      have leafEq : leaf = payloadRoot := by
        have := (ExecutionPayload.hashTreeRoot_header before made).symm.trans leafRooted
        rw [payloadRooted, Except.ok.injEq] at this
        exact this.symm
      subst leafEq
      have below : getSubtreeIndex EXECUTION_PAYLOAD_GINDEX =
          .ok (EXECUTION_PAYLOAD_GINDEX % 2 ^ Nat.log2 EXECUTION_PAYLOAD_GINDEX) := by
        simp [getSubtreeIndex, gindexDepth, gindexBelow, EXECUTION_PAYLOAD_GINDEX, bind,
          Except.bind, pure, Except.pure]
      unfold isValidLightClientHeader
      rw [executionRoot]
      simp only [LightClientError.requireFork, altair, ↓reduceIte, gloas, capella, dite_false,
        dite_true, UInt64.not_lt.mpr started, below, bind, Except.bind, pure, Except.pure,
        LightClientError.liftRoot, Except.mapError, branchVector_toList fits]
      split_ifs with deneb early
      · exact absurd early.1 (UInt64.not_lt.mpr (denebStarted deneb))
      · simp [climbs]
      · simp [climbs]
    · rw [dite_eq_left capella] at rest
      cases rest
      unfold isValidLightClientHeader
      simp [LightClientError.requireFork, altair, gloas, capella]

/-- The beacon header of the light client header of a block is the header of that block.

Its body root is the root of the body of the block. -/
theorem blockToLightClientHeader_beacon {config : Config} {block : SignedBeaconBlock preset fork}
    {header : LightClientHeader preset fork}
    (made : blockToLightClientHeader config block = .ok header) :
    ∃ bodyRoot, SszType.hashTreeRoot block.message.body = .ok bodyRoot ∧
      header.beacon = ⟨block.message.slot, block.message.proposerIndex, block.message.parentRoot,
        block.message.stateRoot, bodyRoot⟩ := by
  unfold blockToLightClientHeader at made
  obtain ⟨_, -, rest⟩ := bind_ok_iff.mp made
  obtain ⟨bodyRoot, bodyRooted, rest⟩ := bind_ok_iff.mp rest
  refine ⟨bodyRoot, LightClientError.liftRoot_ok.mp bodyRooted, ?_⟩
  clear made
  -- Every branch keeps the beacon header that it built first.
  split_ifs at rest <;>
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest <;>
    first
    | (obtain rfl := rest; rfl)
    | (obtain ⟨_, -, _, -, rfl⟩ := rest; rfl)
    | (obtain ⟨_, -, _, -, _, -, rfl⟩ := rest; rfl)

/-- Two layouts of the state whose current sync committee indices have one depth have one index.

The depth of that index differs between the layouts of the state. -/
theorem currentSyncCommitteeGindex_eq_of_log2 {a b : Fork}
    (same : Nat.log2 (currentSyncCommitteeGindex a) = Nat.log2 (currentSyncCommitteeGindex b)) :
    currentSyncCommitteeGindex a = currentSyncCommitteeGindex b := by
  have altair : Nat.log2 54 = 5 := by decide +kernel
  have electra : Nat.log2 86 = 6 := by decide +kernel
  have gloas : Nat.log2 2945 = 11 := by decide +kernel
  unfold currentSyncCommitteeGindex at *
  split_ifs at * <;> simp_all

/-- A bootstrap that the node serves for a block starts a light client that trusts that block.

The store holds the block under its root, and the post state under the same root.

The block gives the root of that state, as the store checks when it takes the block.

The schedule puts the forks from Capella to Heze in order.

The state type is lawful, and the sizes of the preset that the block and state hold are nonzero. -/
theorem bootstrapFor_valid [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat]
    [NeZero preset.PTC_SIZE.toNat] [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]
    [LawfulSszType (BeaconState preset fork)] {config : Config}
    {store : Store preset fork} {root : Root} {block : BeaconBlock preset fork}
    {state : BeaconState preset fork} {bootstrap : LightClientBootstrap preset fork}
    (held : store.blocks[root]? = some block) (heldState : store.blockStates[root]? = some state)
    (rooted : SszType.hashTreeRoot block = .ok root)
    (stated : SszType.hashTreeRoot state = .ok block.stateRoot)
    (ordered : config.CAPELLA_FORK_EPOCH ≤ config.DENEB_FORK_EPOCH ∧
      config.DENEB_FORK_EPOCH ≤ config.ELECTRA_FORK_EPOCH ∧
      config.ELECTRA_FORK_EPOCH ≤ config.FULU_FORK_EPOCH ∧
      config.FULU_FORK_EPOCH ≤ config.GLOAS_FORK_EPOCH ∧
      config.GLOAS_FORK_EPOCH ≤ config.HEZE_FORK_EPOCH)
    (served : bootstrapFor config store root = .ok bootstrap) :
    ∃ lightClient, initializeLightClientStore config root bootstrap = .ok lightClient := by
  unfold bootstrapFor at served
  simp only [held, heldState] at served
  -- The node serves only a block of the fork that the schedule gives at its slot.
  have scheduled : config.forkAtEpoch (computeEpochAtSlot preset block.slot) = fork := by
    by_contra other
    simp [other] at served
  rw [ite_eq_right (not_not.mpr scheduled)] at served
  have created : createLightClientBootstrap config state ⟨block, Vector.replicate 96 0⟩ =
      .ok bootstrap := by
    revert served
    cases createLightClientBootstrap config state ⟨block, Vector.replicate 96 0⟩ <;>
      simp [Except.mapError]
  clear served
  unfold createLightClientBootstrap at created
  simp only [bind_ok_iff] at created
  obtain ⟨⟨altair⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, gindex, indexed, header, madeHeader,
    proof, proved, branch, fits, built⟩ := created
  cases built
  replace proved := LightClientError.liftRoot_ok.mp proved
  -- The header is valid and has the root of the block.
  have valid := blockToLightClientHeader_valid madeHeader scheduled ordered
  obtain ⟨bodyRoot, bodyRooted, beacon⟩ := blockToLightClientHeader_beacon madeHeader
  have trusted : SszType.hashTreeRoot header.beacon = .ok root := by
    rw [beacon]
    exact (BeaconBlock.hashTreeRoot_header bodyRooted).trans rooted
  -- The client reads the committee at the index of the fork of the block.
  have layout : currentSyncCommitteeGindexAtSlot (preset := preset) (fork := fork) config
      header.beacon.slot = .ok (currentSyncCommitteeGindex fork) := by
    rw [beacon]
    exact (stateForkAtSlot_gindices altair (Nat.le_refl _) scheduled ordered.2.2.1
      ordered.2.2.2.2).2.1
  -- The node built the branch at an index of the same depth, so at that same index.
  have sameIndex : gindex = currentSyncCommitteeGindex fork := by
    have long := computeMerkleProof_length state (currentSyncCommitteeGindexAtSlot_named indexed)
      proved
    rw [← branchVector_toList fits, Vector.length_toList] at long
    unfold currentSyncCommitteeGindexAtSlot at indexed
    cases forked : stateForkAtSlot (preset := preset) (fork := fork) config state.slot with
    | error => simp [forked, Functor.map, Except.map] at indexed
    | ok layoutFork =>
      simp only [forked, Functor.map, Except.map, Except.ok.injEq] at indexed
      subst indexed
      exact currentSyncCommitteeGindex_eq_of_log2 long.symm
  subst sameIndex
  obtain ⟨node, nodeRooted⟩ := SszType.hashTreeRoot_total (state.currentSyncCommittee altair)
  obtain ⟨stateRoot, proof', stateRooted, proved', climbs⟩ :=
    computeMerkleProof_isValidNormalizedMerkleBranch state
      (currentSyncCommitteeGindexAtSlot_named layout)
      (BeaconState.nodeRoot_currentSyncCommittee altair state nodeRooted)
  rw [stated, Except.ok.injEq] at stateRooted
  rw [proved, Except.ok.injEq] at proved'
  subst stateRooted proved'
  rw [hashTreeRoot_rooted] at nodeRooted
  have stateRoot : header.beacon.stateRoot = block.stateRoot := by rw [beacon]
  unfold initializeLightClientStore
  simp only [LightClientError.requireFork, altair, ↓reduceIte, valid, trusted, nodeRooted, layout,
    stateRoot, branchVector_toList fits, climbs, LightClientError.liftRoot, Except.mapError,
    LightClientError.require, bind, Except.bind, pure, Except.pure]
  exact ⟨_, rfl⟩

end EthLib.Consensus.BeaconApi
