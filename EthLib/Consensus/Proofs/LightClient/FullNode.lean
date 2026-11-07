module

public import EthLib.Consensus.LightClient.FullNode
public import EthLib.Consensus.LightClient.Upgrade
public import EthLib.Consensus.Proofs.LightClient.Sync
public import EthLib.Serialization.Proofs.Ssz.Typed.Gindex

/-!
# Proofs: the light client data of a full node, and its upgrades

A full node proves a node of a value by the branch that it builds for it.

A light client accepts that branch for the node's generalized index and the root of the value.

An upgrade puts zero nodes in front of a branch.

The check of a normalized branch reads those nodes as the zero front, so it gives the same verdict.

A bootstrap exists only for a state at the slot of its block.

An update has the slot of its block and enough participants.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

/-- Nodes that are the bytes of 32-byte vectors convert back to those vectors. -/
theorem mapM_toChunk_map_toArray :
    ∀ chunks : List Bytes32, (chunks.map Vector.toArray).mapM toChunk = .ok chunks
  | [] => rfl
  | chunk :: rest => by
    simp [List.mapM_cons, toChunk, mapM_toChunk_map_toArray rest, bind, Except.bind, pure,
      Except.pure]

/-- A branch that a full node builds for a node of a value proves that node.

The node is read at a generalized index of at least two, and the root is the root of the value.

The check of a normalized branch accepts the branch at that index and against that root. -/
theorem computeMerkleProof_isValidNormalizedMerkleBranch {α : Type} [SszType α]
    [LawfulSszType α] (value : α) {gindex : Nat} (named : 2 ≤ gindex) {leaf : Bytes32}
    (read : nodeRoot (SszType.desc α) (SszType.toValue value) gindex = .ok leaf.toArray) :
    ∃ root branch, SszType.hashTreeRoot value = .ok root ∧
      computeMerkleProof value gindex = .ok branch ∧
      isValidNormalizedMerkleBranch leaf branch gindex root = .ok true := by
  obtain ⟨root, branch, rooted, built, valid⟩ :=
    SszType.buildProof_isValidMerkleBranch value named read
  refine ⟨root, branch, rooted, ?_, ?_⟩
  · simp only [computeMerkleProof, built, bind, Except.bind]
    exact mapM_toChunk_map_toArray branch
  · -- The branch has exactly the depth of the index, so no node is in front.
    have counted := (isValidMerkleBranch_eq_true_iff.mp valid).1
    rw [isValidNormalizedMerkleBranch_iff named, counted, Nat.sub_self, List.drop_zero]
    refine ⟨by simp, ?_⟩
    rw [← two_pow_log2_add_mod (by omega : 1 ≤ gindex)]
    exact (isValidMerkleBranch_iff_verifyMerkleProof (log2_pos named)
      (Nat.mod_lt _ (Nat.two_pow_pos _))).mp valid

/-- Zero nodes in front of a branch leave the check of a normalized branch unchanged.

This holds when the branch already reaches the depth of the index that the check reads. -/
theorem isValidNormalizedMerkleBranch_normalize {leaf root : Bytes32} {branch : List Bytes32}
    {gindex target : Nat} (deep : Nat.log2 gindex ≤ branch.length) :
    isValidNormalizedMerkleBranch leaf (normalizeMerkleBranch branch target) gindex root =
      isValidNormalizedMerkleBranch leaf branch gindex root := by
  unfold isValidNormalizedMerkleBranch normalizeMerkleBranch
  by_cases zero : gindex < 1
  · simp [gindexDepth, zero, bind, Except.bind]
  · simp only [gindexDepth, zero, ↓reduceIte, bind, Except.bind]
    cases getSubtreeIndex gindex with
    | error => rfl
    | ok index =>
      -- The added zeros join the front, and the rest of the branch stays the same.
      have zeroed : ∀ node ∈ List.replicate (Nat.log2 target - branch.length) zeroBytes32,
          node = zeroBytes32 := fun _ member => List.eq_of_mem_replicate member
      generalize List.replicate (Nat.log2 target - branch.length) zeroBytes32 = zeros at zeroed
      have extra : (zeros ++ branch).length - Nat.log2 gindex =
          zeros.length + (branch.length - Nat.log2 gindex) := by
        simp only [List.length_append]
        omega
      rw [extra, List.take_length_add_append, List.drop_length_add_append, List.all_append]
      have front : (zeros.all fun node => node == Vector.replicate 32 0) = true :=
        List.all_eq_true.mpr fun node member => by simp [zeroed node member, zeroBytes32]
      rw [front, Bool.true_and]

open LightClientError (require liftRoot specifiedFork)

variable {preset : Preset} {fork : Fork}

/-- A bootstrap exists only for a state at the slot of its block. -/
theorem createLightClientBootstrap_stateAtBlock {config : Config} {state : BeaconState preset fork}
    {block : SignedBeaconBlock preset fork} {bootstrap : LightClientBootstrap preset fork}
    (created : createLightClientBootstrap config state block = .ok bootstrap) :
    state.slot = state.latestBlockHeader.slot := by
  unfold createLightClientBootstrap at created
  simp only [bind_ok_iff] at created
  obtain ⟨_, -, _, -, _, atBlock, -⟩ := created
  exact LightClientError.require_ok.mp atBlock

/-- An update has the slot of its block as its signature slot.

Its aggregate has at least the minimum number of participants of the sync committee. -/
theorem createLightClientUpdate_signature {config : Config} {signatureFork finalizedFork : Fork}
    {state : BeaconState preset signatureFork} {block : SignedBeaconBlock preset signatureFork}
    {attestedState : BeaconState preset fork} {attestedBlock : SignedBeaconBlock preset fork}
    {finalizedBlock : Option (SignedBeaconBlock preset finalizedFork)}
    {finalizedEarlier : finalizedFork ≤ fork} {update : LightClientUpdate preset fork}
    (created : createLightClientUpdate config state block attestedState attestedBlock
      finalizedBlock finalizedEarlier = .ok update) :
    update.signatureSlot = block.message.slot ∧
      preset.MIN_SYNC_COMMITTEE_PARTICIPANTS.toNat ≤ update.syncAggregate.participants := by
  unfold createLightClientUpdate at created
  simp only [bind_ok_iff] at created
  obtain ⟨_, -, ⟨signatureAltair⟩, -, _, -, _, few, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -,
    _, -, _, -, tail⟩ := created
  have enough := LightClientError.require_ok.mp few
  -- Every path to a result ends in an update with the slot of the block and the aggregate of it.
  suffices h : update.signatureSlot = block.message.slot ∧
      update.syncAggregate = block.message.body.syncAggregate signatureAltair by
    exact ⟨h.1, h.2 ▸ enough⟩
  split at tail
  all_goals simp only [bind, Except.bind, pure, Except.pure] at tail
  -- A failing step cannot return an update, and each succeeding step leaves the next one.
  all_goals repeat' (first
    | contradiction
    | split at tail
    | simp only [bind, Except.bind, pure, Except.pure] at tail)
  all_goals (simp only [Except.ok.injEq] at tail; subst tail; exact ⟨rfl, rfl⟩)

/-- The optimistic update and the finality update of an update agree on what they share.

They share the attested header, the aggregate and the signature slot. -/
theorem createLightClientOptimisticUpdate_eq_finalityUpdate
    (update : LightClientUpdate preset fork) :
    (createLightClientOptimisticUpdate update).attestedHeader =
        (createLightClientFinalityUpdate update).attestedHeader ∧
      (createLightClientOptimisticUpdate update).syncAggregate =
        (createLightClientFinalityUpdate update).syncAggregate ∧
      (createLightClientOptimisticUpdate update).signatureSlot =
        (createLightClientFinalityUpdate update).signatureSlot :=
  ⟨rfl, rfl, rfl⟩

end EthLib.Consensus
