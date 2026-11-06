module

public import EthLib.Consensus.LightClient.Containers
public import EthLib.Consensus.Proofs.Containers.Block
public import EthLib.Consensus.Proofs.Containers.State
public import EthLib.Serialization.Proofs.Ssz.Codec.PathValues
public import EthLib.Serialization.Proofs.Ssz.Typed.Since

/-!
# Proofs: the light client containers

Each container has distinct field names at every fork, and converts to and from its fields.

So its bytes decode back to it.

The generalized indices of the light client are those that the types give.

They hold at every fork from Altair, for both presets.

At Altair they hold at every preset, and the node at each index is the root of its field.

So the length of each branch is the depth of the node it proves.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- The field names of a light client header are distinct at every fork. -/
theorem LightClientHeader.names_nodup : (LightClientHeader.names fork).Nodup := by
  have all : (["beacon", "execution", "execution_block_hash", "execution_branch"] :
      List String).Nodup := by decide
  exact all.sublist ((((List.Sublist.refl ["beacon"]).append (duringNames_sublist _)).append
    (sinceNames_sublist _)).append (sinceNames_sublist _))

/-- At Altair, the state type gives the three light client indices, at every preset.

The finalized root is the second field of the checkpoint at ordinal 20.

The current and next committees occupy ordinals 22 and 23 of the 24-field state. -/
theorem lightClientGindices_altair_eq :
    getGeneralizedIndex (SszType.desc (BeaconState preset .altair))
        [.position 20, .position 1] = .ok (finalizedRootGindex .altair) ∧
      getGeneralizedIndex (SszType.desc (BeaconState preset .altair))
        [.position 22] = .ok (currentSyncCommitteeGindex .altair) ∧
      getGeneralizedIndex (SszType.desc (BeaconState preset .altair))
        [.position 23] = .ok (nextSyncCommitteeGindex .altair) := by
  -- Field widths affect child trees but not the container's arity or field positions.
  unfold SszType.desc
  simp +decide [BeaconState.instSszType, SszType.forkContainer, SszType.container,
    getGeneralizedIndex, Desc.resolveStep, Desc.chunkPosition, Desc.elementType,
    Desc.chunkCount, SszType.desc, SszFields.descs, BeaconState.names,
    Bind.bind, Except.bind, Pure.pure, Except.pure, nextPow2, finalizedRootGindex,
    currentSyncCommitteeGindex, nextSyncCommitteeGindex]
  simp [gindexConcat, gindexDepth, depthFor, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- In an Altair state, the next committee node is the root of the state's next committee.

The next committee branch of an update opens this node against the attested state root.

It holds for every state of a lawful type with a nonempty committee, whatever the update. -/
theorem BeaconState.nodeRoot_nextSyncCommittee_altair
    [LawfulSszType (BeaconState preset .altair)] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
    (state : BeaconState preset .altair) {root : Bytes32}
    (rooted : SszType.hashTreeRoot (state.nextSyncCommittee (by decide)) = .ok root) :
    nodeRoot (SszType.desc (BeaconState preset .altair)) (SszType.toValue state)
      (nextSyncCommitteeGindex .altair) = .ok root.toArray := by
  -- Ordinal 23 of the state holds the next committee.
  have selected : PathSelects (SszType.desc (BeaconState preset .altair))
      (SszType.toValue state) [.position 23] root.toArray := by
    apply PathSelects.containerField
      (LawfulSszType.wellFormed (α := BeaconState preset .altair))
      (LawfulSszType.fits state) (ordinal := 23)
      (child := SszType.desc (SyncCommittee preset))
      (inner := SszType.toValue (state.nextSyncCommittee (by decide)))
    · rfl
    · rfl
    · exact .root (SszType.hashTreeRoot_ok_iff.mp rooted)
  -- The value path and the type path share the Altair branch index.
  obtain ⟨index, indexed, read⟩ := selected.reads
  have index_eq : index = nextSyncCommitteeGindex .altair := by
    exact Except.ok.inj (indexed.symm.trans lightClientGindices_altair_eq.2.2)
  simpa [index_eq] using read

/-- In an Altair state, the current committee node is the root of the state's current committee.

The branch of a bootstrap opens this node against the state root of its beacon header.

It holds for every state with a lawful type and a nonempty committee. -/
theorem BeaconState.nodeRoot_currentSyncCommittee_altair
    [LawfulSszType (BeaconState preset .altair)] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
    (state : BeaconState preset .altair) {root : Bytes32}
    (rooted : SszType.hashTreeRoot (state.currentSyncCommittee (by decide)) = .ok root) :
    nodeRoot (SszType.desc (BeaconState preset .altair)) (SszType.toValue state)
      (currentSyncCommitteeGindex .altair) = .ok root.toArray := by
  -- Ordinal 22 of the state holds the current committee.
  have selected : PathSelects (SszType.desc (BeaconState preset .altair))
      (SszType.toValue state) [.position 22] root.toArray := by
    apply PathSelects.containerField
      (LawfulSszType.wellFormed (α := BeaconState preset .altair))
      (LawfulSszType.fits state) (ordinal := 22)
      (child := SszType.desc (SyncCommittee preset))
      (inner := SszType.toValue (state.currentSyncCommittee (by decide)))
    · rfl
    · rfl
    · exact .root (SszType.hashTreeRoot_ok_iff.mp rooted)
  -- The value path and the type path share the Altair bootstrap index.
  obtain ⟨index, indexed, read⟩ := selected.reads
  have index_eq : index = currentSyncCommitteeGindex .altair := by
    exact Except.ok.inj (indexed.symm.trans lightClientGindices_altair_eq.2.1)
  simpa [index_eq] using read

/-- In an Altair state, the finality node is the root of the finalized checkpoint's root field.

The finality branch of an update opens this node against the attested state root. -/
theorem BeaconState.nodeRoot_finalizedCheckpoint_root_altair
    [LawfulSszType (BeaconState preset .altair)]
    (state : BeaconState preset .altair) {root : Bytes32}
    (rooted : SszType.hashTreeRoot state.finalizedCheckpoint.root = .ok root) :
    nodeRoot (SszType.desc (BeaconState preset .altair)) (SszType.toValue state)
      (finalizedRootGindex .altair) = .ok root.toArray := by
  -- Finality descends through the checkpoint at ordinal 20, then its root at ordinal 1.
  have selected : PathSelects (SszType.desc (BeaconState preset .altair))
      (SszType.toValue state) [.position 20, .position 1] root.toArray := by
    apply PathSelects.containerField
      (LawfulSszType.wellFormed (α := BeaconState preset .altair))
      (LawfulSszType.fits state) (ordinal := 20)
      (child := SszType.desc Checkpoint) (inner := SszType.toValue state.finalizedCheckpoint)
    · rfl
    · rfl
    · apply PathSelects.containerField
        (LawfulSszType.wellFormed (α := Checkpoint))
        (LawfulSszType.fits state.finalizedCheckpoint) (ordinal := 1)
        (child := SszType.desc Root) (inner := SszType.toValue state.finalizedCheckpoint.root)
      · rfl
      · rfl
      · exact .root (SszType.hashTreeRoot_ok_iff.mp rooted)
  -- The joined path is the finality branch index, not the checkpoint container's index.
  obtain ⟨index, indexed, read⟩ := selected.reads
  have index_eq : index = finalizedRootGindex .altair := by
    exact Except.ok.inj (indexed.symm.trans lightClientGindices_altair_eq.1)
  simpa [index_eq] using read

variable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]

instance : NeZero (Nat.log2 (executionBranchGindex fork)) :=
  ⟨by unfold executionBranchGindex; split <;> decide⟩

instance : LawfulSszType (LightClientHeader preset fork) :=
  .container
    ⟨by
      by_cases gloas : Fork.glamsterdam ≤ fork
      · have late : ¬fork < Fork.glamsterdam := Nat.not_lt_of_le gloas
        have capella : Fork.shapella ≤ fork := Nat.le_trans (by decide) gloas
        simp [LightClientHeader.names, sinceNames, duringNames, SszFields.descs, capella, gloas,
          late]
      · have early : fork < Fork.glamsterdam := Nat.lt_of_not_le gloas
        by_cases capella : Fork.shapella ≤ fork <;>
          simp [LightClientHeader.names, sinceNames, duringNames, SszFields.descs, capella,
            gloas, early],
     by simp [LightClientHeader.names],
     firstDuplicate_of_nodup _ LightClientHeader.names_nodup⟩
    (fun _ => rfl) (fun _ => rfl)

instance : NeZero (Nat.log2 (currentSyncCommitteeGindex fork)) :=
  ⟨by unfold currentSyncCommitteeGindex; split <;> (try split) <;> decide⟩

instance : NeZero (Nat.log2 (nextSyncCommitteeGindex fork)) :=
  ⟨by unfold nextSyncCommitteeGindex; split <;> (try split) <;> decide⟩

instance : NeZero (Nat.log2 (finalizedRootGindex fork)) :=
  ⟨by unfold finalizedRootGindex; split <;> (try split) <;> decide⟩

instance : LawfulSszType (LightClientBootstrap preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType (LightClientUpdate preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType (LightClientFinalityUpdate preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType (LightClientOptimisticUpdate preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

/-- The finalized root and the sync committees sit at the indices that the state type gives.

This holds at every fork from Altair, for both presets.

The root is the second field of the finalized checkpoint. -/
theorem lightClientGindices_eq {preset : Preset} {fork : Fork}
    (named : preset = .mainnet ∨ preset = .minimal) (altair : .altair ≤ fork) :
    (stateGindex preset fork "finalized_checkpoint" [.position 1]).toOption =
        some (finalizedRootGindex fork) ∧
      (stateGindex preset fork "current_sync_committee" []).toOption =
        some (currentSyncCommitteeGindex fork) ∧
      (stateGindex preset fork "next_sync_committee" []).toOption =
        some (nextSyncCommitteeGindex fork) := by
  rcases named with rfl | rfl <;> cases fork <;> first
    | exact absurd altair (by decide) | decide +kernel

/-- The execution payload sits at the generalized index that the type of the body gives.

This holds from Capella to the forks before Gloas, for both presets. -/
theorem executionPayloadGindex_eq {preset : Preset} {fork : Fork}
    (named : preset = .mainnet ∨ preset = .minimal) (capella : .shapella ≤ fork)
    (beforeGloas : fork < .glamsterdam) :
    (SszType.getGeneralizedIndex (BeaconBlockBody preset fork)
        [.position ((BeaconBlockBody.names fork).idxOf "execution_payload")]).toOption =
      some EXECUTION_PAYLOAD_GINDEX := by
  rcases named with rfl | rfl <;> cases fork <;> first
    | exact absurd capella (by decide) | exact absurd beforeGloas (by decide) | decide +kernel

/-- The block hash sits at the index that the type of an execution payload header gives.

This holds from Capella to the forks before Gloas, for both presets. -/
theorem payloadHeaderBlockHashGindex_eq {preset : Preset} {fork : Fork}
    (named : preset = .mainnet ∨ preset = .minimal) (capella : .shapella ≤ fork)
    (beforeGloas : fork < .glamsterdam) :
    (SszType.getGeneralizedIndex (ExecutionPayloadHeader preset fork)
        [.position ((ExecutionPayloadHeader.names fork).idxOf "block_hash")]).toOption =
      some (payloadHeaderBlockHashGindex fork) := by
  rcases named with rfl | rfl <;> cases fork <;> first
    | exact absurd capella (by decide) | exact absurd beforeGloas (by decide) | decide +kernel

/-- The block hash of the payload sits at the index that the type of the body gives.

The index is that of Capella in a Capella body, and that of Deneb from Deneb to Fulu.

This holds for both presets. -/
theorem executionBlockHashGindex_eq {preset : Preset} {fork : Fork}
    (named : preset = .mainnet ∨ preset = .minimal) (capella : .shapella ≤ fork)
    (beforeGloas : fork < .glamsterdam) :
    (SszType.getGeneralizedIndex (BeaconBlockBody preset fork)
        [.position ((BeaconBlockBody.names fork).idxOf "execution_payload"),
          .position ((ExecutionPayload.names fork).idxOf "block_hash")]).toOption =
      some (if .dencun ≤ fork then EXECUTION_BLOCK_HASH_GINDEX_DENEB
        else EXECUTION_BLOCK_HASH_GINDEX) := by
  rcases named with rfl | rfl <;> cases fork <;> first
    | exact absurd capella (by decide) | exact absurd beforeGloas (by decide) | decide +kernel

/-- From Gloas, the parent block hash of the bid sits at the index that the type of the body gives.

The bid is the message of the signed bid, and the parent block hash is its first field.

This holds for both presets. -/
theorem executionBlockHashGindexGloas_eq {preset : Preset} {fork : Fork}
    (named : preset = .mainnet ∨ preset = .minimal) (gloas : .glamsterdam ≤ fork) :
    (SszType.getGeneralizedIndex (BeaconBlockBody preset fork)
        [.position ((BeaconBlockBody.names fork).idxOf "signed_execution_payload_bid"),
          .position 0,
          .position ((ExecutionPayloadBid.names fork).idxOf "parent_block_hash")]).toOption =
      some EXECUTION_BLOCK_HASH_GINDEX_GLOAS := by
  rcases named with rfl | rfl <;> cases fork <;> first
    | exact absurd gloas (by decide) | decide +kernel

end EthLib.Consensus
