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

The indices of the finalized root and of the sync committees are those that the types give.

They hold at every fork from Altair, at every preset.

The execution indices hold from Capella, in the mainnet and the minimal presets.

At each of these forks the node at each index is the root of its field.

So the length of each branch is the depth of the node it proves.

The nodes are those of a state of a lawful type.

Instance search finds that type lawful in the mainnet and the minimal presets.
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

/-- From Altair to the forks before Gloas, the state type gives the three light client indices.

This holds at every preset.

The finalized root is the second field of the checkpoint at ordinal 20.

The current and next committees occupy ordinals 22 and 23 of the state. -/
theorem lightClientGindices_eq_of_lt (altair : .altair ≤ fork) (beforeGloas : fork < .glamsterdam) :
    getGeneralizedIndex (SszType.desc (BeaconState preset fork))
        [.position 20, .position 1] = .ok (finalizedRootGindex fork) ∧
      getGeneralizedIndex (SszType.desc (BeaconState preset fork))
        [.position 22] = .ok (currentSyncCommitteeGindex fork) ∧
      getGeneralizedIndex (SszType.desc (BeaconState preset fork))
        [.position 23] = .ok (nextSyncCommitteeGindex fork) := by
  cases fork
  all_goals try first
    | exact absurd altair (by decide)
    | exact absurd beforeGloas (by decide)
  -- Field widths affect child trees but not the container's arity or field positions.
  all_goals
    unfold SszType.desc
    simp +decide [BeaconState.instSszType, SszType.forkContainer, SszType.container,
      getGeneralizedIndex, Desc.resolveStep, Desc.chunkPosition, Desc.elementType,
      Desc.chunkCount, SszType.desc, SszFields.descs, BeaconState.names,
      Bind.bind, Except.bind, Pure.pure, Except.pure, nextPow2, finalizedRootGindex,
      currentSyncCommitteeGindex, nextSyncCommitteeGindex]
    simp [gindexConcat, gindexDepth, depthFor, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- From Gloas, the state type gives the three light client indices, at every preset.

The state is a progressive container, so a field sits at its place in the layout.

From Heze the three eth1 fields before them are gone, so the ordinals drop by three.

The places, and so the indices, stay those of Gloas. -/
theorem lightClientGindices_eq_of_glamsterdam_le (gloas : .glamsterdam ≤ fork) :
    getGeneralizedIndex (SszType.desc (BeaconState preset fork))
        [.position (if .hegota ≤ fork then 17 else 20), .position 1] =
          .ok (finalizedRootGindex fork) ∧
      getGeneralizedIndex (SszType.desc (BeaconState preset fork))
        [.position (if .hegota ≤ fork then 19 else 22)] = .ok (currentSyncCommitteeGindex fork) ∧
      getGeneralizedIndex (SszType.desc (BeaconState preset fork))
        [.position (if .hegota ≤ fork then 20 else 23)] = .ok (nextSyncCommitteeGindex fork) := by
  cases fork
  all_goals try exact absurd gloas (by decide)
  all_goals
    unfold SszType.desc
    simp +decide [BeaconState.instSszType, SszType.forkContainer, SszType.progressiveContainer,
      getGeneralizedIndex, Desc.resolveStep, Desc.chunkPosition, Desc.elementType,
      Desc.chunkCount, SszType.desc, SszFields.descs, BeaconState.names,
      BeaconState.activeFields, layoutPosition, activePosition, progressiveChunkGindex,
      Bind.bind, Except.bind, Pure.pure, Except.pure, nextPow2, finalizedRootGindex,
      currentSyncCommitteeGindex, nextSyncCommitteeGindex]
    simp [gindexConcat, gindexDepth, depthFor, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- The finalized root and the sync committees sit at the indices that the state type gives.

This holds at every fork from Altair and at every preset.

The root is the second field of the finalized checkpoint. -/
theorem lightClientGindices_eq (altair : .altair ≤ fork) :
    stateGindex preset fork "finalized_checkpoint" [.position 1] = .ok (finalizedRootGindex fork) ∧
      stateGindex preset fork "current_sync_committee" [] =
        .ok (currentSyncCommitteeGindex fork) ∧
      stateGindex preset fork "next_sync_committee" [] = .ok (nextSyncCommitteeGindex fork) := by
  -- At each fork the name of a field gives the ordinal that the two forms above read.
  unfold stateGindex SszType.getGeneralizedIndex
  cases fork
  all_goals try exact absurd altair (by decide)
  all_goals first
    | exact lightClientGindices_eq_of_lt (by decide) (by decide)
    | exact lightClientGindices_eq_of_glamsterdam_le (by decide)

/-- At every fork from Altair, the next committee node is the root of the state's next committee.

The next committee branch of an update opens this node against the attested state root.

It holds for every state of a lawful type with a nonempty committee. -/
theorem BeaconState.nodeRoot_nextSyncCommittee
    [LawfulSszType (BeaconState preset fork)] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
    (altair : .altair ≤ fork) (state : BeaconState preset fork) {root : Bytes32}
    (rooted : SszType.hashTreeRoot (state.nextSyncCommittee altair) = .ok root) :
    nodeRoot (SszType.desc (BeaconState preset fork)) (SszType.toValue state)
      (nextSyncCommitteeGindex fork) = .ok root.toArray := by
  -- The field sits at the ordinal of its name, in a container or a progressive container.
  have selected : PathSelects (SszType.desc (BeaconState preset fork)) (SszType.toValue state)
      [.position ((BeaconState.names fork).idxOf "next_sync_committee")] root.toArray := by
    have inner := PathSelects.root
      ((SszType.hashTreeRoot_ok_iff (α := Rooted (SyncCommittee preset))).mp rooted)
    cases fork
    all_goals try exact absurd altair (by decide)
    all_goals first
      | exact PathSelects.containerField (LawfulSszType.wellFormed (α := type_of% state))
          (LawfulSszType.fits state) rfl rfl inner
      | exact PathSelects.progressiveField (LawfulSszType.wellFormed (α := type_of% state))
          (LawfulSszType.fits state) rfl rfl inner
  exact selected.nodeRoot_eq (lightClientGindices_eq altair).2.2

/-- At every fork from Altair, the current committee node is the root of the current committee.

The branch of a bootstrap opens this node against the state root of its beacon header.

It holds for every state of a lawful type with a nonempty committee. -/
theorem BeaconState.nodeRoot_currentSyncCommittee
    [LawfulSszType (BeaconState preset fork)] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
    (altair : .altair ≤ fork) (state : BeaconState preset fork) {root : Bytes32}
    (rooted : SszType.hashTreeRoot (state.currentSyncCommittee altair) = .ok root) :
    nodeRoot (SszType.desc (BeaconState preset fork)) (SszType.toValue state)
      (currentSyncCommitteeGindex fork) = .ok root.toArray := by
  -- The field sits at the ordinal of its name, in a container or a progressive container.
  have selected : PathSelects (SszType.desc (BeaconState preset fork)) (SszType.toValue state)
      [.position ((BeaconState.names fork).idxOf "current_sync_committee")] root.toArray := by
    have inner := PathSelects.root
      ((SszType.hashTreeRoot_ok_iff (α := Rooted (SyncCommittee preset))).mp rooted)
    cases fork
    all_goals try exact absurd altair (by decide)
    all_goals first
      | exact PathSelects.containerField (LawfulSszType.wellFormed (α := type_of% state))
          (LawfulSszType.fits state) rfl rfl inner
      | exact PathSelects.progressiveField (LawfulSszType.wellFormed (α := type_of% state))
          (LawfulSszType.fits state) rfl rfl inner
  exact selected.nodeRoot_eq (lightClientGindices_eq altair).2.1

/-- At every fork from Altair, the finality node is the finalized root of the state.

The finality branch of an update opens this node against the attested state root.

It holds for every state of a lawful type. -/
theorem BeaconState.nodeRoot_finalizedCheckpoint_root
    [LawfulSszType (BeaconState preset fork)]
    (altair : .altair ≤ fork) (state : BeaconState preset fork) :
    nodeRoot (SszType.desc (BeaconState preset fork)) (SszType.toValue state)
      (finalizedRootGindex fork) = .ok state.finalizedCheckpoint.root.toArray := by
  -- Finality descends through the checkpoint field, then its root at ordinal 1.
  have checkpoint : PathSelects (SszType.desc Checkpoint)
      (SszType.toValue state.finalizedCheckpoint) [.position 1]
      state.finalizedCheckpoint.root.toArray :=
    PathSelects.containerField (LawfulSszType.wellFormed (α := Checkpoint))
      (LawfulSszType.fits state.finalizedCheckpoint) (ordinal := 1)
      (child := SszType.desc Root) (inner := SszType.toValue state.finalizedCheckpoint.root)
      rfl rfl (.root (hashTreeRoot_chunk (by simp [bytesPerChunk])))
  have selected : PathSelects (SszType.desc (BeaconState preset fork)) (SszType.toValue state)
      [.position ((BeaconState.names fork).idxOf "finalized_checkpoint"), .position 1]
      state.finalizedCheckpoint.root.toArray := by
    cases fork
    all_goals try exact absurd altair (by decide)
    all_goals first
      | exact PathSelects.containerField (LawfulSszType.wellFormed (α := type_of% state))
          (LawfulSszType.fits state) rfl rfl checkpoint
      | exact PathSelects.progressiveField (LawfulSszType.wellFormed (α := type_of% state))
          (LawfulSszType.fits state) rfl rfl checkpoint
  exact selected.nodeRoot_eq (lightClientGindices_eq altair).1

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

/-- A node at the depth of the leaves of a container is the root of the field there.

The type and the value need the same number of fields, and nothing else of the other fields. -/
private theorem nodeRoot_containerLeaf {names : List String} {fields : List Desc}
    {values : List Value} {count index ordinal : Nat} {child : Desc} {inner : Value}
    {root : Bytes} (counted : fields.length = count) (paired : fields.length = values.length)
    (named : 2 ≤ index) (depth : Nat.log2 index = depthFor count)
    (placed : gindexBelow index (depthFor count) = ordinal)
    (selectedType : fields[ordinal]? = some child) (selectedValue : values[ordinal]? = some inner)
    (rooted : hashTreeRoot child inner = .ok root) :
    nodeRoot (.container names fields) (.seq values) index = .ok root := by
  have laid : merkleLayout (.container names fields) (.seq values) =
      .ok (.nesting ((fields.zip values).map some) (some fields.length)) := by
    simp [merkleLayout, paired, Pure.pure, Except.pure]
  -- A container mixes nothing in, so the walk stays in its bounded tree of fields.
  rw [nodeRoot_left_contents _ _ _ laid index named
    (fun _ mixed => by simp [MerkleLayout.nesting] at mixed)]
  simp only [MerkleLayout.nesting, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, depth,
    ← counted]
  rw [boundedNode_nested_leaf _ _ _ rfl child inner ?enough index 0 fields.length ?selected,
    rooted]
  · -- The field is no deeper than the deepest field, one level under the container.
    have member : child ∈ fields := List.mem_of_getElem? selectedType
    have := nesting_le_deepest child fields member
    simp only [Desc.nesting]
    omega
  · rw [Nat.zero_add, counted, placed]
    simpa only [List.getElem?_map, Option.map_eq_some_iff] using
      ⟨(child, inner), List.getElem?_zip_eq_some.mpr ⟨selectedType, selectedValue⟩, rfl⟩

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] in
/-- From Capella to the forks before Gloas, the block hash node of a payload header is the hash.

It sits at the index that the light client reads for the fork of the header.

This holds at every preset. -/
theorem ExecutionPayloadHeader.nodeRoot_blockHash (capella : .shapella ≤ fork)
    (beforeGloas : fork < .glamsterdam) (header : ExecutionPayloadHeader preset fork) :
    nodeRoot (SszType.desc (ExecutionPayloadHeader preset fork)) (SszType.toValue header)
      (payloadHeaderBlockHashGindex fork) = .ok header.blockHash.toArray := by
  -- The block hash is field 12 at each of these forks, a leaf of the tree of fields.
  cases fork
  all_goals try first
    | exact absurd capella (by decide)
    | exact absurd beforeGloas (by decide)
  all_goals first
    | exact nodeRoot_containerLeaf (count := 15) (ordinal := 12)
        (child := .byteVector bytesPerChunk) (inner := .bytes header.blockHash.toArray)
        rfl rfl (by decide) (by decide +kernel) (by decide +kernel) rfl rfl
        (hashTreeRoot_chunk (by simp [bytesPerChunk]))
    | exact nodeRoot_containerLeaf (count := 17) (ordinal := 12)
        (child := .byteVector bytesPerChunk) (inner := .bytes header.blockHash.toArray)
        rfl rfl (by decide) (by decide +kernel) (by decide +kernel) rfl rfl
        (hashTreeRoot_chunk (by simp [bytesPerChunk]))

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
