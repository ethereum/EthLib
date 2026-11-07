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

The execution indices hold from Capella, at every preset.

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

/-- From Capella to the forks before Gloas, the execution payload is field 9 of a body. -/
theorem BeaconBlockBody.idxOf_executionPayload (capella : .shapella ≤ fork)
    (beforeGloas : fork < .glamsterdam) :
    (BeaconBlockBody.names fork).idxOf "execution_payload" = 9 := by
  cases fork <;>
    first | exact absurd capella (by decide) | exact absurd beforeGloas (by decide) | decide

/-- The block hash is field 12 of an execution payload header. -/
theorem ExecutionPayloadHeader.idxOf_blockHash :
    (ExecutionPayloadHeader.names fork).idxOf "block_hash" = 12 := by
  cases fork <;> decide

/-- The block hash is field 12 of an execution payload. -/
theorem ExecutionPayload.idxOf_blockHash :
    (ExecutionPayload.names fork).idxOf "block_hash" = 12 := by
  cases fork <;> decide

/-- From Capella to the forks before Gloas, a body has 11 to 13 fields, so 16 leaves.

The execution payload is field 9. -/
theorem BeaconBlockBody.desc_executionPayload (capella : .shapella ≤ fork)
    (beforeGloas : fork < .glamsterdam) :
    ∃ fields, SszType.desc (BeaconBlockBody preset fork) =
        .container (BeaconBlockBody.names fork) fields ∧ nextPow2 fields.length = 16 ∧
      fields[9]? = some (SszType.desc (ExecutionPayload preset fork)) := by
  have counted : ∃ fields, SszType.desc (BeaconBlockBody preset fork) =
        .container (BeaconBlockBody.names fork) fields ∧
      (fields.length = 11 ∨ fields.length = 12 ∨ fields.length = 13) ∧
      fields[9]? = some (SszType.desc (ExecutionPayload preset fork)) := by
    cases fork <;> first
      | exact absurd capella (by decide)
      | exact absurd beforeGloas (by decide)
      | exact ⟨_, rfl, by first | exact .inl rfl | exact .inr (.inl rfl) | exact .inr (.inr rfl),
          rfl⟩
  obtain ⟨fields, desc, count, chosen⟩ := counted
  refine ⟨fields, desc, ?_, chosen⟩
  rcases count with count | count | count <;> rw [count] <;> simp [nextPow2, depthFor]

/-- From Capella to the forks before Gloas, the block hash is field 12 of an execution payload.

The payload has 15 fields at Capella, so 16 leaves, and 17 from Deneb, so 32 leaves. -/
theorem ExecutionPayload.desc_blockHash (capella : .shapella ≤ fork)
    (beforeGloas : fork < .glamsterdam) :
    ∃ names fields, SszType.desc (ExecutionPayload preset fork) = .container names fields ∧
      nextPow2 fields.length = (if .dencun ≤ fork then 32 else 16) ∧
      fields[12]? = some (SszType.desc Hash32) := by
  have counted : ∃ names fields, SszType.desc (ExecutionPayload preset fork) =
        .container names fields ∧
      fields.length = (if .dencun ≤ fork then 17 else 15) ∧
      fields[12]? = some (SszType.desc Hash32) := by
    cases fork <;> first
      | exact absurd capella (by decide)
      | exact absurd beforeGloas (by decide)
      | exact ⟨_, _, rfl, rfl, rfl⟩
  obtain ⟨names, fields, desc, count, chosen⟩ := counted
  refine ⟨names, fields, desc, ?_, chosen⟩
  rw [count]
  split <;> simp [nextPow2, depthFor]

/-- From Capella to the forks before Gloas, field 9 of a body is node 25 of its tree.

This holds at every preset. -/
theorem executionPayloadGindex_eq_of_lt (capella : .shapella ≤ fork)
    (beforeGloas : fork < .glamsterdam) :
    getGeneralizedIndex (SszType.desc (BeaconBlockBody preset fork)) [.position 9] =
      .ok EXECUTION_PAYLOAD_GINDEX := by
  obtain ⟨fields, desc, filled, chosen⟩ :=
    BeaconBlockBody.desc_executionPayload (preset := preset) capella beforeGloas
  rw [desc]
  exact getGeneralizedIndex_step (filled ▸ resolveStep_container _ _ _ _ chosen)
    (getGeneralizedIndex_nil _) (gindexConcat_root_right (by decide))

/-- From Capella to the forks before Gloas, the block hash of the payload of a body is node 412.

From Deneb the payload has 32 leaves, so the node is 812.

This holds at every preset. -/
theorem executionBlockHashGindex_eq_of_lt (capella : .shapella ≤ fork)
    (beforeGloas : fork < .glamsterdam) :
    getGeneralizedIndex (SszType.desc (BeaconBlockBody preset fork)) [.position 9, .position 12] =
      .ok (if .dencun ≤ fork then EXECUTION_BLOCK_HASH_GINDEX_DENEB
        else EXECUTION_BLOCK_HASH_GINDEX) := by
  obtain ⟨fields, desc, filled, chosen⟩ :=
    BeaconBlockBody.desc_executionPayload (preset := preset) capella beforeGloas
  obtain ⟨names, payloadFields, payloadDesc, payloadFilled, hashChosen⟩ :=
    ExecutionPayload.desc_blockHash (preset := preset) capella beforeGloas
  rw [desc]
  rw [payloadDesc] at chosen
  -- The payload has 16 leaves at Capella and 32 from Deneb, and the hash is leaf 12.
  by_cases deneb : Fork.dencun ≤ fork <;> simp only [deneb, ↓reduceIte] at payloadFilled ⊢
  · exact getGeneralizedIndex_step (filled ▸ resolveStep_container _ _ _ _ chosen)
      (getGeneralizedIndex_step (payloadFilled ▸ resolveStep_container _ _ _ _ hashChosen)
        (getGeneralizedIndex_nil _) (gindexConcat_root_right (by decide)))
      (by rw [gindexConcat_eq (by decide) (by decide)]; exact congrArg Except.ok (by decide))
  · exact getGeneralizedIndex_step (filled ▸ resolveStep_container _ _ _ _ chosen)
      (getGeneralizedIndex_step (payloadFilled ▸ resolveStep_container _ _ _ _ hashChosen)
        (getGeneralizedIndex_nil _) (gindexConcat_root_right (by decide)))
      (by rw [gindexConcat_eq (by decide) (by decide)]; exact congrArg Except.ok (by decide))

/-- From Capella to the forks before Gloas, the value of a body holds its payload at field 9. -/
theorem BeaconBlockBody.values_executionPayload (capella : .shapella ≤ fork)
    (beforeGloas : fork < .glamsterdam) (body : BeaconBlockBody preset fork) :
    ∃ values, SszType.toValue body = .seq values ∧ values[9]? =
      some (SszType.toValue
        (body.executionPayload ⟨Nat.le_trans (by decide) capella, beforeGloas⟩)) := by
  cases fork <;> first
    | exact absurd capella (by decide)
    | exact absurd beforeGloas (by decide)
    | exact ⟨_, rfl, rfl⟩

/-- From Gloas, the signed bid of a body follows the fields of the body before it.

It is field 10, and field 8 from Heze, where the deposits and the eth1 data are gone. -/
theorem BeaconBlockBody.idxOf_signedBid (gloas : .glamsterdam ≤ fork) :
    (BeaconBlockBody.names fork).idxOf "signed_execution_payload_bid" =
      if .hegota ≤ fork then 8 else 10 := by
  cases fork <;> first | exact absurd gloas (by decide) | decide

/-- From Gloas, the bid of a body below the root of the body is node 357 of its tree.

This holds at every preset. -/
theorem BeaconBlockBody.resolveStep_signedBid (gloas : .glamsterdam ≤ fork) :
    (SszType.desc (BeaconBlockBody preset fork)).resolveStep
      (.position (if .hegota ≤ fork then 8 else 10)) =
      .ok (357, some (SszType.desc (SignedExecutionPayloadBid preset fork))) := by
  have shaped : ∃ active names fields position,
      SszType.desc (BeaconBlockBody preset fork) = .progressiveContainer active names fields ∧
      fields[if .hegota ≤ fork then 8 else 10]? =
        some (SszType.desc (SignedExecutionPayloadBid preset fork)) ∧
      layoutPosition active (if .hegota ≤ fork then 8 else 10) = .ok position ∧
      progressiveChunkGindex position = 357 := by
    cases fork
    all_goals try exact absurd gloas (by decide)
    all_goals exact ⟨_, _, _, _, rfl, rfl, rfl, by
      simp +decide [progressiveChunkGindex]⟩
  obtain ⟨active, names, fields, position, desc, chosen, placed, gindex⟩ := shaped
  rw [desc, ← gindex]
  exact resolveStep_progressiveContainer active names fields _ position _ chosen placed

/-- The parent block hash is the first field of a bid, node 4 of its tree. -/
theorem ExecutionPayloadBid.resolveStep_parentBlockHash :
    (SszType.desc (ExecutionPayloadBid preset fork)).resolveStep (.position 0) =
      .ok (4, some (SszType.desc Hash32)) := by
  have shaped : ∃ active names fields position,
      SszType.desc (ExecutionPayloadBid preset fork) = .progressiveContainer active names fields ∧
      fields[0]? = some (SszType.desc Hash32) ∧
      layoutPosition active 0 = .ok position ∧ progressiveChunkGindex position = 4 := by
    cases fork
    all_goals exact ⟨_, _, _, _, rfl, rfl, rfl, by
      simp +decide [progressiveChunkGindex]⟩
  obtain ⟨active, names, fields, position, desc, chosen, placed, gindex⟩ := shaped
  rw [desc, ← gindex]
  exact resolveStep_progressiveContainer active names fields _ position _ chosen placed

/-- From Gloas, the parent block hash of the bid of a body is node 2856 of the body.

The path goes through the bid, its message, then its first field.

This holds at every preset. -/
theorem executionBlockHashGindexGloas_eq_of_le (gloas : .glamsterdam ≤ fork) :
    getGeneralizedIndex (SszType.desc (BeaconBlockBody preset fork))
      [.position (if .hegota ≤ fork then 8 else 10), .position 0, .position 0] =
      .ok EXECUTION_BLOCK_HASH_GINDEX_GLOAS := by
  have signed : (SszType.desc (SignedExecutionPayloadBid preset fork)).resolveStep (.position 0) =
      .ok (2, some (SszType.desc (ExecutionPayloadBid preset fork))) := by
    have desc : SszType.desc (SignedExecutionPayloadBid preset fork) =
        .container ["message", "signature"]
          [SszType.desc (ExecutionPayloadBid preset fork),
            SszType.desc Cryptography.Bls.BLSSignature] := rfl
    rw [desc]
    simpa [nextPow2, depthFor] using resolveStep_container ["message", "signature"]
      [SszType.desc (ExecutionPayloadBid preset fork), SszType.desc Cryptography.Bls.BLSSignature]
      0 _ rfl
  exact getGeneralizedIndex_step (BeaconBlockBody.resolveStep_signedBid gloas)
    (getGeneralizedIndex_step signed
      (getGeneralizedIndex_step ExecutionPayloadBid.resolveStep_parentBlockHash
        (getGeneralizedIndex_nil _) (gindexConcat_root_right (by decide)))
      (by rw [gindexConcat_eq (by decide) (by decide)]))
    (by rw [gindexConcat_eq (by decide) (by decide)]; exact congrArg Except.ok (by decide))

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

This holds from Capella to the forks before Gloas, at every preset. -/
theorem executionPayloadGindex_eq {preset : Preset} {fork : Fork} (capella : .shapella ≤ fork)
    (beforeGloas : fork < .glamsterdam) :
    (SszType.getGeneralizedIndex (BeaconBlockBody preset fork)
        [.position ((BeaconBlockBody.names fork).idxOf "execution_payload")]).toOption =
      some EXECUTION_PAYLOAD_GINDEX := by
  rw [BeaconBlockBody.idxOf_executionPayload capella beforeGloas]
  simp [SszType.getGeneralizedIndex, executionPayloadGindex_eq_of_lt (preset := preset) capella
    beforeGloas, Except.toOption]

/-- The block hash sits at the index that the type of an execution payload header gives.

This holds from Capella to the forks before Gloas, at every preset. -/
theorem payloadHeaderBlockHashGindex_eq {preset : Preset} {fork : Fork}
    (capella : .shapella ≤ fork) (beforeGloas : fork < .glamsterdam) :
    (SszType.getGeneralizedIndex (ExecutionPayloadHeader preset fork)
        [.position ((ExecutionPayloadHeader.names fork).idxOf "block_hash")]).toOption =
      some (payloadHeaderBlockHashGindex fork) := by
  rw [ExecutionPayloadHeader.idxOf_blockHash]
  cases fork
  all_goals try first
    | exact absurd capella (by decide)
    | exact absurd beforeGloas (by decide)
  -- The header is a plain container, so its field 12 is a leaf of its tree of fields.
  all_goals
    unfold SszType.getGeneralizedIndex SszType.desc
    simp +decide [ExecutionPayloadHeader.instSszType, SszType.container,
      getGeneralizedIndex, Desc.resolveStep, Desc.chunkPosition, Desc.elementType,
      Desc.chunkCount, SszType.desc, SszFields.descs, ExecutionPayloadHeader.names,
      Bind.bind, Except.bind, Pure.pure, Except.pure, nextPow2, payloadHeaderBlockHashGindex]
    simp [gindexConcat, gindexDepth, depthFor, Bind.bind, Except.bind, Pure.pure, Except.pure,
      Except.toOption]

/-- The block hash of the payload sits at the index that the type of the body gives.

The index is that of Capella in a Capella body, and that of Deneb from Deneb to Fulu.

This holds at every preset. -/
theorem executionBlockHashGindex_eq {preset : Preset} {fork : Fork}
    (capella : .shapella ≤ fork) (beforeGloas : fork < .glamsterdam) :
    (SszType.getGeneralizedIndex (BeaconBlockBody preset fork)
        [.position ((BeaconBlockBody.names fork).idxOf "execution_payload"),
          .position ((ExecutionPayload.names fork).idxOf "block_hash")]).toOption =
      some (if .dencun ≤ fork then EXECUTION_BLOCK_HASH_GINDEX_DENEB
        else EXECUTION_BLOCK_HASH_GINDEX) := by
  rw [BeaconBlockBody.idxOf_executionPayload capella beforeGloas, ExecutionPayload.idxOf_blockHash]
  simp [SszType.getGeneralizedIndex, executionBlockHashGindex_eq_of_lt (preset := preset) capella
    beforeGloas, Except.toOption]

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

This holds at every preset. -/
theorem executionBlockHashGindexGloas_eq {preset : Preset} {fork : Fork}
    (gloas : .glamsterdam ≤ fork) :
    (SszType.getGeneralizedIndex (BeaconBlockBody preset fork)
        [.position ((BeaconBlockBody.names fork).idxOf "signed_execution_payload_bid"),
          .position 0,
          .position ((ExecutionPayloadBid.names fork).idxOf "parent_block_hash")]).toOption =
      some EXECUTION_BLOCK_HASH_GINDEX_GLOAS := by
  have first : (ExecutionPayloadBid.names fork).idxOf "parent_block_hash" = 0 := by
    cases fork <;> decide
  rw [BeaconBlockBody.idxOf_signedBid gloas, first]
  simp [SszType.getGeneralizedIndex,
    executionBlockHashGindexGloas_eq_of_le (preset := preset) gloas, Except.toOption]

end EthLib.Consensus
