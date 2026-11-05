module

public import EthLib.Consensus.LightClient.Containers
public import EthLib.Consensus.Proofs.Containers.Block
public import EthLib.Consensus.Proofs.Containers.State
public import EthLib.Serialization.Proofs.Ssz.Typed.Since

/-!
# Proofs: the light client containers

Each container has distinct field names at every fork, and converts to and from its fields.

So its bytes decode back to it.

The generalized indices of the light client are those that the types give.

They hold at every fork from Altair, for both presets.

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
