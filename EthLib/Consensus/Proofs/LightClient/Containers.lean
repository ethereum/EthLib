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

They hold from Altair to the forks before Gloas, for both presets.

So the length of each branch is the depth of the node it proves.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- The field names of a light client header are distinct at every fork. -/
theorem LightClientHeader.names_nodup : (LightClientHeader.names fork).Nodup := by
  have all : (["beacon", "execution", "execution_branch"] : List String).Nodup := by decide
  exact all.sublist ((List.Sublist.refl ["beacon"]).append (sinceNames_sublist _))

variable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]

instance : NeZero (Nat.log2 EXECUTION_PAYLOAD_GINDEX) := ⟨by decide⟩

instance : LawfulSszType (LightClientHeader preset fork) :=
  .container
    ⟨by
      by_cases capella : Fork.shapella ≤ fork <;>
        simp [LightClientHeader.names, sinceNames, SszFields.descs, capella],
     by simp [LightClientHeader.names],
     firstDuplicate_of_nodup _ LightClientHeader.names_nodup⟩
    (fun _ => rfl) (fun _ => rfl)

instance : NeZero (Nat.log2 (currentSyncCommitteeGindex fork)) :=
  ⟨by unfold currentSyncCommitteeGindex; split <;> decide⟩

instance : NeZero (Nat.log2 (nextSyncCommitteeGindex fork)) :=
  ⟨by unfold nextSyncCommitteeGindex; split <;> decide⟩

instance : NeZero (Nat.log2 (finalizedRootGindex fork)) :=
  ⟨by unfold finalizedRootGindex; split <;> decide⟩

instance : LawfulSszType (LightClientBootstrap preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType (LightClientUpdate preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType (LightClientFinalityUpdate preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType (LightClientOptimisticUpdate preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

/-- The finalized root and the sync committees sit at the indices that the state type gives.

This holds from Altair to the forks before Gloas, for both presets.

The root is the second field of the finalized checkpoint. -/
theorem lightClientGindices_eq {preset : Preset} {fork : Fork}
    (named : preset = .mainnet ∨ preset = .minimal) (altair : .altair ≤ fork)
    (beforeGloas : fork < .glamsterdam) :
    (stateGindex preset fork "finalized_checkpoint" [.position 1]).toOption =
        some (finalizedRootGindex fork) ∧
      (stateGindex preset fork "current_sync_committee" []).toOption =
        some (currentSyncCommitteeGindex fork) ∧
      (stateGindex preset fork "next_sync_committee" []).toOption =
        some (nextSyncCommitteeGindex fork) := by
  rcases named with rfl | rfl <;> cases fork <;> first
    | exact absurd altair (by decide) | exact absurd beforeGloas (by decide) | decide +kernel

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

end EthLib.Consensus
