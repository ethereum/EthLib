module

public import EthLib.Consensus.Containers.Block
public import EthLib.Consensus.Proofs.Containers.Attestation
public import EthLib.Consensus.Proofs.Containers.Bid
public import EthLib.Consensus.Proofs.Containers.Builder
public import EthLib.Consensus.Proofs.Containers.Execution
public import EthLib.Consensus.Proofs.Containers.Requests
public import EthLib.Consensus.Proofs.Containers.SyncCommittee

/-!
# Proofs: the beacon block is lawful at every fork

The body has distinct field names at every fork, and converts to and from its fields.

So the body, the block and the signed block decode back from their bytes, at every fork.

At Fulu the body has the thirteen fields of Electra, and at Gloas the thirteen fields of Gloas.

The vectors whose length comes from the preset need that length to be positive.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- The field names of a body are distinct at every fork. -/
theorem BeaconBlockBody.names_nodup : (BeaconBlockBody.names fork).Nodup := by
  have all : (["randao_reveal", "eth1_data", "graffiti", "proposer_slashings",
      "attester_slashings", "attestations", "deposits", "voluntary_exits", "sync_aggregate",
      "execution_payload", "bls_to_execution_changes", "blob_kzg_commitments",
      "execution_requests", "signed_execution_payload_bid", "payload_attestations",
      "parent_execution_requests"] : List String).Nodup := by decide
  refine all.sublist ?_
  unfold BeaconBlockBody.names
  exact ((((((List.Sublist.refl _).append (sinceNames_sublist _)).append
    (duringNames_sublist _)).append (sinceNames_sublist _)).append (duringNames_sublist _)).append
    (duringNames_sublist _)).append (sinceNames_sublist _)

/-- At Fulu, the fields of a body are those of Electra, in their order. -/
theorem BeaconBlockBody.names_fusaka :
    BeaconBlockBody.names .fusaka =
      ["randao_reveal", "eth1_data", "graffiti", "proposer_slashings", "attester_slashings",
        "attestations", "deposits", "voluntary_exits", "sync_aggregate", "execution_payload",
        "bls_to_execution_changes", "blob_kzg_commitments", "execution_requests"] := by
  decide

/-- At Gloas, the payload, its commitments and its requests give way to the bid and two lists. -/
theorem BeaconBlockBody.names_glamsterdam :
    BeaconBlockBody.names .glamsterdam =
      ["randao_reveal", "eth1_data", "graffiti", "proposer_slashings", "attester_slashings",
        "attestations", "deposits", "voluntary_exits", "sync_aggregate",
        "bls_to_execution_changes", "signed_execution_payload_bid", "payload_attestations",
        "parent_execution_requests"] := by
  decide

variable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]

instance : LawfulSszType (BeaconBlockBody preset fork) :=
  .forkContainer
    (fun gloas => by
      have altair : Fork.altair ≤ fork := Nat.le_trans (by decide) gloas
      have capella : Fork.shapella ≤ fork := Nat.le_trans (by decide) gloas
      exact ⟨rfl, by decide, by
        simp [BeaconBlockBody.activeFields, SszFields.descs, altair, capella, gloas,
          not_lt_of_switch gloas]⟩)
    ⟨by
      by_cases altair : Fork.altair ≤ fork <;> by_cases bellatrix : Fork.bellatrix ≤ fork <;>
        by_cases capella : Fork.shapella ≤ fork <;> by_cases deneb : Fork.dencun ≤ fork <;>
        by_cases electra : Fork.pectra ≤ fork <;> by_cases gloas : Fork.glamsterdam ≤ fork <;>
        simp [BeaconBlockBody.names, sinceNames, duringNames, SszFields.descs, altair,
          bellatrix, capella, deneb, electra, gloas, not_lt_of_switch, lt_of_not_switch],
     by simp [BeaconBlockBody.names],
     firstDuplicate_of_nodup _ BeaconBlockBody.names_nodup⟩
    (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType (BeaconBlock preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType (SignedBeaconBlock preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

end EthLib.Consensus
