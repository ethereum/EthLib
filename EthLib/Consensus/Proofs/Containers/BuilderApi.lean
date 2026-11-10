module

public import EthLib.Consensus.Containers.BuilderApi
public import EthLib.Consensus.Proofs.Containers.Block

/-!
# Proofs: the containers of the Builder API are lawful at every fork

The bid and the blinded body have distinct field names at every fork.

With distinct field names, every container of the Builder API decodes back from its bytes.

The vectors whose length comes from the preset need that length to be positive.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- The field names of a bid are distinct at every fork. -/
theorem BuilderBid.names_nodup : (BuilderBid.names fork).Nodup := by
  have all : (["header", "blob_kzg_commitments", "execution_requests", "value", "pubkey"] :
      List String).Nodup := by decide
  refine all.sublist ?_
  unfold BuilderBid.names
  exact (((List.Sublist.refl _).append (sinceNames_sublist _)).append
    (sinceNames_sublist _)).append (List.Sublist.refl _)

/-- The field names of a blinded body are distinct at every fork. -/
theorem BlindedBeaconBlockBody.names_nodup : (BlindedBeaconBlockBody.names fork).Nodup := by
  have all : (["randao_reveal", "eth1_data", "graffiti", "proposer_slashings",
      "attester_slashings", "attestations", "deposits", "voluntary_exits", "sync_aggregate",
      "execution_payload_header", "bls_to_execution_changes", "blob_kzg_commitments",
      "execution_requests"] : List String).Nodup := by decide
  refine all.sublist ?_
  unfold BlindedBeaconBlockBody.names
  exact (((((((((List.Sublist.refl _).append (untilNames_sublist _)).append
    (List.Sublist.refl _)).append (untilNames_sublist _)).append (List.Sublist.refl _)).append
    (sinceNames_sublist _)).append (duringNames_sublist _)).append (sinceNames_sublist _)).append
    (duringNames_sublist _)).append (duringNames_sublist _)

instance : LawfulSszType ValidatorRegistrationV1 :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType SignedValidatorRegistrationV1 :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType BuilderRequestAuth :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType SignedBuilderRequestAuth :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType BuilderPreferences :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType BuilderPreferencesRequest :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

variable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat]

instance : LawfulSszType (BuilderBid preset fork) :=
  .container
    ⟨by
      by_cases deneb : Fork.dencun ≤ fork <;> by_cases electra : Fork.pectra ≤ fork <;>
        simp [BuilderBid.names, sinceNames, SszFields.descs, deneb, electra],
     by simp [BuilderBid.names],
     firstDuplicate_of_nodup _ BuilderBid.names_nodup⟩
    (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType (SignedBuilderBid preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType (BlindedBeaconBlockBody preset fork) :=
  .container
    ⟨by
      by_cases altair : Fork.altair ≤ fork <;> by_cases bellatrix : Fork.bellatrix ≤ fork <;>
        by_cases capella : Fork.shapella ≤ fork <;> by_cases deneb : Fork.dencun ≤ fork <;>
        by_cases electra : Fork.pectra ≤ fork <;> by_cases gloas : Fork.glamsterdam ≤ fork <;>
        by_cases heze : Fork.hegota ≤ fork <;>
        simp [BlindedBeaconBlockBody.names, sinceNames, untilNames, duringNames,
          SszFields.descs, altair, bellatrix, capella, deneb, electra, gloas, heze,
          not_lt_of_switch, lt_of_not_switch],
     by simp [BlindedBeaconBlockBody.names],
     firstDuplicate_of_nodup _ BlindedBeaconBlockBody.names_nodup⟩
    (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType (BlindedBeaconBlock preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType (SignedBlindedBeaconBlock preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

end EthLib.Consensus
