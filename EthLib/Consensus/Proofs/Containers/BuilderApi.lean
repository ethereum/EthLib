module

public import EthLib.Consensus.Containers.BuilderApi
public import EthLib.Consensus.Proofs.Containers.Block
public import EthLib.Consensus.Proofs.DataAvailability.Blob
public import EthLib.Serialization.Proofs.Ssz.Typed.Choice

/-!
# Proofs: the containers of the Builder API are lawful at every fork

The bid, the blinded body, the blobs bundle and a payload with its bundle have distinct fields.

With distinct field names, every container of the Builder API decodes back from its bytes.

The payload that a builder reveals reads as the form of its fork, and is lawful at every fork.

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

/-- The field names of a blobs bundle are distinct. -/
theorem BuilderBlobsBundle.names_nodup : BuilderBlobsBundle.names.Nodup := by decide

/-- The field names of a payload with its blobs bundle are distinct. -/
theorem ExecutionPayloadAndBlobsBundle.names_nodup :
    ExecutionPayloadAndBlobsBundle.names.Nodup := by
  decide

instance : LawfulSszType (BuilderBlobsBundle preset fork) :=
  .container ⟨rfl, by simp [BuilderBlobsBundle.names],
    firstDuplicate_of_nodup _ BuilderBlobsBundle.names_nodup⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType (ExecutionPayloadAndBlobsBundle preset fork) :=
  .container ⟨rfl, by simp [ExecutionPayloadAndBlobsBundle.names],
    firstDuplicate_of_nodup _ ExecutionPayloadAndBlobsBundle.names_nodup⟩
    (fun _ => rfl) (fun _ => rfl)

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] in
/-- From Deneb, the revealed bytes read exactly as a payload with its blobs bundle. -/
theorem RevealedPayload.deserialize_of_deneb (deneb : Fork.dencun ≤ fork) (data : ByteArray) :
    SszType.deserialize (RevealedPayload preset fork) data =
      RevealedPayload.ofBundle deneb <$>
        SszType.deserialize (ExecutionPayloadAndBlobsBundle preset fork) data := by
  have key : ∀ (d : Decidable (Fork.dencun ≤ fork)) (h : Fork.dencun ≤ fork),
      @SszType.decode _ (@instSszTypeIte _ d _ _ _ _) data =
        (fun b => cast (@ite_eq_left _ d h _ _ (ExecutionPayload preset fork)).symm b) <$>
          SszType.decode (α := ExecutionPayloadAndBlobsBundle preset fork) data := by
    intro d h
    cases d
    · contradiction
    · exact (id_map _).symm
  exact key _ deneb

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] in
/-- Before Deneb, the revealed bytes read exactly as a payload alone. -/
theorem RevealedPayload.deserialize_of_not_deneb (early : ¬Fork.dencun ≤ fork)
    (data : ByteArray) :
    SszType.deserialize (RevealedPayload preset fork) data =
      RevealedPayload.ofPayload early <$>
        SszType.deserialize (ExecutionPayload preset fork) data := by
  have key : ∀ (d : Decidable (Fork.dencun ≤ fork)) (h : ¬Fork.dencun ≤ fork),
      @SszType.decode _ (@instSszTypeIte _ d _ _ _ _) data =
        (fun p => cast (@ite_eq_right _ d h _ (ExecutionPayloadAndBlobsBundle preset fork) _).symm
          p) <$> SszType.decode (α := ExecutionPayload preset fork) data := by
    intro d h
    cases d
    · exact (id_map _).symm
    · contradiction
  exact key _ early

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] in
/-- The payload of a revealed payload with its bundle is the payload of the bundle. -/
theorem RevealedPayload.executionPayload_ofBundle (deneb : Fork.dencun ≤ fork)
    (bundle : ExecutionPayloadAndBlobsBundle preset fork) :
    (RevealedPayload.ofBundle deneb bundle).executionPayload = bundle.executionPayload := by
  unfold RevealedPayload.executionPayload RevealedPayload.ofBundle
  rw [dite_eq_left deneb]
  dsimp only
  exact congrArg (·.executionPayload) ((cast_cast _ _ bundle).trans (cast_eq _ bundle))

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] in
/-- The payload of a revealed payload alone is that payload. -/
theorem RevealedPayload.executionPayload_ofPayload (early : ¬Fork.dencun ≤ fork)
    (payload : ExecutionPayload preset fork) :
    (RevealedPayload.ofPayload early payload).executionPayload = payload := by
  unfold RevealedPayload.executionPayload RevealedPayload.ofPayload
  rw [dite_eq_right early]
  exact (cast_cast _ _ payload).trans (cast_eq _ payload)

/-- The payload that a builder reveals is lawful at every fork, as each of its two forms is. -/
instance : LawfulSszType (RevealedPayload preset fork) :=
  inferInstanceAs (LawfulSszType (if .dencun ≤ fork then _ else _))

end EthLib.Consensus
