module

public import EthLib.Consensus.Containers.Block
public import EthLib.Consensus.Proofs.Containers.Attestation
public import EthLib.Consensus.Proofs.Containers.Bid
public import EthLib.Consensus.Proofs.Containers.Builder
public import EthLib.Consensus.Proofs.Containers.Execution
public import EthLib.Consensus.Proofs.Containers.Requests
public import EthLib.Consensus.Proofs.Containers.SyncCommittee
public import EthLib.Serialization.Proofs.Ssz.Type.CompatibilityIndices
public import EthLib.Serialization.Ssz.Typed.Gindex

/-!
# Proofs: the beacon block is lawful at every fork

The body has distinct field names at every fork, and converts to and from its fields.

So the body, the block and the signed block decode back from their bytes, at every fork.

At Fulu the body has the thirteen fields of Electra, and at Gloas the thirteen fields of Gloas.

At Heze the body has eleven of the thirteen places of Gloas, and two gaps.

Each field that Heze keeps sits at the place it has at Gloas.

The vectors whose length comes from the preset need that length to be positive.

The genesis block holds the state root, and the defaults of every other field.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- The genesis block holds the state root, and zero in its slot, proposer and parent root.

Its body is the one that the default value of the body type stands for. -/
theorem BeaconBlock.genesis_fields {stateRoot : Root} {block : BeaconBlock preset fork}
    (built : BeaconBlock.genesis preset fork stateRoot = .ok block) :
    block.slot = 0 ∧ block.proposerIndex = 0 ∧ block.parentRoot = Vector.replicate 32 0 ∧
      block.stateRoot = stateRoot ∧
      ∃ value, (SszType.desc (BeaconBlockBody preset fork)).default = .ok value ∧
        SszType.ofValue value = .ok block.body := by
  unfold BeaconBlock.genesis at built
  simp only [bind_ok_iff] at built
  obtain ⟨value, isDefault, body, decoded, built⟩ := built
  cases built
  exact ⟨rfl, rfl, rfl, rfl, value, isDefault, decoded⟩

/-- The field names of a body are distinct at every fork. -/
theorem BeaconBlockBody.names_nodup : (BeaconBlockBody.names fork).Nodup := by
  have all : (["randao_reveal", "eth1_data", "graffiti", "proposer_slashings",
      "attester_slashings", "attestations", "deposits", "voluntary_exits", "sync_aggregate",
      "execution_payload", "bls_to_execution_changes", "blob_kzg_commitments",
      "execution_requests", "signed_execution_payload_bid", "payload_attestations",
      "parent_execution_requests"] : List String).Nodup := by decide
  refine all.sublist ?_
  unfold BeaconBlockBody.names
  exact ((((((((((List.Sublist.refl _).append (untilNames_sublist _)).append
    (List.Sublist.refl _)).append (untilNames_sublist _)).append (List.Sublist.refl _)).append
    (sinceNames_sublist _)).append (duringNames_sublist _)).append (sinceNames_sublist _)).append
    (duringNames_sublist _)).append (duringNames_sublist _)).append (sinceNames_sublist _)

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

/-- At Heze, the vote on the deposit contract and the deposits leave the body. -/
theorem BeaconBlockBody.names_hegota :
    BeaconBlockBody.names .hegota =
      ["randao_reveal", "graffiti", "proposer_slashings", "attester_slashings", "attestations",
        "voluntary_exits", "sync_aggregate", "bls_to_execution_changes",
        "signed_execution_payload_bid", "payload_attestations", "parent_execution_requests"] := by
  decide

/-- The place of a named field in the tree of a progressive container, if it has that field.

The layout and the names are those of the container. -/
def fieldPlace (active : List Bool) (names : List String) (name : String) : Option Nat :=
  if name ∈ names then activePosition active (names.idxOf name) else none

/-- Every field of a body at Heze sits at the place it has at Gloas.

So a proof of one of these fields against a Gloas body root keeps its path at Heze. -/
theorem BeaconBlockBody.fieldPlace_hegota :
    ∀ name ∈ BeaconBlockBody.names .hegota,
      fieldPlace (BeaconBlockBody.activeFields .hegota) (BeaconBlockBody.names .hegota) name =
        fieldPlace (BeaconBlockBody.activeFields .glamsterdam)
          (BeaconBlockBody.names .glamsterdam) name := by
  decide

/-- At Gloas, the vote on the deposit contract and the deposits sit at places 1 and 6.

Those places are the gaps of the Heze layout. -/
theorem BeaconBlockBody.fieldPlace_removed_hegota :
    fieldPlace (BeaconBlockBody.activeFields .glamsterdam) (BeaconBlockBody.names .glamsterdam)
        "eth1_data" = some 1 ∧
      fieldPlace (BeaconBlockBody.activeFields .glamsterdam)
        (BeaconBlockBody.names .glamsterdam) "deposits" = some 6 ∧
      (BeaconBlockBody.activeFields .hegota)[1]? = some false ∧
      (BeaconBlockBody.activeFields .hegota)[6]? = some false := by
  decide

/-- Two progressive containers that put a named field at one place address it at one node.

Each container has as many field types as names. -/
theorem getGeneralizedIndex_eq_of_fieldPlace {leftActive rightActive : List Bool}
    {leftNames rightNames : List String} {leftFields rightFields : List Desc} {name : String}
    {place : Nat} (leftSized : leftFields.length = leftNames.length)
    (rightSized : rightFields.length = rightNames.length)
    (leftPlaced : fieldPlace leftActive leftNames name = some place)
    (rightPlaced : fieldPlace rightActive rightNames name = some place) :
    getGeneralizedIndex (.progressiveContainer leftActive leftNames leftFields)
        [.position (leftNames.idxOf name)] =
      getGeneralizedIndex (.progressiveContainer rightActive rightNames rightFields)
        [.position (rightNames.idxOf name)] := by
  unfold fieldPlace at leftPlaced rightPlaced
  split at leftPlaced <;> split at rightPlaced <;> try contradiction
  rename_i leftIn rightIn
  have leftBound : leftNames.idxOf name < leftFields.length :=
    leftSized ▸ List.idxOf_lt_length_of_mem leftIn
  have rightBound : rightNames.idxOf name < rightFields.length :=
    rightSized ▸ List.idxOf_lt_length_of_mem rightIn
  rw [progressiveContainer_field_index (position := place) (List.getElem?_eq_getElem leftBound)
      (by simp [layoutPosition, leftPlaced]),
    progressiveContainer_field_index (position := place) (List.getElem?_eq_getElem rightBound)
      (by simp [layoutPosition, rightPlaced])]

/-- Every field of a body at Heze has the generalized index it has at Gloas, at every preset. -/
theorem BeaconBlockBody.getGeneralizedIndex_hegota {name : String}
    (kept : name ∈ BeaconBlockBody.names .hegota) :
    SszType.getGeneralizedIndex (BeaconBlockBody preset .hegota)
        [.position ((BeaconBlockBody.names .hegota).idxOf name)] =
      SszType.getGeneralizedIndex (BeaconBlockBody preset .glamsterdam)
        [.position ((BeaconBlockBody.names .glamsterdam).idxOf name)] := by
  have placed : ∀ name ∈ BeaconBlockBody.names .hegota,
      (fieldPlace (BeaconBlockBody.activeFields .hegota) (BeaconBlockBody.names .hegota)
        name).isSome := by
    decide
  obtain ⟨place, found⟩ := Option.isSome_iff_exists.mp (placed name kept)
  unfold SszType.getGeneralizedIndex
  refine getGeneralizedIndex_eq_of_fieldPlace (leftActive := BeaconBlockBody.activeFields .hegota)
    (rightActive := BeaconBlockBody.activeFields .glamsterdam) ?_ ?_ found
    ((BeaconBlockBody.fieldPlace_hegota name kept) ▸ found) <;> rfl

variable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]

instance : LawfulSszType (BeaconBlockBody preset fork) :=
  .forkContainer
    (fun gloas => by
      have altair : Fork.altair ≤ fork := Nat.le_trans (by decide) gloas
      have capella : Fork.shapella ≤ fork := Nat.le_trans (by decide) gloas
      by_cases heze : Fork.hegota ≤ fork
      · exact ⟨by simp [BeaconBlockBody.activeFields, heze],
          by simp [BeaconBlockBody.activeFields, heze, maxActiveFields], by
          simp [BeaconBlockBody.activeFields, SszFields.descs, altair, capella, gloas, heze,
            not_lt_of_switch gloas, not_lt_of_switch heze]⟩
      · exact ⟨by simp [BeaconBlockBody.activeFields, heze],
          by simp [BeaconBlockBody.activeFields, heze, maxActiveFields], by
          simp [BeaconBlockBody.activeFields, SszFields.descs, altair, capella, gloas, heze,
            not_lt_of_switch gloas, lt_of_not_switch heze]⟩)
    ⟨by
      by_cases altair : Fork.altair ≤ fork <;> by_cases bellatrix : Fork.bellatrix ≤ fork <;>
        by_cases capella : Fork.shapella ≤ fork <;> by_cases deneb : Fork.dencun ≤ fork <;>
        by_cases electra : Fork.pectra ≤ fork <;> by_cases gloas : Fork.glamsterdam ≤ fork <;>
        by_cases heze : Fork.hegota ≤ fork <;>
        simp [BeaconBlockBody.names, sinceNames, untilNames, duringNames, SszFields.descs,
          altair, bellatrix, capella, deneb, electra, gloas, heze, not_lt_of_switch,
          lt_of_not_switch],
     by simp [BeaconBlockBody.names],
     firstDuplicate_of_nodup _ BeaconBlockBody.names_nodup⟩
    (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType (BeaconBlock preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType (SignedBeaconBlock preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

end EthLib.Consensus
