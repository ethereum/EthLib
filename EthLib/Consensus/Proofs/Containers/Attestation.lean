module

public import EthLib.Consensus.Containers.Attestation
public import EthLib.Consensus.Proofs.Containers.Misc
public import EthLib.Serialization.Proofs.Ssz.Typed.Since
public import EthLib.Serialization.Proofs.Ssz.Type.Legality

/-!
# Proofs: the attestation containers are lawful at every fork

Each container has distinct field names at every fork, and converts to and from its fields.

So its bytes decode back to it, at every fork.

Before Electra an attestation covers one committee, as it did at Phase 0.

The bit vector of committees needs at least one committee in a slot.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- Before Electra, an attestation covers at most the validators of one committee. -/
theorem maxAttesters_of_lt (before : fork < .pectra) :
    maxAttesters preset fork = preset.MAX_VALIDATORS_PER_COMMITTEE.toNat := by
  simp [maxAttesters, show ¬Fork.pectra ≤ fork from Nat.not_le.mpr before]

/-- From Electra, an attestation covers at most the validators of all committees of a slot. -/
theorem maxAttesters_of_le (after : .pectra ≤ fork) :
    maxAttesters preset fork =
      preset.MAX_VALIDATORS_PER_COMMITTEE.toNat * preset.MAX_COMMITTEES_PER_SLOT.toNat := by
  simp [maxAttesters, after]

/-- The field names of an attestation are distinct at every fork. -/
theorem Attestation.names_nodup : (Attestation.names fork).Nodup := by
  have all : (["aggregation_bits", "data", "signature", "committee_bits"] : List String).Nodup :=
    by decide
  exact all.sublist ((List.Sublist.refl _).append (sinceNames_sublist _))

instance [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] :
    LawfulSszType (Attestation preset fork) :=
  .container
    ⟨by
      by_cases electra : Fork.pectra ≤ fork <;>
        simp [Attestation.names, sinceNames, SszFields.descs, electra],
     by simp [Attestation.names],
     firstDuplicate_of_nodup _ Attestation.names_nodup⟩
    (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType (IndexedAttestation preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType (AttesterSlashing preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] :
    LawfulSszType (AggregateAndProof preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] :
    LawfulSszType (SignedAggregateAndProof preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType SingleAttestation := .container (by decide) (fun _ => rfl) (fun _ => rfl)

end EthLib.Consensus
