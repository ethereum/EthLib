module

public import EthLib.Consensus.Containers.SyncCommittee
public import EthLib.Consensus.Proofs.Containers.Misc

/-!
# Proofs: the sync committee containers are lawful

Each container has distinct field names, and converts to and from its fields.

So its bytes decode back to it.

A vector or bit vector whose length comes from the preset needs that length to be positive.
-/

@[expose] public section

namespace EthLib.Consensus

open Serialization.Ssz

variable {preset : Preset}

instance [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] : LawfulSszType (SyncCommittee preset) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] : LawfulSszType (SyncAggregate preset) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType SyncCommitteeMessage :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance [NeZero (syncSubcommitteeSize preset)] :
    LawfulSszType (SyncCommitteeContribution preset) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance [NeZero (syncSubcommitteeSize preset)] : LawfulSszType (ContributionAndProof preset) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance [NeZero (syncSubcommitteeSize preset)] :
    LawfulSszType (SignedContributionAndProof preset) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType SyncAggregatorSelectionData :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

end EthLib.Consensus
