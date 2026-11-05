module

public import EthLib.Consensus.Containers.Attestation
public import EthLib.Consensus.Proofs.Containers.Misc
public import EthLib.Serialization.Proofs.Ssz.Typed.ForkKind
public import EthLib.Serialization.Proofs.Ssz.Typed.Since
public import EthLib.Serialization.Proofs.Ssz.Type.Legality

/-!
# Proofs: the attestation containers are lawful at every fork

Each container has distinct field names at every fork, and converts to and from its fields.

So its bytes decode back to it, at every fork.

Before Electra an attestation covers one committee, as it did at Phase 0.

The bit vector of committees needs at least one committee in a slot.

From Gloas both progressive layouts hold every field, so they are lawful too.

The upgrade of each container to Gloas keeps all its contents, so it loses nothing.
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
  .forkContainer
    (fun gloas => by
      have electra : Fork.pectra ≤ fork := Nat.le_trans (by decide) gloas
      exact ⟨rfl, by decide, by simp [Attestation.activeFields, SszFields.descs, electra]⟩)
    ⟨by
      by_cases electra : Fork.pectra ≤ fork <;>
        simp [Attestation.names, sinceNames, SszFields.descs, electra],
     by simp [Attestation.names],
     firstDuplicate_of_nodup _ Attestation.names_nodup⟩
    (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType (IndexedAttestation preset fork) :=
  .forkContainer (fun _ => ⟨rfl, by decide, rfl⟩) ⟨rfl, by simp, by decide⟩ (fun _ => rfl)
    (fun _ => rfl)

instance : LawfulSszType (AttesterSlashing preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] :
    LawfulSszType (AggregateAndProof preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] :
    LawfulSszType (SignedAggregateAndProof preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType SingleAttestation := .container (by decide) (fun _ => rfl) (fun _ => rfl)

/-- The upgrade of an attestation to Gloas keeps its bits, data, signature and committee bits. -/
theorem Attestation.upgradeToGloas_spec (pre : Attestation preset .fusaka) :
    pre.upgradeToGloas.aggregationBits.bits = pre.aggregationBits.bits ∧
      pre.upgradeToGloas.data = pre.data ∧ pre.upgradeToGloas.signature = pre.signature ∧
      pre.upgradeToGloas.committeeBits (by decide) = pre.committeeBits (by decide) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Two attestations with one upgrade are equal, so the upgrade loses nothing. -/
theorem Attestation.upgradeToGloas_injective :
    Function.Injective (Attestation.upgradeToGloas (preset := preset)) := by
  intro a b same
  have bits := congrArg (fun x => x.aggregationBits.bits) same
  have data := congrArg Attestation.data same
  have signature := congrArg Attestation.signature same
  have committees := congrArg (fun x => x.committeeBits (by decide)) same
  obtain ⟨⟨bitsA, boundA⟩, dataA, signatureA, committeesA⟩ := a
  obtain ⟨⟨bitsB, boundB⟩, dataB, signatureB, committeesB⟩ := b
  simp only [Attestation.upgradeToGloas] at bits data signature committees
  subst bits data signature
  have : committeesA = committeesB := funext fun _ => committees
  subst this
  rfl

/-- The upgrade of an indexed attestation to Gloas keeps its indices, data and signature. -/
theorem IndexedAttestation.upgradeToGloas_spec (pre : IndexedAttestation preset .fusaka) :
    pre.upgradeToGloas.attestingIndices.data = pre.attestingIndices.data ∧
      pre.upgradeToGloas.data = pre.data ∧ pre.upgradeToGloas.signature = pre.signature :=
  ⟨rfl, rfl, rfl⟩

/-- Two indexed attestations with one upgrade are equal, so the upgrade loses nothing. -/
theorem IndexedAttestation.upgradeToGloas_injective :
    Function.Injective (IndexedAttestation.upgradeToGloas (preset := preset)) := by
  intro a b same
  obtain ⟨⟨indicesA, boundA⟩, dataA, signatureA⟩ := a
  obtain ⟨⟨indicesB, boundB⟩, dataB, signatureB⟩ := b
  simp only [IndexedAttestation.upgradeToGloas, IndexedAttestation.mk.injEq,
    ForkList.mk.injEq] at same
  obtain ⟨indices, data, signature⟩ := same
  subst indices data signature
  rfl

/-- The upgrade of an attester slashing to Gloas upgrades each of its two attestations. -/
theorem AttesterSlashing.upgradeToGloas_injective :
    Function.Injective (AttesterSlashing.upgradeToGloas (preset := preset)) := by
  intro a b same
  simp only [AttesterSlashing.upgradeToGloas, AttesterSlashing.mk.injEq] at same
  cases a
  cases b
  simp only [AttesterSlashing.mk.injEq]
  exact ⟨IndexedAttestation.upgradeToGloas_injective same.1,
    IndexedAttestation.upgradeToGloas_injective same.2⟩

end EthLib.Consensus
