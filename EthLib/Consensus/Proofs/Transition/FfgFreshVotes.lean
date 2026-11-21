module

public import EthLib.Consensus.Proofs.SlashingProtection
public import Mathlib.Data.Set.Image

/-!
# Proofs: honest votes with a fresh source add no slashable pair

A validator becomes slashable when it signs two attestation data that a slashing punishes.

That is a double vote, two different data for one target epoch, or a surround vote.

Take a validator whose votes so far hold no such pair.

Let it cast new votes, at most one for each target epoch, with sources that never go back.

Let each new vote also have a source at least, and a target after, those of every old vote.

Then the old and the new votes together still hold no such pair.

This is the last step of plausible liveness, Theorem 2 of Casper FFG §2.1.

The paper is [arXiv 1710.09437v4](https://arxiv.org/abs/1710.09437v4).
-/

@[expose] public section

namespace EthLib.Consensus

/-- The validator signed two data in the set that a slashing punishes.

Each element pairs a validator index with data that it signed. -/
def SlashableIn (votes : Set (ValidatorIndex × AttestationData)) (validator : ValidatorIndex) :
    Prop :=
  ∃ data1 data2, (validator, data1) ∈ votes ∧ (validator, data2) ∈ votes ∧
    isSlashableAttestationData data1 data2 = true

/-- New votes add no slashable pair to old ones.

The old votes hold no slashable pair of the validator.

Each new vote has a source at least, and a target after, those of each old vote.

The new votes have at most one data for each target epoch.

Among them, a later target never has an earlier source. -/
theorem not_slashableIn_union {old new : Set (ValidatorIndex × AttestationData)}
    {validator : ValidatorIndex} (safe : ¬SlashableIn old validator)
    (later : ∀ oldData newData, (validator, oldData) ∈ old → (validator, newData) ∈ new →
      oldData.source.epoch ≤ newData.source.epoch ∧ oldData.target.epoch < newData.target.epoch)
    (single : ∀ data1 data2, (validator, data1) ∈ new → (validator, data2) ∈ new →
      data1.target.epoch = data2.target.epoch → data1 = data2)
    (ordered : ∀ data1 data2, (validator, data1) ∈ new → (validator, data2) ∈ new →
      data1.target.epoch < data2.target.epoch → data1.source.epoch ≤ data2.source.epoch) :
    ¬SlashableIn (old ∪ new) validator := by
  rintro ⟨data1, data2, member1 | member1, member2 | member2, slashable⟩
  · exact safe ⟨data1, data2, member1, member2, slashable⟩
  · -- An old vote and a newer one are never slashable, in either order.
    obtain ⟨source, target⟩ := later data1 data2 member1 member2
    simp [(isSlashableAttestationData_eq_false_of_le_of_lt source target).1] at slashable
  · obtain ⟨source, target⟩ := later data2 data1 member2 member1
    simp [(isSlashableAttestationData_eq_false_of_le_of_lt source target).2] at slashable
  · -- Two new votes: a double vote breaks the single data per target, a surround the order.
    simp only [isSlashableAttestationData, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
      beq_iff_eq, decide_eq_true_eq] at slashable
    rcases slashable with ⟨distinct, targets⟩ | ⟨sources, targets⟩
    · exact distinct (single data1 data2 member1 member2 targets)
    · exact UInt64.not_lt.mpr (ordered data2 data1 member2 member1 targets) sources

/-- New votes with a fresh source add no slashable pair to old ones.

The bounds are a source epoch and a target epoch.

They may be the highest justified epoch, and an epoch after every earlier target.

Each old vote of the validator has a source at most the first bound and a target below the second.

That is an assumption of honesty: an honest validator votes only from a justified source.

Each new vote has a source at least the first bound and a target at least the second.

The new votes have at most one data for each target epoch.

Among them, a later target never has an earlier source. -/
theorem not_slashableIn_union_of_fresh {old new : Set (ValidatorIndex × AttestationData)}
    {validator : ValidatorIndex} {source target : Epoch} (safe : ¬SlashableIn old validator)
    (oldVotes : ∀ data, (validator, data) ∈ old →
      data.source.epoch ≤ source ∧ data.target.epoch < target)
    (newVotes : ∀ data, (validator, data) ∈ new →
      source ≤ data.source.epoch ∧ target ≤ data.target.epoch)
    (single : ∀ data1 data2, (validator, data1) ∈ new → (validator, data2) ∈ new →
      data1.target.epoch = data2.target.epoch → data1 = data2)
    (ordered : ∀ data1 data2, (validator, data1) ∈ new → (validator, data2) ∈ new →
      data1.target.epoch < data2.target.epoch → data1.source.epoch ≤ data2.source.epoch) :
    ¬SlashableIn (old ∪ new) validator :=
  not_slashableIn_union safe (fun oldData newData oldMember newMember =>
    ⟨UInt64.le_trans (oldVotes oldData oldMember).1 (newVotes newData newMember).1,
      UInt64.lt_of_lt_of_le (oldVotes oldData oldMember).2 (newVotes newData newMember).2⟩)
    single ordered

/-- Votes chosen by target epoch have one data for each target epoch.

The choice gives each epoch data whose target has that epoch. -/
theorem single_of_choice {validator : ValidatorIndex} {epochs : Set Epoch}
    {vote : Epoch → AttestationData} (targets : ∀ epoch, (vote epoch).target.epoch = epoch)
    (data1 data2 : AttestationData)
    (member1 : (validator, data1) ∈ (fun epoch => (validator, vote epoch)) '' epochs)
    (member2 : (validator, data2) ∈ (fun epoch => (validator, vote epoch)) '' epochs)
    (same : data1.target.epoch = data2.target.epoch) : data1 = data2 := by
  obtain ⟨epoch1, -, equal1⟩ := member1
  obtain ⟨epoch2, -, equal2⟩ := member2
  cases equal1
  cases equal2
  rw [targets, targets] at same
  rw [same]

/-- Votes chosen by target epoch have sources in order, when the choice does on those epochs. -/
theorem ordered_of_choice {validator : ValidatorIndex} {epochs : Set Epoch}
    {vote : Epoch → AttestationData} (targets : ∀ epoch, (vote epoch).target.epoch = epoch)
    (sources : ∀ epoch1 ∈ epochs, ∀ epoch2 ∈ epochs, epoch1 < epoch2 →
      (vote epoch1).source.epoch ≤ (vote epoch2).source.epoch)
    (data1 data2 : AttestationData)
    (member1 : (validator, data1) ∈ (fun epoch => (validator, vote epoch)) '' epochs)
    (member2 : (validator, data2) ∈ (fun epoch => (validator, vote epoch)) '' epochs)
    (before : data1.target.epoch < data2.target.epoch) :
    data1.source.epoch ≤ data2.source.epoch := by
  obtain ⟨epoch1, chosen1, equal1⟩ := member1
  obtain ⟨epoch2, chosen2, equal2⟩ := member2
  cases equal1
  cases equal2
  rw [targets, targets] at before
  exact sources epoch1 chosen1 epoch2 chosen2 before

/-- The hypotheses on fresh votes hold together, with one old vote and new votes for two epochs.

The old vote has source epoch 8 and target epoch 9.

The new votes have source epoch 9 and target epoch 10, and source epoch 10 and target epoch 11.

The bounds are 9 for the source and 10 for the target. -/
theorem exists_fresh_votes (validator : ValidatorIndex) (root : Root) :
    ∃ old new : Set (ValidatorIndex × AttestationData),
      (validator, ⟨0, 0, root, ⟨8, root⟩, ⟨9, root⟩⟩) ∈ old ∧
      (validator, ⟨0, 0, root, ⟨9, root⟩, ⟨10, root⟩⟩) ∈ new ∧
      (validator, ⟨0, 0, root, ⟨10, root⟩, ⟨11, root⟩⟩) ∈ new ∧
      ¬SlashableIn old validator ∧
      (∀ data, (validator, data) ∈ old → data.source.epoch ≤ 9 ∧ data.target.epoch < 10) ∧
      (∀ data, (validator, data) ∈ new → 9 ≤ data.source.epoch ∧ 10 ≤ data.target.epoch) ∧
      (∀ data1 data2, (validator, data1) ∈ new → (validator, data2) ∈ new →
        data1.target.epoch = data2.target.epoch → data1 = data2) ∧
      (∀ data1 data2, (validator, data1) ∈ new → (validator, data2) ∈ new →
        data1.target.epoch < data2.target.epoch → data1.source.epoch ≤ data2.source.epoch) := by
  -- The new vote of an epoch has the epoch before it as source.
  let vote : Epoch → AttestationData := fun epoch => ⟨0, 0, root, ⟨epoch - 1, root⟩, ⟨epoch, root⟩⟩
  let old : Set (ValidatorIndex × AttestationData) :=
    {(validator, ⟨0, 0, root, ⟨8, root⟩, ⟨9, root⟩⟩)}
  have targets : ∀ epoch, (vote epoch).target.epoch = epoch := fun _ => rfl
  refine ⟨old, (fun epoch => (validator, vote epoch)) '' {10, 11}, Set.mem_singleton _,
    ⟨10, by simp, rfl⟩, ⟨11, by simp, rfl⟩, ?_, ?_, ?_, single_of_choice targets, ?_⟩
  · rintro ⟨data1, data2, member1, member2, slashable⟩
    simp only [old, Set.mem_singleton_iff, Prod.mk.injEq, true_and] at member1 member2
    subst member1 member2
    simp [isSlashableAttestationData] at slashable
  · intro data member
    simp only [old, Set.mem_singleton_iff, Prod.mk.injEq, true_and] at member
    subst member
    simp
  · rintro data ⟨epoch, member, equal⟩
    cases equal
    rcases member with rfl | rfl <;> simp [vote]
  · rintro data1 data2 ⟨epoch1, member1, equal1⟩ ⟨epoch2, member2, equal2⟩ before
    cases equal1
    cases equal2
    rcases member1 with rfl | rfl <;> rcases member2 with rfl | rfl <;> revert before <;>
      simp [vote]

end EthLib.Consensus
