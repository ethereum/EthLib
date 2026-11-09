module

public import EthLib.Consensus.Proofs.Models.Ffg.AccountableSafety
public import EthLib.Consensus.Transition.Block

/-!
# Proofs: slashable attestation data and the Casper FFG model

An attestation carries a Casper FFG vote: the link from its source checkpoint to its target.

A map from roots to blocks turns each checkpoint into a checkpoint of the model.

Each pair of votes that breaks a slashing condition of the model is slashable in the beacon chain.

The beacon chain slashes two more kinds of pairs, so the converse fails.

The first kind is two different attestations with one source and one target.

They differ in their slot, their committee or their head, and they make one vote of the model.

The second kind is a surround whose inner vote does not go forward in epochs.

The model counts a surround only when the inner link goes forward.

Casper FFG §2 states its second slashing condition with that order of the four epochs.

The paper is [arXiv 1710.09437v4](https://arxiv.org/abs/1710.09437v4).

With these two kinds added, and an injective map, the two rules agree exactly.

Accountable safety then holds for signed attestations.

Two conflicting finalized checkpoints make validators with one third of the stake slashable.

Each of them signed two attestations that an attester slashing can hold.
-/

@[expose] public section

namespace EthLib.Consensus

open Models Models.Ffg

variable {ν β : Type*}

/-- The checkpoint of the model: the block of the root, with the epoch as a natural number. -/
def Checkpoint.toFfg (block : Root → β) (c : Checkpoint) : Models.Ffg.Checkpoint β :=
  ⟨block c.root, c.epoch.toNat⟩

/-- The vote of the model that a validator casts when it signs attestation data.

It links the source checkpoint of the data to its target checkpoint. -/
def AttestationData.toFfgVote (block : Root → β) (validator : ν) (data : AttestationData) :
    Vote ν β :=
  ⟨validator, data.source.toFfg block, data.target.toFfg block⟩

/-- The votes of the model that a set of signed attestation data casts.

Each element pairs a validator with data that it signed. -/
def ffgVotes (block : Root → β) (signed : Set (ν × AttestationData)) : Set (Vote ν β) :=
  (fun signer => signer.2.toFfgVote block signer.1) '' signed

/-- Two different attestation data with one source and one target.

They make one vote of the model, but the beacon chain slashes them as a double vote. -/
def SameLinkDoubleVote (data1 data2 : AttestationData) : Prop :=
  data1 ≠ data2 ∧ data1.source = data2.source ∧ data1.target = data2.target

/-- The first data surrounds the second, whose target epoch is not after its source epoch.

The beacon chain slashes such a pair, but the model does not. -/
def BackwardSurroundVote (data1 data2 : AttestationData) : Prop :=
  data1.source.epoch < data2.source.epoch ∧ data2.target.epoch ≤ data2.source.epoch ∧
    data2.target.epoch < data1.target.epoch

@[simp]
theorem Checkpoint.toFfg_epoch (block : Root → β) (c : Checkpoint) :
    (c.toFfg block).epoch = c.epoch.toNat :=
  rfl

/-- An injective map from roots to blocks keeps two different checkpoints apart. -/
theorem Checkpoint.toFfg_injective {block : Root → β} (injective : Function.Injective block) :
    Function.Injective (Checkpoint.toFfg block) := by
  intro c₁ c₂ equal
  simp only [Checkpoint.toFfg, Models.Ffg.Checkpoint.mk.injEq] at equal
  obtain ⟨roots, epochs⟩ := equal
  cases c₁
  cases c₂
  simp_all [injective.eq_iff, UInt64.toNat_inj]

/-- Each double vote or surround vote of the model is slashable in the beacon chain.

This holds for every validator and every map from roots to blocks. -/
theorem isSlashableAttestationData_of_ffg {block : Root → β} {validator : ν}
    {data1 data2 : AttestationData}
    (slashable : DoubleVote (data1.toFfgVote block validator) (data2.toFfgVote block validator) ∨
      SurroundVote (data1.toFfgVote block validator) (data2.toFfgVote block validator)) :
    isSlashableAttestationData data1 data2 = true := by
  simp only [isSlashableAttestationData, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq, decide_eq_true_eq]
  rcases slashable with ⟨distinct, epochs⟩ | ⟨sources, -, targets⟩
  · refine .inl ⟨fun equal => distinct (by rw [equal]), ?_⟩
    simpa [AttestationData.toFfgVote, Checkpoint.toFfg, UInt64.toNat_inj] using epochs
  · simp only [AttestationData.toFfgVote, Checkpoint.toFfg] at sources targets
    exact .inr ⟨UInt64.lt_iff_toNat_lt.mpr sources, UInt64.lt_iff_toNat_lt.mpr targets⟩

/-- The beacon chain slashes exactly four kinds of pairs.

They are the double votes and surround votes of the model, and the two kinds that it does not see.

The map from roots to blocks must be injective.

Then two checkpoints of one epoch with two roots stay apart. -/
theorem isSlashableAttestationData_iff_ffg {block : Root → β}
    (injective : Function.Injective block) (validator : ν) (data1 data2 : AttestationData) :
    isSlashableAttestationData data1 data2 = true ↔
      DoubleVote (data1.toFfgVote block validator) (data2.toFfgVote block validator) ∨
        SurroundVote (data1.toFfgVote block validator) (data2.toFfgVote block validator) ∨
        SameLinkDoubleVote data1 data2 ∨ BackwardSurroundVote data1 data2 := by
  have checkpoints := Checkpoint.toFfg_injective injective
  simp only [isSlashableAttestationData, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq, decide_eq_true_eq, DoubleVote, SurroundVote, SameLinkDoubleVote,
    BackwardSurroundVote, AttestationData.toFfgVote, Vote.mk.injEq, checkpoints.eq_iff,
    Checkpoint.toFfg_epoch, UInt64.toNat_inj, ← UInt64.lt_iff_toNat_lt, true_and]
  constructor
  · rintro (⟨distinct, targets⟩ | ⟨sources, epochs⟩)
    · by_cases link : data1.source = data2.source ∧ data1.target = data2.target
      · exact .inr (.inr (.inl ⟨distinct, link⟩))
      · exact .inl ⟨fun equal => link equal, targets⟩
    · by_cases forward : data2.source.epoch < data2.target.epoch
      · exact .inr (.inl ⟨sources, forward, epochs⟩)
      · exact .inr (.inr (.inr ⟨sources, UInt64.not_lt.mp forward, epochs⟩))
  · rintro (⟨distinct, targets⟩ | ⟨sources, -, epochs⟩ | ⟨distinct, -, targets⟩ |
      ⟨sources, -, epochs⟩)
    · exact .inl ⟨fun equal => distinct (by rw [equal]; exact ⟨rfl, rfl⟩), targets⟩
    · exact .inr ⟨sources, epochs⟩
    · exact .inl ⟨distinct, by rw [targets]⟩
    · exact .inr ⟨sources, epochs⟩

/-- When the two votes of the model differ and the second goes forward, the two rules agree.

The beacon chain then slashes the pair exactly when the model sees a double or a surround vote. -/
theorem isSlashableAttestationData_iff_ffg_of_forward {block : Root → β}
    (injective : Function.Injective block) (validator : ν) {data1 data2 : AttestationData}
    (link : data1.source ≠ data2.source ∨ data1.target ≠ data2.target)
    (forward : data2.source.epoch < data2.target.epoch) :
    isSlashableAttestationData data1 data2 = true ↔
      DoubleVote (data1.toFfgVote block validator) (data2.toFfgVote block validator) ∨
        SurroundVote (data1.toFfgVote block validator) (data2.toFfgVote block validator) := by
  rw [isSlashableAttestationData_iff_ffg injective]
  refine ⟨fun slashable => ?_, fun slashable => slashable.imp_right .inl⟩
  rcases slashable with double | surround | ⟨-, sources, targets⟩ | ⟨-, backward, -⟩
  · exact .inl double
  · exact .inr surround
  · exact (link.elim (· sources) (· targets)).elim
  · exact absurd forward (UInt64.not_lt.mpr backward)

/-- The model sees no slashable pair in two data with one source and one target. -/
theorem SameLinkDoubleVote.not_ffg {block : Root → β} {validator : ν}
    {data1 data2 : AttestationData} (same : SameLinkDoubleVote data1 data2) :
    ¬DoubleVote (data1.toFfgVote block validator) (data2.toFfgVote block validator) ∧
      ¬SurroundVote (data1.toFfgVote block validator) (data2.toFfgVote block validator) := by
  obtain ⟨-, sources, targets⟩ := same
  simp [DoubleVote, SurroundVote, AttestationData.toFfgVote, sources, targets]

/-- The model sees no slashable pair in a surround whose inner vote does not go forward. -/
theorem BackwardSurroundVote.not_ffg {block : Root → β} {validator : ν}
    {data1 data2 : AttestationData} (backward : BackwardSurroundVote data1 data2) :
    ¬DoubleVote (data1.toFfgVote block validator) (data2.toFfgVote block validator) ∧
      ¬SurroundVote (data1.toFfgVote block validator) (data2.toFfgVote block validator) := by
  obtain ⟨-, inner, outer⟩ := backward
  simp only [DoubleVote, SurroundVote, AttestationData.toFfgVote, Checkpoint.toFfg_epoch]
  have := UInt64.le_iff_toNat_le.mp inner
  have := UInt64.lt_iff_toNat_lt.mp outer
  omega

/-- Two different data with one source and one target exist: they differ only in their slot. -/
theorem exists_sameLinkDoubleVote (root : Root) : ∃ data1 data2, SameLinkDoubleVote data1 data2 :=
  ⟨⟨1, 0, root, ⟨0, root⟩, ⟨1, root⟩⟩, ⟨2, 0, root, ⟨0, root⟩, ⟨1, root⟩⟩, by
    simp [SameLinkDoubleVote]⟩

/-- A surround whose inner vote does not go forward exists: the inner vote has one epoch. -/
theorem exists_backwardSurroundVote (root : Root) :
    ∃ data1 data2, BackwardSurroundVote data1 data2 :=
  ⟨⟨0, 0, root, ⟨0, root⟩, ⟨2, root⟩⟩, ⟨0, 0, root, ⟨1, root⟩, ⟨1, root⟩⟩, by
    simp [BackwardSurroundVote]⟩

/-- A validator that is slashable in the model signed two data that the beacon chain slashes. -/
theorem exists_isSlashableAttestationData_of_slashable {block : Root → β}
    {signed : Set (ν × AttestationData)} {validator : ν}
    (slashable : Slashable (ffgVotes block signed) validator) :
    ∃ data1 data2, (validator, data1) ∈ signed ∧ (validator, data2) ∈ signed ∧
      isSlashableAttestationData data1 data2 = true := by
  obtain ⟨_, ⟨⟨signer1, data1⟩, signed1, rfl⟩, _, ⟨⟨signer2, data2⟩, signed2, rfl⟩, rfl, same,
    broken⟩ := slashable
  obtain rfl : signer2 = signer1 := same
  exact ⟨data1, data2, signed1, signed2, isSlashableAttestationData_of_ffg broken⟩

open scoped Classical in
/-- Accountable safety for signed attestations.

Take the votes of the model that the signed attestation data cast.

Take two finalized checkpoints of the model whose blocks conflict.

Then some validators of `V` each signed two attestation data that the beacon chain slashes.

Together they hold at least one third of the stake of `V`.

The theorem takes one validator set and one stake for every vote, a special case of the model. -/
theorem accountable_safety_isSlashableAttestationData [Preorder β] {V : Finset ν} {w : ν → ℕ}
    {genesis : β} {block : Root → β} {signed : Set (ν × AttestationData)}
    {c₁ c₂ : Models.Ffg.Checkpoint β}
    (finalized₁ : Finalized (fun _ => V) w genesis (ffgVotes block signed) c₁)
    (finalized₂ : Finalized (fun _ => V) w genesis (ffgVotes block signed) c₂)
    (conflicting : Conflicting c₁.block c₂.block) :
    stake w V ≤ 3 * stake w {validator ∈ V | ∃ data1 data2, (validator, data1) ∈ signed ∧
      (validator, data2) ∈ signed ∧ isSlashableAttestationData data1 data2 = true} :=
  (accountable_safety finalized₁ finalized₂ conflicting).trans <|
    Nat.mul_le_mul_left 3 <| stake_mono <| Finset.monotone_filter_right V
      fun _ _ => exists_isSlashableAttestationData_of_slashable

end EthLib.Consensus
