module

public import EthLib.Consensus.Proofs.Transition.ActiveKept
public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.TargetFlags

/-!
# Proofs: the target flags of a block come from the votes of its attestations

From Altair the state keeps one byte of flags for each validator, in each of two epochs.

They are the current and the previous epoch.

Justification counts the stake of the unslashed validators whose byte holds the timely target flag.

A vote here is a pair of a validator index and attestation data, as in the model of Casper FFG.

An attestation casts a vote for each validator that its bits show in its committees.

The vote holds the data of the attestation.

A block casts the votes of its attestations, with the committees of the state before the block.

The block reads the same committees when it processes each attestation.

A step of a block sets each target flag only from such a vote, for the link of its epoch.

Such a vote has the position of the flag, and the target epoch of the flag.

Its source is the justified checkpoint of that epoch.

Its target root is the block root that the state records for the first slot of that epoch.

Two steps chain into one step, whose votes are the union of their votes.

Each attestation, each other step of a block, and a whole block are such steps.

A block accepts an attestation only when the signature checks accept its aggregate signature.

Reading such a vote as signed by its validator assumes the BLS checks and unforgeable aggregates.

Gasper §4.4, Definition 4.5, justifies a checkpoint by the stake of the votes for one link.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-- The votes that an attestation casts in a state.

Each holds the data of the attestation.

Its validator is one that the bits of the attestation show in the committees of the state. -/
def attestationVotes (state : BeaconState preset fork) (attestation : Attestation preset fork) :
    Set (ValidatorIndex × AttestationData) :=
  {vote | vote.2 = attestation.data ∧
    ∃ indices, getAttestingIndices state attestation = .ok indices ∧ vote.1 ∈ indices}

/-- The votes that the attestations of a block cast, in the committees of a state.

The meaningful state is the one before the block. -/
def blockVotes (state : BeaconState preset fork) (block : BeaconBlock preset fork) :
    Set (ValidatorIndex × AttestationData) :=
  {vote | ∃ attestation ∈ block.body.attestations.data, vote ∈ attestationVotes state attestation}

/-- A vote for the link of the current epoch, or else of the previous one, at a position.

The validator has that position and the target epoch is that epoch.

The source is the justified checkpoint that the state holds for that epoch.

The target root is the block root that the state records for the first slot of that epoch. -/
def LinkVote (state : BeaconState preset fork) (current : Bool) (position : Nat)
    (vote : ValidatorIndex × AttestationData) : Prop :=
  vote.1.toNat = position ∧
    vote.2.target.epoch = (if current then getCurrentEpoch state else getPreviousEpoch state) ∧
    vote.2.source =
      (if current then state.currentJustifiedCheckpoint else state.previousJustifiedCheckpoint) ∧
    getBlockRoot state vote.2.target.epoch = .ok vote.2.target.root

/-- From Altair, each target flag of the two epochs comes from a vote of the set.

That vote is for the link of the epoch of the flag, at the position of the flag. -/
def TargetFlagsVoted (votes : Set (ValidatorIndex × AttestationData))
    (state : BeaconState preset fork) : Prop :=
  ∀ (altair : .altair ≤ fork) (current : Bool) (position : Nat),
    TargetFlagAt (recentParticipation state altair current) position →
      ∃ vote ∈ votes, LinkVote state current position vote

/-- A frame that sets target flags only from a set of votes for the right link.

It keeps the slot, the checkpoints, the fork versions and the genesis validators root.

It also keeps the block roots.

A target flag after the step was there before, or comes from a vote of the set.

That vote is for the link of the epoch of the flag, at the position of the flag. -/
structure VoteFrame (votes : Set (ValidatorIndex × AttestationData))
    (state after : BeaconState preset fork) : Prop extends Frame state after where
  blockRoots : after.blockRoots = state.blockRoots
  flags : ∀ (altair : .altair ≤ fork) (current : Bool) (position : Nat),
    TargetFlagAt (recentParticipation after altair current) position →
      TargetFlagAt (recentParticipation state altair current) position ∨
        ∃ vote ∈ votes, LinkVote state current position vote

/-- A vote for a link is one in a state with the same slot, block roots and checkpoints. -/
private theorem LinkVote.congr {other : BeaconState preset fork} {current : Bool}
    {position : Nat} {vote : ValidatorIndex × AttestationData}
    (slot : other.slot = state.slot) (blockRoots : other.blockRoots = state.blockRoots)
    (previous : other.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint)
    (current' : other.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint) :
    LinkVote other current position vote ↔ LinkVote state current position vote := by
  simp only [LinkVote, getCurrentEpoch, getPreviousEpoch, getBlockRoot, getBlockRootAtSlot, slot,
    blockRoots, previous, current']

/-- A vote for a link stays one in a state with the same slot, block roots and checkpoints. -/
theorem LinkVote.of_voteFrame {votes : Set (ValidatorIndex × AttestationData)}
    {current : Bool} {position : Nat} {vote : ValidatorIndex × AttestationData}
    (frame : VoteFrame votes state after)
    (link : LinkVote state current position vote) :
    LinkVote after current position vote :=
  (LinkVote.congr frame.slot frame.blockRoots frame.previousJustified frame.currentJustified).mpr
    link

theorem VoteFrame.refl (state : BeaconState preset fork) : VoteFrame ∅ state state :=
  ⟨Frame.refl state, rfl, fun _ _ _ flagged => .inl flagged⟩

/-- Two steps chain, with the union of their votes. -/
theorem VoteFrame.trans {first second third : BeaconState preset fork}
    {votes votes' : Set (ValidatorIndex × AttestationData)}
    (one : VoteFrame votes first second) (two : VoteFrame votes' second third) :
    VoteFrame (votes ∪ votes') first third := by
  refine ⟨one.toFrame.trans two.toFrame, two.blockRoots.trans one.blockRoots,
    fun altair current position flagged => ?_⟩
  rcases two.flags altair current position flagged with old | ⟨vote, chosen, link⟩
  · exact (one.flags altair current position old).imp_right
      fun ⟨vote, chosen, link⟩ => ⟨vote, .inl chosen, link⟩
  · exact .inr ⟨vote, .inr chosen, (LinkVote.congr one.slot one.blockRoots one.previousJustified
      one.currentJustified).mp link⟩

/-- A step with some votes is a step with any larger set of votes. -/
theorem VoteFrame.mono {votes votes' : Set (ValidatorIndex × AttestationData)}
    (frame : VoteFrame votes state after) (sub : votes ⊆ votes') :
    VoteFrame votes' state after :=
  ⟨frame.toFrame, frame.blockRoots, fun altair current position flagged =>
    (frame.flags altair current position flagged).imp_right
      fun ⟨vote, chosen, link⟩ => ⟨vote, sub chosen, link⟩⟩

/-- A block frame is a step that sets no target flag, since a zero byte holds no flag. -/
theorem VoteFrame.of_blockFrame (frame : BlockFrame state after) : VoteFrame ∅ state after where
  toFrame := frame.toFrame
  blockRoots := frame.blockRoots
  flags _ _ _ flagged := .inl (flagged.of_flagsKeptOrZero frame.flags)

/-- With more votes, each target flag still comes from a vote of the set. -/
theorem TargetFlagsVoted.mono {votes votes' : Set (ValidatorIndex × AttestationData)}
    (holds : TargetFlagsVoted votes state) (sub : votes ⊆ votes') :
    TargetFlagsVoted votes' state := fun altair current position flagged =>
  let ⟨vote, chosen, link⟩ := holds altair current position flagged
  ⟨vote, sub chosen, link⟩

/-- After a step, each target flag comes from a vote of the earlier set or of the step. -/
theorem TargetFlagsVoted.of_voteFrame {votes added : Set (ValidatorIndex × AttestationData)}
    (holds : TargetFlagsVoted votes state) (frame : VoteFrame added state after) :
    TargetFlagsVoted (votes ∪ added) after := by
  intro altair current position flagged
  rcases frame.flags altair current position flagged with old | ⟨vote, chosen, link⟩
  · obtain ⟨vote, chosen, link⟩ := holds altair current position old
    exact ⟨vote, .inl chosen, link.of_voteFrame frame⟩
  · exact ⟨vote, .inr chosen, link.of_voteFrame frame⟩

/-! ## Attestations

Each step of a block other than an attestation is a block frame, so it sets no target flag.
-/

/-- From Altair, an attestation sets target flags only from the votes that it casts. -/
private theorem voteFrame_processAttestationAltair {attestation : Attestation preset fork}
    {altair : .altair ≤ fork} {parentSlot : Slot}
    (computed :
      processAttestationAltair config checks state attestation altair parentSlot = .ok after) :
    VoteFrame (attestationVotes state attestation) state after := by
  have frame := frame_processAttestationAltair computed
  have flagsOf := processAttestationAltair_targetFlag computed
  unfold processAttestationAltair at computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, attesters, attestersOk, ⟨updated, _⟩, _, _, _,
    raised, raisedOk, final⟩ := computed
  obtain ⟨indexed, indexedOk, members, -, -⟩ :=
    getIndexedAttestation_of_getAttestingIndices attestersOk
  have last : BlockFrame raised after := by
    split at final
    · rw [recordPaymentWeight_eq final]
      exact BlockFrame.of_validators ⟨rfl, rfl⟩
    · cases final
      exact BlockFrame.refl _
  have kept := (frame_increaseBalance raisedOk).toBlockFrame.trans last
  generalize (attestation.data.target.epoch == getCurrentEpoch state) = same at kept
  refine ⟨frame, ?_, fun altair' current position flagged => ?_⟩
  · rw [kept.blockRoots]
    unfold setEpochParticipation
    split <;> rfl
  · rcases flagsOf current position flagged with old | ⟨other, otherOk, -, -, member, link⟩
    · exact .inl old
    · rw [indexedOk] at otherOk
      cases otherOk
      obtain ⟨attester, chosen, place⟩ := member
      rw [members] at chosen
      exact .inr ⟨(attester, attestation.data), ⟨rfl, attesters, attestersOk,
        List.mem_toArray.mp chosen⟩, place, link⟩

/-- An attestation sets target flags only from the votes that it casts in the state before it. -/
theorem voteFrame_processAttestation {attestation : Attestation preset fork} {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    VoteFrame (attestationVotes state attestation) state after := by
  unfold processAttestation at computed
  split at computed
  · exact voteFrame_processAttestationAltair computed
  refine (VoteFrame.of_blockFrame ?_).mono fun _ chosen => chosen.elim
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
  have kept := recordPendingAttestation_ok recorded
  split at kept <;>
  · obtain ⟨_, rest⟩ := kept
    rw [← rest]
    exact BlockFrame.of_validators ⟨rfl, rfl⟩

/-- An attestation casts the same votes in two states with the same registry and mixes. -/
theorem attestationVotes_eq_of_eq {other : BeaconState preset fork}
    (validators : other.validators.data = state.validators.data)
    (mixes : other.randaoMixes.elements = state.randaoMixes.elements)
    (attestation : Attestation preset fork) :
    attestationVotes other attestation = attestationVotes state attestation := by
  unfold attestationVotes
  rw [getAttestingIndices_eq_of_eq validators mixes]

/-! ## Blocks -/

/-- A list of attestations adds the votes that each casts in the state where the list starts.

The fact must grow with the votes, and each attestation must add the votes that it casts.

Each attestation keeps the registry and the mixes, so it casts the votes it casts at the start. -/
theorem foldlM_processAttestation_votes {parentSlot : Slot}
    (holds : Set (ValidatorIndex × AttestationData) → BeaconState preset fork → Prop)
    (mono : ∀ {votes votes' : Set (ValidatorIndex × AttestationData)} {mid},
      holds votes mid → votes ⊆ votes' → holds votes' mid)
    (step : ∀ {votes : Set (ValidatorIndex × AttestationData)} {mid next}
      {attestation : Attestation preset fork}, holds votes mid →
        processAttestation config checks mid parentSlot attestation = .ok next →
          holds (votes ∪ attestationVotes mid attestation) next) :
    ∀ {attestations : List (Attestation preset fork)}
      {votes : Set (ValidatorIndex × AttestationData)} {first last : BeaconState preset fork},
      holds votes first →
      attestations.foldlM (processAttestation config checks · parentSlot ·) first = .ok last →
        holds (votes ∪ {vote | ∃ attestation ∈ attestations,
          vote ∈ attestationVotes first attestation}) last
  | [], _, _, _, start, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact mono start fun _ chosen => .inl chosen
  | attestation :: rest, votes, first, last, start, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨mid, stepOk, computed⟩ := computed
    have registry := processAttestation_registry stepOk
    have more := foldlM_processAttestation_votes holds mono step (step start stepOk) computed
    refine mono more fun vote chosen => ?_
    rcases chosen with (old | mine) | ⟨other, member, cast⟩
    · exact .inl old
    · exact .inr ⟨attestation, List.mem_cons_self, mine⟩
    · rw [attestationVotes_eq_of_eq (congrArg (·.data) registry.1)
        (congrArg (·.elements) registry.2)] at cast
      exact .inr ⟨other, List.mem_cons_of_mem attestation member, cast⟩

/-- A block casts, where its attestations start, the votes of its attestations before it.

That holds when each of them has the same attesters there as in the state before the block. -/
theorem blockVotes_eq_of_attesters {first : BeaconState preset fork}
    {block : BeaconBlock preset fork}
    (same : ∀ attestation ∈ block.body.attestations.data,
      getAttestingIndices first attestation = getAttestingIndices state attestation) :
    {vote | ∃ attestation ∈ block.body.attestations.data.toList,
      vote ∈ attestationVotes first attestation} = blockVotes state block := by
  ext vote
  constructor
  · rintro ⟨attestation, member, cast⟩
    have member := Array.mem_toList_iff.mp member
    refine ⟨attestation, member, ?_⟩
    unfold attestationVotes at cast ⊢
    rw [← same attestation member]
    exact cast
  · rintro ⟨attestation, member, cast⟩
    refine ⟨attestation, Array.mem_toList_iff.mpr member, ?_⟩
    unfold attestationVotes at cast ⊢
    rw [same attestation member]
    exact cast

/-- A block sets target flags only from the votes of its attestations, for the right link.

Those votes are read in the committees of the state before the block.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
theorem voteFrame_processBlock
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    VoteFrame (blockVotes state block) state after := by
  obtain ⟨first, last, head, same, attested, tail⟩ :=
    processBlock_attestationSplit apart computed
  have middle := foldlM_processAttestation_votes (fun votes mid => VoteFrame votes state mid)
    (fun frame sub => frame.mono sub)
    (fun frame ok => frame.trans (voteFrame_processAttestation ok))
    (VoteFrame.of_blockFrame head) attested
  rw [blockVotes_eq_of_attesters same] at middle
  exact (middle.trans (VoteFrame.of_blockFrame tail)).mono fun vote chosen => by
    rcases chosen with (empty | cast) | empty
    · exact empty.elim
    · exact cast
    · exact empty.elim

end EthLib.Consensus
