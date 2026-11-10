module

public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.TargetFlags

/-!
# Proofs: the target flags of a block come from signed votes of the right link

From Altair the state keeps one byte of flags for each validator, in each of two epochs.

They are the current and the previous epoch.

Justification counts the stake of the unslashed validators whose byte holds the timely target flag.

A vote here is a pair of a validator index and attestation data, as in the model of Casper FFG.

A vote is signed in a state when an aggregate signature over its data verifies.

It verifies under keys of the state that include the validator's key.

Its domain is that of attestations, at the version of a fork of the chain up to the state's fork.

An indexed attestation that passes the checks of an attestation gives such a signature.

Those checks use one of the two fork versions of the state.

The proofs assume those two to be versions of forks of the chain, as genesis and upgrades set them.

Reading that as the validator's signature assumes that no one forges a BLS aggregate.

A step of a block sets each target flag only from signed votes for the link of its epoch.

Such a vote has the position of the flag, and the target epoch of the flag.

Its source is the justified checkpoint of that epoch.

Its target root is the block root that the state records for the first slot of that epoch.

Two steps chain into one step, whose votes are the union of their votes.

Each attestation, each other step of a block, and a whole block are such steps.

The votes of a block hold the data of attestations in its body.

From Gloas the type of the registry does not bound its size.

With 2^64 validators or more, a 64-bit index would name another validator and could change its key.

So the proofs keep the keys, and the signatures of the votes, while the registry stays below 2^64.

The registry never shrinks, so a bound on the last state covers each state before it.

A vote signed in a state stays signed while the genesis validators root and the keys stay.

So each target flag still comes from a signed vote for its link after the step.

Gasper §4.4, Definition 4.5, justifies a checkpoint by the stake of the votes for one link.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-- The two fork versions of the state are versions of forks of the chain, up to its own fork.

Genesis and each upgrade set them so, and the slots and blocks keep them. -/
def ForkVersionsKnown (config : Config) (state : BeaconState preset fork) : Prop :=
  (∃ signer ≤ fork, state.forkVersions.previousVersion = config.forkVersion signer) ∧
    ∃ signer ≤ fork, state.forkVersions.currentVersion = config.forkVersion signer

/-- A vote signed in a state, under the version of a fork of the chain up to the state's fork.

A sorted list of distinct validator indices holds the validator.

An aggregate signature verifies for that list.

It verifies under the keys that the state holds for those indices.

Its message is the data, in the attester domain of that version and the genesis validators root.

With the BLS checks, and no forged aggregate, the validator signed the data.

That reading assumes that BLS aggregates with proofs of possession of the keys cannot be forged.

The attestation checks use one of the two versions of the state, for the target epoch.

They also bound the number of indices from Gloas, which this leaves out.

Two upgrades in one epoch change the version of the previous epoch, so any earlier fork counts.

So a signature of the same data in the domain of an earlier fork also counts. -/
def SignedVote (config : Config) (checks : SignatureChecks) (state : BeaconState preset fork)
    (vote : ValidatorIndex × AttestationData) : Prop :=
  ∃ (indices : List ValidatorIndex) (signer : Base.Fork) (signature : BLSSignature)
    (pubkeys : Array ByteArray) (domain : Domain) (root : Root),
    signer ≤ fork ∧ vote.1 ∈ indices ∧ indices = sortedSet indices ∧
      (indices.toArray.mapM fun index => do
        return packBytes (← liftAccessor (getValidator state index)).pubkey) =
        (.ok pubkeys : Except TransitionError (Array ByteArray)) ∧
      computeDomain config DOMAIN_BEACON_ATTESTER (config.forkVersion signer)
        state.genesisValidatorsRoot = .ok domain ∧
      computeSigningRoot vote.2 domain = .ok root ∧
      checks.fastAggregateVerify pubkeys (packBytes root) (packBytes signature) = true

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

That vote is for the link of the epoch of the flag, at the position of the flag.

This says nothing about signatures without a fact about the set. -/
def TargetFlagsVoted (votes : ValidatorIndex × AttestationData → Prop)
    (state : BeaconState preset fork) : Prop :=
  ∀ (altair : .altair ≤ fork) (current : Bool) (position : Nat),
    TargetFlagAt (recentParticipation state altair current) position →
      ∃ vote, votes vote ∧ LinkVote state current position vote

/-- From Altair, each target flag of the two epochs comes from a vote signed in the state.

Its aggregate signature verifies in the attester domain of a fork of the chain, up to that fork.

That vote is for the link of the epoch of the flag, at the position of the flag. -/
def TargetFlagsSigned (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) : Prop :=
  ∀ (altair : .altair ≤ fork) (current : Bool) (position : Nat),
    TargetFlagAt (recentParticipation state altair current) position →
      ∃ vote, LinkVote state current position vote ∧ SignedVote config checks state vote

/-- A frame that sets target flags only from a set of signed votes for the right link.

It keeps the slot, the checkpoints, the fork versions and the genesis validators root.

It also keeps the block roots.

While the registry stays below 2^64 validators, it also keeps the keys.

A target flag after the step was there before, or comes from a vote of the set.

That vote is for the link of the epoch of the flag, at the position of the flag.

While the registry stays below 2^64 validators, each vote of the set is signed after the step.

That needs the fork versions after the step to be those of forks of the chain. -/
structure VoteFrame (config : Config) (checks : SignatureChecks)
    (votes : ValidatorIndex × AttestationData → Prop) (state after : BeaconState preset fork) :
    Prop extends Frame state after where
  blockRoots : after.blockRoots = state.blockRoots
  flags : ∀ (altair : .altair ≤ fork) (current : Bool) (position : Nat),
    TargetFlagAt (recentParticipation after altair current) position →
      TargetFlagAt (recentParticipation state altair current) position ∨
        ∃ vote, votes vote ∧ LinkVote state current position vote
  signed : after.validators.data.size < 2 ^ 64 → ForkVersionsKnown config after →
    ∀ vote, votes vote → SignedVote config checks after vote

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
theorem LinkVote.of_voteFrame {votes : ValidatorIndex × AttestationData → Prop}
    {current : Bool} {position : Nat} {vote : ValidatorIndex × AttestationData}
    (frame : VoteFrame config checks votes state after)
    (link : LinkVote state current position vote) :
    LinkVote after current position vote :=
  (LinkVote.congr frame.slot frame.blockRoots frame.previousJustified frame.currentJustified).mpr
    link

/-- An indexed attestation that passes the checks signs each vote of its validators and data.

The fork versions of the state must be those of forks of the chain. -/
theorem SignedVote.of_valid {indexed : IndexedAttestation preset fork}
    {vote : ValidatorIndex × AttestationData} (known : ForkVersionsKnown config state)
    (valid : isValidIndexedAttestation config checks state indexed = .ok true)
    (member : vote.1 ∈ indexed.attestingIndices.data) (data : indexed.data = vote.2) :
    SignedVote config checks state vote := by
  unfold isValidIndexedAttestation at valid
  dsimp only at valid
  split at valid
  · cases valid
  rename_i shape
  have sorted : indexed.attestingIndices.data.toList =
      sortedSet indexed.attestingIndices.data.toList :=
    Classical.byContradiction fun differ => shape (.inr (.inl differ))
  simp only [bind_ok_iff, liftAccessor_ok, liftSsz_ok, pure, Except.pure,
    Except.ok.injEq] at valid
  obtain ⟨keys, keysOk, domain, domainOk, root, rootOk, final⟩ := valid
  simp only [getDomain, Option.getD_some, mapError_ok_iff] at domainOk
  have signer : ∃ signer ≤ fork,
      computeDomain config DOMAIN_BEACON_ATTESTER (config.forkVersion signer)
        state.genesisValidatorsRoot = .ok domain := by
    split at domainOk
    · obtain ⟨signer, le, same⟩ := known.1
      exact ⟨signer, le, same ▸ domainOk⟩
    · obtain ⟨signer, le, same⟩ := known.2
      exact ⟨signer, le, same ▸ domainOk⟩
  obtain ⟨signer, le, domainOk⟩ := signer
  refine ⟨indexed.attestingIndices.data.toList, signer, indexed.signature, keys, domain, root, le,
    Array.mem_toList_iff.mpr member, sorted, keysOk, domainOk, data ▸ rootOk, final⟩

/-- Two states with the same fork versions both have known versions, or neither has. -/
theorem ForkVersionsKnown.congr (same : after.forkVersions = state.forkVersions) :
    ForkVersionsKnown config after ↔ ForkVersionsKnown config state := by
  unfold ForkVersionsKnown
  rw [same]

/-- A vote signed in a state is signed after a step or an upgrade that keeps the root and keys.

The fork of the state after must be at least the fork before. -/
theorem SignedVote.of_keys {post : Base.Fork} {later : BeaconState preset post}
    {vote : ValidatorIndex × AttestationData} (forward : fork ≤ post)
    (genesisValidatorsRoot : later.genesisValidatorsRoot = state.genesisValidatorsRoot)
    (pubkeys : KeysKept state later)
    (signed : SignedVote config checks state vote) : SignedVote config checks later vote := by
  obtain ⟨indices, signer, signature, keys, domain, root, le, member, sorted, keysOk, domainOk,
    rootOk, final⟩ := signed
  refine ⟨indices, signer, signature, keys, domain, root, Nat.le_trans le forward, member, sorted,
    ?_,
    genesisValidatorsRoot ▸ domainOk, rootOk, final⟩
  rw [Array.mapM_eq_mapM_toList] at keysOk ⊢
  simp only [Functor.map, Except.map] at keysOk ⊢
  split at keysOk
  · cases keysOk
  rename_i list listOk
  obtain ⟨length, each⟩ := mapM_eq_ok_iff.mp listOk
  rw [mapM_eq_ok_iff.mpr ⟨length, fun position inside => ?_⟩]
  · exact keysOk
  have one := each position inside
  simp only [bind_ok_iff, liftAccessor_ok] at one ⊢
  obtain ⟨validator, found, packed⟩ := one
  obtain ⟨kept, keptOk, same⟩ := pubkeys _ _ found
  exact ⟨kept, keptOk, by rw [same]; exact packed⟩

/-- A vote signed before a frame is signed after it, if then fewer than 2^64 validators exist. -/
theorem SignedVote.of_frame {vote : ValidatorIndex × AttestationData} (frame : Frame state after)
    (small : after.validators.data.size < 2 ^ 64)
    (signed : SignedVote config checks state vote) : SignedVote config checks after vote :=
  signed.of_keys (Nat.le_refl _) frame.genesisValidatorsRoot (frame.keysKept small)

theorem VoteFrame.refl (state : BeaconState preset fork) :
    VoteFrame config checks (fun _ => False) state state :=
  ⟨Frame.refl state, rfl, fun _ _ _ flagged => .inl flagged, fun _ _ _ chosen => chosen.elim⟩

/-- Two steps chain, with the union of their votes. -/
theorem VoteFrame.trans {first second third : BeaconState preset fork}
    {votes votes' : ValidatorIndex × AttestationData → Prop}
    (one : VoteFrame config checks votes first second)
    (two : VoteFrame config checks votes' second third) :
    VoteFrame config checks (fun vote => votes vote ∨ votes' vote) first third := by
  refine ⟨one.toFrame.trans two.toFrame, two.blockRoots.trans one.blockRoots,
    fun altair current position flagged => ?_, fun small known vote chosen => ?_⟩
  · rcases two.flags altair current position flagged with old | ⟨vote, chosen, link⟩
    · exact (one.flags altair current position old).imp_right
        fun ⟨vote, chosen, link⟩ => ⟨vote, .inl chosen, link⟩
    · refine .inr ⟨vote, .inr chosen, ?_⟩
      exact (LinkVote.congr one.slot one.blockRoots one.previousJustified
        one.currentJustified).mp link
  · rcases chosen with first | second
    · exact (one.signed (Nat.lt_of_le_of_lt two.registryGrows small)
        ((ForkVersionsKnown.congr two.forkVersions).mp known) vote first).of_frame
        two.toFrame small
    · exact two.signed small known vote second

/-- A block frame is a step that sets no target flag, since a zero byte holds no flag. -/
theorem VoteFrame.of_blockFrame (frame : BlockFrame state after) :
    VoteFrame config checks (fun _ => False) state after where
  toFrame := frame.toFrame
  blockRoots := frame.blockRoots
  flags _ _ _ flagged := .inl (flagged.of_flagsKeptOrZero frame.flags)
  signed _ _ _ chosen := chosen.elim

/-- After a step, each target flag comes from a vote of the earlier set or of the step. -/
theorem TargetFlagsVoted.of_voteFrame {votes added : ValidatorIndex × AttestationData → Prop}
    (holds : TargetFlagsVoted votes state) (frame : VoteFrame config checks added state after) :
    TargetFlagsVoted (fun vote => votes vote ∨ added vote) after := by
  intro altair current position flagged
  rcases frame.flags altair current position flagged with old | ⟨vote, chosen, link⟩
  · obtain ⟨vote, chosen, link⟩ := holds altair current position old
    exact ⟨vote, .inl chosen, link.of_voteFrame frame⟩
  · exact ⟨vote, .inr chosen, link.of_voteFrame frame⟩

/-- After a step, each target flag still comes from a vote for its link, signed after the step.

It needs the registry below 2^64 validators after the step.

It also needs the fork versions after the step to be those of forks of the chain. -/
theorem TargetFlagsSigned.of_voteFrame {votes : ValidatorIndex × AttestationData → Prop}
    (small : after.validators.data.size < 2 ^ 64) (known : ForkVersionsKnown config after)
    (holds : TargetFlagsSigned config checks state)
    (frame : VoteFrame config checks votes state after) :
    TargetFlagsSigned config checks after := by
  intro altair current position flagged
  rcases frame.flags altair current position flagged with old | ⟨vote, chosen, link⟩
  · obtain ⟨vote, link, signed⟩ := holds altair current position old
    exact ⟨vote, link.of_voteFrame frame, signed.of_frame frame.toFrame small⟩
  · exact ⟨vote, link.of_voteFrame frame, frame.signed small known vote chosen⟩

/-- A step with votes that hold the same votes as another set. -/
private theorem VoteFrame.congr {votes votes' : ValidatorIndex × AttestationData → Prop}
    (frame : VoteFrame config checks votes state after) (same : ∀ vote, votes vote ↔ votes' vote) :
    VoteFrame config checks votes' state after :=
  ⟨frame.toFrame, frame.blockRoots,
    fun altair current position flagged => (frame.flags altair current position flagged).imp_right
      fun ⟨vote, chosen, link⟩ => ⟨vote, (same vote).mp chosen, link⟩,
    fun small known vote chosen => frame.signed small known vote ((same vote).mpr chosen)⟩

/-! ## Attestations

Each step of a block other than an attestation is a block frame, so it sets no target flag.
-/

/-- From Altair, an attestation sets target flags only from the votes of its indexed attestation.

That indexed attestation passes the checks, and holds the data of the attestation. -/
private theorem voteFrame_processAttestationAltair {attestation : Attestation preset fork}
    {altair : .altair ≤ fork} {parentSlot : Slot}
    (computed :
      processAttestationAltair config checks state attestation altair parentSlot = .ok after) :
    ∃ votes, VoteFrame config checks votes state after ∧
      ∀ vote, votes vote → vote.2 = attestation.data := by
  have frame := frame_processAttestationAltair computed
  have flagsOf := processAttestationAltair_targetFlag computed
  unfold processAttestationAltair at computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, indexed, indexedOk,
    valid, validOk, _, checked, _, _, attesters, attestersOk, ⟨updated, _⟩, fold, _, _,
    raised, raisedOk, final⟩ := computed
  rw [ensure_ok_iff] at checked
  subst checked
  obtain ⟨indexed', indexedOk', -, dataEq, -⟩ :=
    getIndexedAttestation_of_getAttestingIndices attestersOk
  rw [indexedOk] at indexedOk'
  cases indexedOk'
  have last : BlockFrame raised after := by
    split at final
    · rw [recordPaymentWeight_eq final]
      exact BlockFrame.of_validators ⟨rfl, rfl⟩
    · cases final
      exact BlockFrame.refl _
  have kept := (frame_increaseBalance raisedOk).toBlockFrame.trans last
  generalize (attestation.data.target.epoch == getCurrentEpoch state) = same at kept
  refine ⟨fun vote => vote.1 ∈ indexed.attestingIndices.data ∧ vote.2 = attestation.data,
    ⟨frame, ?_, fun altair' current position flagged => ?_,
      fun small known vote ⟨member, data⟩ =>
        (SignedVote.of_valid ((ForkVersionsKnown.congr frame.forkVersions).mp known) validOk
          member (by rw [data, dataEq])).of_frame frame small⟩,
    fun _ chosen => chosen.2⟩
  · rw [kept.blockRoots]
    unfold setEpochParticipation
    split <;> rfl
  · rcases flagsOf current position flagged with old | ⟨other, otherOk, -, -, member, link⟩
    · exact .inl old
    · rw [indexedOk] at otherOk
      cases otherOk
      obtain ⟨attester, chosen, place⟩ := member
      exact .inr ⟨(attester, attestation.data), ⟨chosen, rfl⟩, place, link⟩

/-- An attestation sets target flags only from votes for the right link, with its own data.

While the registry stays below 2^64 validators, each of them is signed after the step.

That also needs the fork versions to be those of forks of the chain. -/
theorem voteFrame_processAttestation {attestation : Attestation preset fork} {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    ∃ votes, VoteFrame config checks votes state after ∧
      ∀ vote, votes vote → vote.2 = attestation.data := by
  unfold processAttestation at computed
  split at computed
  · exact voteFrame_processAttestationAltair computed
  refine ⟨fun _ => False, VoteFrame.of_blockFrame ?_, fun _ chosen => chosen.elim⟩
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
  have kept := recordPendingAttestation_ok recorded
  split at kept <;>
  · obtain ⟨_, rest⟩ := kept
    rw [← rest]
    exact BlockFrame.of_validators ⟨rfl, rfl⟩

/-! ## Folds -/

/-- A step with votes between two steps that set no target flag keeps its votes. -/
private theorem VoteFrame.around {first second third fourth : BeaconState preset fork}
    {votes : ValidatorIndex × AttestationData → Prop}
    (pre : VoteFrame config checks (fun _ => False) first second)
    (main : VoteFrame config checks votes second third)
    (post : VoteFrame config checks (fun _ => False) third fourth) :
    VoteFrame config checks votes first fourth :=
  ((pre.trans main).trans post).congr fun _ => by simp only [false_or, or_false]

/-- A list of attestations sets target flags only from signed votes for their data. -/
private theorem voteFrame_foldlM_processAttestation {parentSlot : Slot}
    {attestations : List (Attestation preset fork)}
    (computed :
      attestations.foldlM (processAttestation config checks · parentSlot ·) state = .ok after) :
    ∃ votes, VoteFrame config checks votes state after ∧
      ∀ vote, votes vote → ∃ attestation ∈ attestations, vote.2 = attestation.data := by
  induction attestations generalizing state with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨_, VoteFrame.refl _, fun _ chosen => chosen.elim⟩
  | cons first rest more =>
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨_, step, computed⟩ := computed
    obtain ⟨votes, frame, data⟩ := voteFrame_processAttestation step
    obtain ⟨votes', frame', data'⟩ := more computed
    refine ⟨_, frame.trans frame', fun vote chosen => ?_⟩
    rcases chosen with mine | theirs
    · exact ⟨first, List.mem_cons_self, data vote mine⟩
    · obtain ⟨attestation, member, same⟩ := data' vote theirs
      exact ⟨attestation, List.mem_cons_of_mem first member, same⟩

/-- From Altair, the operations of a block set target flags only from votes for the right link.

Each of those votes holds the data of an attestation of the body.

While the registry stays below 2^64 validators, each of them is signed after the operations.

That also needs the fork versions to be those of forks of the chain. -/
theorem voteFrame_processOperations {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    ∃ votes, VoteFrame config checks votes state after ∧
      ∀ vote, votes vote → ∃ attestation ∈ body.attestations.data, vote.2 = attestation.data := by
  obtain ⟨_, _, first, attestedOk, last⟩ := processOperations_split computed
  obtain ⟨votes, attested, data⟩ := voteFrame_foldlM_processAttestation attestedOk
  refine ⟨votes, VoteFrame.around (VoteFrame.of_blockFrame first) attested
    (VoteFrame.of_blockFrame last), fun vote chosen => ?_⟩
  obtain ⟨attestation, member, same⟩ := data vote chosen
  exact ⟨attestation, Array.mem_toList_iff.mp member, same⟩

/-- From Altair, a block sets target flags only from votes for the right link.

Each of those votes holds the data of an attestation of its body.

While the registry stays below 2^64 validators, each of them is signed after the block.

That also needs the fork versions to be those of forks of the chain. -/
theorem voteFrame_processBlock {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ∃ votes, VoteFrame config checks votes state after ∧
      ∀ vote, votes vote →
        ∃ attestation ∈ block.body.attestations.data, vote.2 = attestation.data := by
  obtain ⟨_, _, first, operatedOk, last⟩ := processBlock_split computed
  obtain ⟨votes, operated, data⟩ := voteFrame_processOperations operatedOk
  exact ⟨votes, VoteFrame.around (VoteFrame.of_blockFrame first) operated
    (VoteFrame.of_blockFrame last), data⟩

end EthLib.Consensus
