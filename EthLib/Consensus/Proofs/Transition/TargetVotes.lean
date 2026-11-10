module

public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.TargetFlags

/-!
# Proofs: the target flags of a block come from signed votes of the right link

From Altair the state keeps one byte of flags for each validator, in each of two epochs.

They are the current and the previous epoch.

Justification counts the stake of the unslashed validators whose byte holds the timely target flag.

A vote here is a pair of a validator index and attestation data, as in the model of Casper FFG.

A vote is signed in a state when an indexed attestation holds the validator and the data.

That indexed attestation must pass the checks of an attestation in that state.

With the BLS checks, its aggregate signature then verifies under keys that include the validator's.

Reading that as the validator's signature assumes that no one forges a BLS aggregate.

A step of a block sets each target flag only from signed votes for the link of its epoch.

Such a vote has the position of the flag, and the target epoch of the flag.

Its source is the justified checkpoint of that epoch.

Its target root is the block root that the state records for the first slot of that epoch.

Two steps chain into one step, whose votes are the union of their votes.

Each step of a block, and a whole block, is such a step.

The votes of a block hold the data of attestations in its body.

From Gloas the type of the registry does not bound its size.

So two of those steps need a hypothesis.

A deposit and the payload of the parent then need the registry within its limit.

With 2^64 validators or more, a 64-bit index would name another validator and could change its key.

A vote signed in a state stays signed while the fork versions, the root and the keys stay.

So each target flag still comes from a signed vote for its link after the step.

Gasper §4.4, Definition 4.5, justifies a checkpoint by the stake of the votes for one link.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-- An indexed attestation that passes the checks of the state holds the validator and the data.

With the BLS checks, and no forged aggregate, the validator signed the data.

That reading assumes that BLS aggregates with proofs of possession of the keys cannot be forged. -/
def SignedVote (config : Config) (checks : SignatureChecks) (state : BeaconState preset fork)
    (vote : ValidatorIndex × AttestationData) : Prop :=
  ∃ indexed : IndexedAttestation preset fork,
    isValidIndexedAttestation config checks state indexed = .ok true ∧
      vote.1 ∈ indexed.attestingIndices.data ∧ indexed.data = vote.2

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

/-- From Altair, each target flag of the two epochs comes from a vote that passes the checks.

With the BLS checks, that vote is signed in the state.

That vote is for the link of the epoch of the flag, at the position of the flag. -/
def TargetFlagsSigned (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) : Prop :=
  ∀ (altair : .altair ≤ fork) (current : Bool) (position : Nat),
    TargetFlagAt (recentParticipation state altair current) position →
      ∃ vote, LinkVote state current position vote ∧ SignedVote config checks state vote

/-- A step that sets target flags only from a set of signed votes for the right link.

It keeps the slot, the block roots and the two justified checkpoints.

It keeps the fork versions, the genesis validators root and the key of each validator.

A target flag after the step was there before, or comes from a vote of the set.

That vote is for the link of the epoch of the flag, at the position of the flag.

Each vote of the set is signed in the state after the step. -/
structure VoteFrame (config : Config) (checks : SignatureChecks)
    (votes : ValidatorIndex × AttestationData → Prop) (state after : BeaconState preset fork) :
    Prop where
  slot : after.slot = state.slot
  blockRoots : after.blockRoots = state.blockRoots
  previousJustified : after.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint
  currentJustified : after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint
  forkVersions : after.forkVersions = state.forkVersions
  genesisValidatorsRoot : after.genesisValidatorsRoot = state.genesisValidatorsRoot
  pubkeys : ∀ index validator, getValidator state index = .ok validator →
    ∃ kept, getValidator after index = .ok kept ∧ kept.pubkey = validator.pubkey
  flags : ∀ (altair : .altair ≤ fork) (current : Bool) (position : Nat),
    TargetFlagAt (recentParticipation after altair current) position →
      TargetFlagAt (recentParticipation state altair current) position ∨
        ∃ vote, votes vote ∧ LinkVote state current position vote
  signed : ∀ vote, votes vote → SignedVote config checks after vote

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

/-- A vote signed in a state is signed in one with the same fork versions, root and keys. -/
theorem SignedVote.of_keys {vote : ValidatorIndex × AttestationData}
    (forkVersions : after.forkVersions = state.forkVersions)
    (genesisValidatorsRoot : after.genesisValidatorsRoot = state.genesisValidatorsRoot)
    (pubkeys : ∀ index validator, getValidator state index = .ok validator →
      ∃ kept, getValidator after index = .ok kept ∧ kept.pubkey = validator.pubkey)
    (signed : SignedVote config checks state vote) : SignedVote config checks after vote := by
  obtain ⟨indexed, valid, member, data⟩ := signed
  refine ⟨indexed, ?_, member, data⟩
  unfold isValidIndexedAttestation at valid ⊢
  dsimp only at valid ⊢
  split at valid
  · cases valid
  rename_i shape
  rw [ite_eq_right shape]
  simp only [bind_ok_iff, liftAccessor_ok, liftSsz_ok, pure, Except.pure] at valid ⊢
  obtain ⟨keys, keysOk, domain, domainOk, root, rootOk, final⟩ := valid
  refine ⟨keys, ?_, domain, ?_, root, rootOk, final⟩
  · rw [Array.mapM_eq_mapM_toList] at keysOk ⊢
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
  · simpa only [getDomain, Option.getD_some, forkVersions, genesisValidatorsRoot] using domainOk

/-- A vote signed before a step is signed after it. -/
theorem SignedVote.of_voteFrame {votes : ValidatorIndex × AttestationData → Prop}
    {vote : ValidatorIndex × AttestationData} (frame : VoteFrame config checks votes state after)
    (signed : SignedVote config checks state vote) : SignedVote config checks after vote :=
  signed.of_keys frame.forkVersions frame.genesisValidatorsRoot frame.pubkeys

theorem VoteFrame.refl (state : BeaconState preset fork) :
    VoteFrame config checks (fun _ => False) state state :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ validator found => ⟨validator, found, rfl⟩,
    fun _ _ _ flagged => .inl flagged, fun _ => False.elim⟩

/-- Two steps chain, with the union of their votes. -/
theorem VoteFrame.trans {first second third : BeaconState preset fork}
    {votes votes' : ValidatorIndex × AttestationData → Prop}
    (one : VoteFrame config checks votes first second)
    (two : VoteFrame config checks votes' second third) :
    VoteFrame config checks (fun vote => votes vote ∨ votes' vote) first third := by
  refine ⟨two.slot.trans one.slot, two.blockRoots.trans one.blockRoots,
    two.previousJustified.trans one.previousJustified,
    two.currentJustified.trans one.currentJustified, two.forkVersions.trans one.forkVersions,
    two.genesisValidatorsRoot.trans one.genesisValidatorsRoot, fun index validator found => ?_,
    fun altair current position flagged => ?_,
    fun vote chosen => ?_⟩
  · obtain ⟨middle, middleOk, same⟩ := one.pubkeys index validator found
    obtain ⟨kept, keptOk, same'⟩ := two.pubkeys index middle middleOk
    exact ⟨kept, keptOk, same'.trans same⟩
  · rcases two.flags altair current position flagged with old | ⟨vote, chosen, link⟩
    · exact (one.flags altair current position old).imp_right
        fun ⟨vote, chosen, link⟩ => ⟨vote, .inl chosen, link⟩
    · refine .inr ⟨vote, .inr chosen, ?_⟩
      exact (LinkVote.congr one.slot one.blockRoots one.previousJustified
        one.currentJustified).mp link
  · rcases chosen with first | second
    · exact (one.signed vote first).of_voteFrame two
    · exact two.signed vote second

/-- After a step, each target flag comes from a vote of the earlier set or of the step. -/
theorem TargetFlagsVoted.of_voteFrame {votes added : ValidatorIndex × AttestationData → Prop}
    (holds : TargetFlagsVoted votes state) (frame : VoteFrame config checks added state after) :
    TargetFlagsVoted (fun vote => votes vote ∨ added vote) after := by
  intro altair current position flagged
  rcases frame.flags altair current position flagged with old | ⟨vote, chosen, link⟩
  · obtain ⟨vote, chosen, link⟩ := holds altair current position old
    exact ⟨vote, .inl chosen, link.of_voteFrame frame⟩
  · exact ⟨vote, .inr chosen, link.of_voteFrame frame⟩

/-- After a step, each target flag still comes from a vote signed in the state. -/
theorem TargetFlagsSigned.of_voteFrame {votes : ValidatorIndex × AttestationData → Prop}
    (holds : TargetFlagsSigned config checks state)
    (frame : VoteFrame config checks votes state after) :
    TargetFlagsSigned config checks after := by
  intro altair current position flagged
  rcases frame.flags altair current position flagged with old | ⟨vote, chosen, link⟩
  · obtain ⟨vote, link, signed⟩ := holds altair current position old
    exact ⟨vote, link.of_voteFrame frame, signed.of_voteFrame frame⟩
  · exact ⟨vote, link.of_voteFrame frame, frame.signed vote chosen⟩

/-! ## Steps that keep the flags -/

/-- A step that keeps the block roots, the fork versions and the genesis validators root.

It keeps both lists of flags, the size of the registry and the key of each validator. -/
private structure Kept (state after : BeaconState preset fork) : Prop where
  blockRoots : after.blockRoots = state.blockRoots
  forkVersions : after.forkVersions = state.forkVersions
  genesisValidatorsRoot : after.genesisValidatorsRoot = state.genesisValidatorsRoot
  previous : after.previousEpochParticipation = state.previousEpochParticipation
  current : after.currentEpochParticipation = state.currentEpochParticipation
  size : after.validators.data.size = state.validators.data.size
  pubkeys : ∀ index validator, getValidator state index = .ok validator →
    ∃ kept, getValidator after index = .ok kept ∧ kept.pubkey = validator.pubkey

private theorem Kept.refl (state : BeaconState preset fork) : Kept state state :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ validator found => ⟨validator, found, rfl⟩⟩

private theorem Kept.trans {first second third : BeaconState preset fork}
    (one : Kept first second) (two : Kept second third) : Kept first third := by
  refine ⟨two.blockRoots.trans one.blockRoots, two.forkVersions.trans one.forkVersions,
    two.genesisValidatorsRoot.trans one.genesisValidatorsRoot, two.previous.trans one.previous,
    two.current.trans one.current, two.size.trans one.size, fun index validator found => ?_⟩
  obtain ⟨middle, middleOk, same⟩ := one.pubkeys index validator found
  obtain ⟨kept, keptOk, same'⟩ := two.pubkeys index middle middleOk
  exact ⟨kept, keptOk, same'.trans same⟩

/-- A step with the same registry that keeps the other fields of a kept step. -/
private theorem Kept.of_validators (validators : after.validators = state.validators)
    (blockRoots : after.blockRoots = state.blockRoots)
    (forkVersions : after.forkVersions = state.forkVersions)
    (genesisValidatorsRoot : after.genesisValidatorsRoot = state.genesisValidatorsRoot)
    (previous : after.previousEpochParticipation = state.previousEpochParticipation)
    (current : after.currentEpochParticipation = state.currentEpochParticipation) :
    Kept state after :=
  ⟨blockRoots, forkVersions, genesisValidatorsRoot, previous, current, by rw [validators],
    fun index validator found => ⟨validator, by rw [getValidator, validators]; exact found, rfl⟩⟩

/-- A fold whose every step is kept is kept. -/
private theorem Kept.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x s', step s x = .ok s' → Kept s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : Kept state after :=
  foldlM_ok_invariant (Kept state) (fun _ _ _ before ok => before.trans (kept _ _ _ ok))
    (Kept.refl state) computed

/-- A kept step that is also a frame sets no target flag. -/
private theorem VoteFrame.of_kept (frame : Frame state after) (kept : Kept state after) :
    VoteFrame config checks (fun _ => False) state after where
  slot := frame.slot
  blockRoots := kept.blockRoots
  previousJustified := frame.previousJustified
  currentJustified := frame.currentJustified
  forkVersions := kept.forkVersions
  genesisValidatorsRoot := kept.genesisValidatorsRoot
  pubkeys := kept.pubkeys
  flags altair current position flagged := by
    left
    cases current <;>
      simpa only [recentParticipation, kept.previous, kept.current] using flagged
  signed _ chosen := chosen.elim

/-- Replacing a validator by one with the same key keeps the step. -/
private theorem kept_setValidator {index : ValidatorIndex} {validator old : Validator}
    (set : state.setValidator index validator = .ok after)
    (found : getValidator state index = .ok old) (same : validator.pubkey = old.pubkey) :
    Kept state after := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  refine ⟨rfl, rfl, rfl, rfl, rfl, by simp [BeaconState.putValidator], ?_⟩
  intro other validator' found'
  by_cases here : other.toNat = index.toNat
  · refine ⟨validator, ?_, ?_⟩
    · simp [getValidator, BeaconState.putValidator, here, inside]
    · obtain rfl := UInt64.toNat_inj.mp here
      rw [found] at found'
      cases found'
      exact same
  · refine ⟨validator', ?_, rfl⟩
    simpa [getValidator, BeaconState.putValidator, Array.getElem?_set, Ne.symm here] using found'

/-- A fold whose every step is kept on a registry that fits 64 bits is kept. -/
private theorem Kept.foldlM_small {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x s', s.validators.data.size < 2 ^ 64 → step s x = .ok s' → Kept s s')
    {items : List α} (small : state.validators.data.size < 2 ^ 64)
    (computed : items.foldlM step state = .ok after) : Kept state after :=
  foldlM_ok_invariant (Kept state)
    (fun _ _ _ before ok => before.trans (kept _ _ _ (before.size ▸ small) ok))
    (Kept.refl state) computed

private theorem kept_increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : Kept state after := by
  obtain ⟨_, set⟩ := increaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact Kept.of_validators rfl rfl rfl rfl rfl rfl

private theorem kept_decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : Kept state after := by
  obtain ⟨_, set⟩ := decreaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact Kept.of_validators rfl rfl rfl rfl rfl rfl

private theorem kept_exitQueue {exitBalance : Gwei} {exitEpoch : Epoch}
    (computed : exitQueue config state exitBalance = .ok (after, exitEpoch)) :
    Kept state after := by
  obtain ⟨validators, -⟩ := exitQueue_validators computed
  unfold exitQueue at computed
  split at computed
  · simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := computed
    exact Kept.of_validators validators rfl rfl rfl rfl rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, rfl, _⟩ := computed
    exact Kept.refl _

private theorem kept_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) : Kept state after := by
  obtain ⟨validator, found, ⟨_, rfl⟩ | ⟨_, queued, exitEpoch, withdrawableEpoch, queue, -, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact Kept.refl _
  · have same := (exitQueue_validators queue).1
    exact (kept_exitQueue queue).trans
      (kept_setValidator (old := validator) set (by rw [getValidator, same]; exact found) rfl)

private theorem kept_slashings (state : BeaconState preset fork) (slashings : RootedVector Gwei _) :
    Kept state { state with slashings } :=
  Kept.of_validators rfl rfl rfl rfl rfl rfl

private theorem kept_slashValidatorLast {last : BeaconState preset fork} {index : ValidatorIndex}
    (done : (pure (if gloas : .glamsterdam ≤ fork then cancelProposerPayments last gloas index
      else last) : Except AccessorError (BeaconState preset fork)) = .ok after) :
    Kept last after := by
  simp only [pure, Except.pure, Except.ok.injEq] at done
  subst done
  split
  · exact Kept.of_validators rfl rfl rfl rfl rfl rfl
  · exact Kept.refl _

private theorem kept_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    Kept state after := by
  obtain ⟨_, validator, _, _, _, _, _, _, _, _, _, last, exitedOk, found, -, markedOk, -, -, -,
    loweredOk, -, -, raisedOk, lastOk, done⟩ := slashValidator_ok computed
  refine (kept_initiateValidatorExit exitedOk).trans <|
    ((kept_setValidator markedOk found rfl).trans (kept_slashings _ _)).trans <|
    (kept_decreaseBalance loweredOk).trans <| (kept_increaseBalance raisedOk).trans <|
    (kept_increaseBalance lastOk).trans (kept_slashValidatorLast
      (last := last) (after := after) (index := slashedIndex) (by subst done; rfl))

private theorem kept_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) : Kept state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact Kept.of_validators rfl rfl rfl rfl rfl rfl

private theorem kept_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) : Kept state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact Kept.of_validators rfl rfl rfl rfl rfl rfl

private theorem kept_processEth1Data {before : fork < .hegota} {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) : Kept state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  exact Kept.of_validators (by rw [← rest]) (by rw [← rest]) (by rw [← rest]) (by rw [← rest])
    (by rw [← rest]) (by rw [← rest])

private theorem kept_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    Kept state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact kept_slashValidator slashed

private theorem kept_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    Kept step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact kept_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Kept.refl _

private theorem kept_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    Kept state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant (fun step => Kept state step.1)
    (fun _ _ _ before ok => before.trans (kept_slashIfSlashable ok))
    (show Kept state (state, false).1 from Kept.refl state) folded

private theorem kept_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    Kept state after := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact kept_initiateValidatorExit exited

private theorem kept_processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) : Kept state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact Kept.of_validators rfl rfl rfl rfl rfl rfl

private theorem kept_computeExitEpochAndUpdateChurn {electra : .pectra ≤ fork} {exitBalance : Gwei}
    {epoch : Epoch}
    (computed :
      computeExitEpochAndUpdateChurn config state electra exitBalance = .ok (after, epoch)) :
    Kept state after := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact Kept.of_validators rfl rfl rfl rfl rfl rfl

private theorem kept_computeConsolidationEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {balance : Gwei}
    {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (after, epoch)) :
    Kept state after := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact Kept.of_validators rfl rfl rfl rfl rfl rfl

private theorem kept_requestPartialWithdrawal {electra : .pectra ≤ fork} {index : ValidatorIndex}
    {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    Kept state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    exact (kept_computeExitEpochAndUpdateChurn churned).trans
      (Kept.of_validators rfl rfl rfl rfl rfl rfl)
  · cases computed
    exact Kept.refl _

private theorem kept_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    Kept state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact Kept.refl _)
    | exact kept_initiateValidatorExit (liftAccessor_ok.mp computed)
    | exact kept_requestPartialWithdrawal computed

private theorem kept_queueExcessActiveBalance {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queueExcessActiveBalance state electra index = .ok after) : Kept state after := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, set, rfl⟩ := computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact Kept.of_validators rfl rfl rfl rfl rfl rfl
  · cases computed
    exact Kept.refl _

private theorem kept_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    Kept state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨validator, found, _, set, queued⟩ := computed
  exact (kept_setValidator set found rfl).trans (kept_queueExcessActiveBalance queued)

private theorem kept_queueConsolidation {electra : .pectra ≤ fork} {sourcePosition : Nat}
    {source : Validator} {targetIndex : ValidatorIndex}
    (small : state.validators.data.size < 2 ^ 64)
    (found : ∃ inside : sourcePosition < state.validators.data.size,
      state.validators.data[sourcePosition] = source)
    (computed :
      queueConsolidation config state electra sourcePosition source targetIndex = .ok after) :
    Kept state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure] at computed
  obtain ⟨⟨churnedState, exitEpoch⟩, churned, withdrawable, -, _, set, _, _, computed⟩ :=
    computed
  simp only [Except.ok.injEq] at computed
  subst computed
  obtain ⟨inside, rfl⟩ := found
  have validators : churnedState.validators = state.validators := by
    simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churned
    obtain ⟨_, _, _, _, _, _, churned⟩ := churned
    cases churned
    rfl
  have read : getValidator churnedState sourcePosition.toUInt64 =
      .ok state.validators.data[sourcePosition] := by
    rw [getValidator, validators, Nat.toUInt64_eq,
      UInt64.toNat_ofNat_of_lt' (Nat.lt_trans inside small), Array.getElem?_eq_getElem inside]
  exact (kept_computeConsolidationEpochAndUpdateChurn churned).trans <|
    (kept_setValidator set read rfl).trans (Kept.of_validators rfl rfl rfl rfl rfl rfl)

private theorem kept_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest} (small : state.validators.data.size < 2 ^ 64)
    (computed : processConsolidationRequest config state electra request = .ok after) :
    Kept state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact Kept.refl _)
    | exact kept_switchToCompoundingValidator (liftAccessor_ok.mp computed)
    | exact kept_queueConsolidation small ⟨_, rfl⟩ computed

private theorem kept_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    Kept state after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  have small : state.validators.data.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (state.validators.bound electra.2) (UInt64.toNat_lt _)
  have deposits := Kept.foldlM (fun _ _ _ ok => kept_processDepositRequest ok) depositsOk
  have withdrawals := Kept.foldlM (fun _ _ _ ok => kept_processWithdrawalRequest ok) withdrawalsOk
  exact deposits.trans <| withdrawals.trans <|
    Kept.foldlM_small (fun _ _ _ fits ok => kept_processConsolidationRequest fits ok)
      (by rw [withdrawals.size, deposits.size]; exact small) consolidationsOk

private theorem kept_applyWithdrawal {withdrawal : Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) : Kept state after := by
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, set⟩ := computed
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact Kept.of_validators rfl rfl rfl rfl rfl rfl
  · exact kept_decreaseBalance computed

private theorem kept_updateNextWithdrawalIndex {withdrawals : Array Withdrawal}
    (computed : updateNextWithdrawalIndex state withdrawals = .ok after) : Kept state after := by
  unfold updateNextWithdrawalIndex at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact Kept.of_validators rfl rfl rfl rfl rfl rfl
  · cases computed
    exact Kept.refl _

private theorem kept_updateNextWithdrawalValidatorIndex {capella : .shapella ≤ fork}
    {withdrawals : Array Withdrawal}
    (computed : updateNextWithdrawalValidatorIndex state capella withdrawals = .ok after) :
    Kept state after := by
  unfold updateNextWithdrawalValidatorIndex at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · cases computed
  · cases computed
    exact Kept.of_validators rfl rfl rfl rfl rfl rfl

private theorem kept_updateNextWithdrawalBuilderIndex {gloas : .glamsterdam ≤ fork} {count : Nat}
    (computed : updateNextWithdrawalBuilderIndex state gloas count = .ok after) :
    Kept state after := by
  unfold updateNextWithdrawalBuilderIndex at computed
  dsimp only at computed
  split at computed
  · cases computed
    exact Kept.of_validators rfl rfl rfl rfl rfl rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact Kept.of_validators rfl rfl rfl rfl rfl rfl

private theorem kept_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    Kept state after := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : Kept state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact Kept.foldlM (fun _ _ _ ok => kept_applyWithdrawal ok) appliedOk
  have queued : ∀ kept : BeaconState preset fork,
      Kept kept (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals kept gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else kept) := by
    intro kept
    split <;> exact Kept.of_validators rfl rfl rfl rfl rfl rfl
  have partials : ∀ kept : BeaconState preset fork,
      Kept kept (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals kept electra expected.processedPartialWithdrawalsCount
      else kept) := by
    intro kept
    split <;> exact Kept.of_validators rfl rfl rfl rfl rfl rfl
  have swept : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → Kept kept finished := by
    intro kept ok
    split at ok
    · exact kept_updateNextWithdrawalBuilderIndex ok
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ Kept.refl _
  exact one.trans <| (kept_updateNextWithdrawalIndex indexedOk).trans <| (queued _).trans <|
    (partials _).trans <| (swept _ sweptOk).trans (kept_updateNextWithdrawalValidatorIndex last)

private theorem kept_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) : Kept state after := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, applied⟩ := computed
      exact kept_applyExpectedWithdrawals applied
    · cases computed
      exact Kept.refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact kept_applyExpectedWithdrawals applied

private theorem kept_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    Kept state after := by
  obtain ⟨validator, found, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact kept_setValidator set found rfl

private theorem kept_processExecutionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    Kept state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  exact Kept.of_validators rfl rfl rfl rfl rfl rfl

private theorem kept_processBuilderDepositRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    Kept state after := by
  unfold processBuilderDepositRequest addBuilderToRegistry at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact Kept.of_validators rfl rfl rfl rfl rfl rfl)

private theorem kept_processBuilderExitRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    Kept state after := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · exact Kept.refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact Kept.of_validators rfl rfl rfl rfl rfl rfl

private theorem kept_settleParentPayment {gloas : .glamsterdam ≤ fork}
    (computed : settleParentPayment state gloas = .ok after) : Kept state after := by
  unfold settleParentPayment at computed
  split at computed
  · have settled := liftAccessor_ok.mp computed
    unfold settleBuilderPayment at settled
    split at settled
    · cases settled
      exact Kept.of_validators rfl rfl rfl rfl rfl rfl
    · cases settled
  · simp only at computed
    split at computed <;> cases computed <;>
      exact Kept.of_validators rfl rfl rfl rfl rfl rfl

private theorem kept_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (small : state.validators.data.size < 2 ^ 64)
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    Kept state after := by
  unfold processParentExecutionPayload at computed
  dsimp only at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact Kept.refl _
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, applied⟩ := computed
  unfold applyParentExecutionPayload at applied
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at applied
  obtain ⟨_, _, _, _, _, _, _, _, settled, settledOk, requested, requestedOk, _, _, rfl⟩ :=
    applied
  unfold processParentRequests at requestedOk
  simp only [bind_ok_iff, ← Array.foldlM_toList] at requestedOk
  obtain ⟨_, depositsOk, _, withdrawalsOk, _, consolidationsOk, _, buildersOk, exitsOk⟩ :=
    requestedOk
  have settled := kept_settleParentPayment settledOk
  have deposits := Kept.foldlM (fun _ _ _ ok => kept_processDepositRequest ok) depositsOk
  have withdrawals := Kept.foldlM (fun _ _ _ ok => kept_processWithdrawalRequest ok) withdrawalsOk
  exact settled.trans <| deposits.trans <| withdrawals.trans <|
    (Kept.foldlM_small (fun _ _ _ fits ok => kept_processConsolidationRequest fits ok)
      (by rw [withdrawals.size, deposits.size, settled.size]; exact small)
      consolidationsOk).trans <|
    (Kept.foldlM (fun _ _ _ ok => kept_processBuilderDepositRequest ok) buildersOk).trans <|
    (Kept.foldlM (fun _ _ _ ok => kept_processBuilderExitRequest ok) exitsOk).trans
      (Kept.of_validators rfl rfl rfl rfl rfl rfl)

private theorem kept_processExecutionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    Kept state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok computed
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact Kept.of_validators rfl rfl rfl rfl rfl rfl
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at recordedOk
    subst recordedOk
    exact Kept.of_validators rfl rfl rfl rfl rfl rfl

private theorem kept_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    Kept state after := by
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    exact (kept_processWithdrawals withdrawnOk).trans (kept_processExecutionPayloadBid bid)
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact (kept_processWithdrawals withdrawnOk).trans (kept_processExecutionPayload paid)
  · dsimp only at computed
    split at computed
    · exact kept_processExecutionPayload computed
    · cases computed
      exact Kept.refl _

private theorem kept_applySyncReward {reward proposerReward : Gwei}
    {proposer : Except AccessorError ValidatorIndex} {member : ValidatorIndex × Bool}
    (computed : applySyncReward reward proposerReward proposer state member = .ok after) :
    Kept state after := by
  unfold applySyncReward at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, raised, _, _, paid⟩ := computed
    exact (kept_increaseBalance raised).trans (kept_increaseBalance paid)
  · exact kept_decreaseBalance (liftAccessor_ok.mp computed)

private theorem kept_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    Kept state after := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  exact Kept.foldlM (fun _ _ _ ok => kept_applySyncReward ok) folded

/-! ## Deposits -/

/-- A step with votes that hold the same votes as another set. -/
private theorem VoteFrame.congr {votes votes' : ValidatorIndex × AttestationData → Prop}
    (frame : VoteFrame config checks votes state after) (same : ∀ vote, votes vote ↔ votes' vote) :
    VoteFrame config checks votes' state after :=
  ⟨frame.slot, frame.blockRoots, frame.previousJustified, frame.currentJustified,
    frame.forkVersions, frame.genesisValidatorsRoot, frame.pubkeys,
    fun altair current position flagged => (frame.flags altair current position flagged).imp_right
      fun ⟨vote, chosen, link⟩ => ⟨vote, (same vote).mp chosen, link⟩,
    fun vote chosen => frame.signed vote ((same vote).mpr chosen)⟩

/-- Two steps that set no target flag chain into one. -/
private theorem VoteFrame.trans_none {first second third : BeaconState preset fork}
    (one : VoteFrame config checks (fun _ => False) first second)
    (two : VoteFrame config checks (fun _ => False) second third) :
    VoteFrame config checks (fun _ => False) first third :=
  (one.trans two).congr fun _ => or_self_iff

/-- Before Gloas the type bounds the registry, and from Gloas the hypothesis does. -/
private theorem small_of_within (within : .glamsterdam ≤ fork → state.RegistryWithinLimit) :
    state.validators.data.size < 2 ^ 64 := by
  by_cases gloas : .glamsterdam ≤ fork
  · exact Nat.lt_of_le_of_lt (within gloas) (UInt64.toNat_lt _)
  · exact Nat.lt_of_le_of_lt (state.validators.bound (Nat.lt_of_not_le gloas))
      (UInt64.toNat_lt _)

/-- A new validator gets a zero byte of flags, which holds no target flag. -/
private theorem voteFrame_addValidatorToRegistry {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (small : state.validators.data.size < 2 ^ 64)
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    VoteFrame config checks (fun _ => False) state after := by
  have frame := frame_addValidatorToRegistry computed
  have pushed := addValidatorToRegistry_validators_eq_push computed small
  have pubkeys : ∀ index validator, getValidator state index = .ok validator →
      ∃ kept, getValidator after index = .ok kept ∧ kept.pubkey = validator.pubkey := by
    intro index validator found
    refine ⟨validator, ?_, rfl⟩
    unfold getValidator at found ⊢
    split at found
    · rename_i read
      cases found
      rw [pushed, Array.getElem?_push, ite_eq_right, read]
      exact Nat.ne_of_lt (Array.getElem?_eq_some_iff.mp read).1
    · cases found
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, previous, previousOk, current, currentOk, _, _, rfl⟩ := computed
    refine ⟨frame.slot, rfl, frame.previousJustified, frame.currentJustified, rfl, rfl, pubkeys,
      fun altair recent position flagged => ?_, fun _ chosen => chosen.elim⟩
    left
    obtain ⟨flags, found, set⟩ := flagged
    cases recent
    · simp only [recentParticipation, Bool.false_eq_true, ↓reduceIte] at found
      rw [setOrAppendList_getElem? previousOk] at found
      split at found
      · cases found
        exact absurd set (by decide)
      · exact ⟨flags, found, set⟩
    · simp only [recentParticipation, ↓reduceIte] at found
      rw [setOrAppendList_getElem? currentOk] at found
      split at found
      · cases found
        exact absurd set (by decide)
      · exact ⟨flags, found, set⟩
  split at computed
  · cases computed
    refine ⟨frame.slot, rfl, frame.previousJustified, frame.currentJustified, rfl, rfl, pubkeys,
      fun _ _ _ flagged => .inl flagged,
      fun _ chosen => chosen.elim⟩
  · cases computed

private theorem voteFrame_applyDepositElectra {electra : .pectra ≤ fork} {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei} {signature : BLSSignature}
    (small : state.validators.data.size < 2 ^ 64)
    (computed : applyDepositElectra config checks state electra pubkey withdrawalCredentials
      amount signature = .ok after) :
    VoteFrame config checks (fun _ => False) state after := by
  unfold applyDepositElectra at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, added, pushed⟩ := computed
      obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
      exact (voteFrame_addValidatorToRegistry small added).trans_none
        (VoteFrame.of_kept (Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl rfl)
          (Kept.of_validators rfl rfl rfl rfl rfl rfl))
    · cases computed
      exact VoteFrame.refl _
  · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
    exact VoteFrame.of_kept (Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl rfl)
      (Kept.of_validators rfl rfl rfl rfl rfl rfl)

private theorem voteFrame_applyPendingDeposit {deposit : PendingDeposit}
    (small : state.validators.data.size < 2 ^ 64)
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    VoteFrame config checks (fun _ => False) state after := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact VoteFrame.refl _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact voteFrame_addValidatorToRegistry small computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ VoteFrame.refl _
  · rw [liftAccessor_ok] at computed
    exact VoteFrame.of_kept (frame_increaseBalance computed).toFrame (kept_increaseBalance computed)

private theorem voteFrame_applyDeposit {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature} (small : state.validators.data.size < 2 ^ 64)
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    VoteFrame config checks (fun _ => False) state after := by
  unfold applyDeposit at computed
  split at computed
  · exact voteFrame_applyDepositElectra small computed
  · exact voteFrame_applyPendingDeposit small computed

/-! ## Attestations -/

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
  have last : Kept raised after := by
    split at final
    · rw [recordPaymentWeight_eq final]
      exact Kept.of_validators rfl rfl rfl rfl rfl rfl
    · cases final
      exact Kept.refl _
  have kept := (kept_increaseBalance raisedOk).trans last
  generalize (attestation.data.target.epoch == getCurrentEpoch state) = same at kept
  have validators : (setEpochParticipation state same updated).validators = state.validators := by
    unfold setEpochParticipation
    split <;> rfl
  have pubkeys : ∀ index validator, getValidator state index = .ok validator →
      ∃ kept, getValidator after index = .ok kept ∧ kept.pubkey = validator.pubkey :=
    fun index validator found =>
      kept.pubkeys index validator (by rw [getValidator, validators]; exact found)
  have forkVersions : after.forkVersions = state.forkVersions := by
    rw [kept.forkVersions]
    unfold setEpochParticipation
    split <;> rfl
  have genesisValidatorsRoot : after.genesisValidatorsRoot = state.genesisValidatorsRoot := by
    rw [kept.genesisValidatorsRoot]
    unfold setEpochParticipation
    split <;> rfl
  refine ⟨fun vote => vote.1 ∈ indexed.attestingIndices.data ∧ vote.2 = attestation.data,
    ⟨frame.slot, ?_, frame.previousJustified, frame.currentJustified, forkVersions,
      genesisValidatorsRoot, pubkeys, fun altair' current position flagged => ?_,
      fun vote ⟨member, data⟩ => SignedVote.of_keys forkVersions genesisValidatorsRoot pubkeys
        ⟨indexed, validOk, member, by rw [data, dataEq]⟩⟩,
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

/-! ## The steps of a block

Each step of a block other than an attestation sets no target flag.
-/

theorem voteFrame_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) :
    VoteFrame config checks (fun _ => False) state after := by
  exact VoteFrame.of_kept (frame_processBlockHeader computed) (kept_processBlockHeader computed)

theorem voteFrame_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) :
    VoteFrame config checks (fun _ => False) state after := by
  exact VoteFrame.of_kept (frame_processRandao computed) (kept_processRandao computed)

theorem voteFrame_processEth1Data {before : fork < .hegota} {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) :
    VoteFrame config checks (fun _ => False) state after := by
  exact VoteFrame.of_kept (frame_processEth1Data computed) (kept_processEth1Data computed)

theorem voteFrame_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    VoteFrame config checks (fun _ => False) state after := by
  exact VoteFrame.of_kept (frame_processProposerSlashing computed)
    (kept_processProposerSlashing computed)

theorem voteFrame_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    VoteFrame config checks (fun _ => False) state after := by
  exact VoteFrame.of_kept (frame_processAttesterSlashing computed)
    (kept_processAttesterSlashing computed)

/-- An attestation sets target flags only from signed votes for its own data. -/
theorem voteFrame_processAttestation {attestation : Attestation preset fork} {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    ∃ votes, VoteFrame config checks votes state after ∧
      ∀ vote, votes vote → vote.2 = attestation.data := by
  have frame := frame_processAttestation computed
  unfold processAttestation at computed
  split at computed
  · exact voteFrame_processAttestationAltair computed
  refine ⟨fun _ => False, VoteFrame.of_kept frame ?_, fun _ chosen => chosen.elim⟩
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
  have kept := recordPendingAttestation_ok recorded
  split at kept <;>
  · obtain ⟨_, rest⟩ := kept
    exact Kept.of_validators (by rw [← rest]) (by rw [← rest]) (by rw [← rest]) (by rw [← rest])
      (by rw [← rest]) (by rw [← rest])

/-- A deposit sets no target flag.

From Gloas it needs the registry within its limit, so that a new validator goes at its end.

A block from Gloas on runs no such step, so the hypothesis only matters for the step alone. -/
theorem voteFrame_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (within : .glamsterdam ≤ fork → state.RegistryWithinLimit)
    (computed : processDeposit config checks before state deposit = .ok after) :
    VoteFrame config checks (fun _ => False) state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact (VoteFrame.of_kept (state := state)
    (after := { state with eth1DepositIndex := fun _ => next })
    (Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl rfl)
    (Kept.of_validators rfl rfl rfl rfl rfl rfl)).trans_none
    (voteFrame_applyDeposit (small_of_within within) applied)

theorem voteFrame_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    VoteFrame config checks (fun _ => False) state after := by
  exact VoteFrame.of_kept (frame_processVoluntaryExit computed) (kept_processVoluntaryExit computed)

theorem voteFrame_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    VoteFrame config checks (fun _ => False) state after := by
  exact VoteFrame.of_kept (frame_processBlsToExecutionChange computed)
    (kept_processBlsToExecutionChange computed)

theorem voteFrame_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    VoteFrame config checks (fun _ => False) state after := by
  exact VoteFrame.of_kept (frame_processExecutionRequests computed)
    (kept_processExecutionRequests computed)

theorem voteFrame_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) :
    VoteFrame config checks (fun _ => False) state after := by
  exact VoteFrame.of_kept (frame_processWithdrawals computed) (kept_processWithdrawals computed)

theorem voteFrame_processExecutionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    VoteFrame config checks (fun _ => False) state after := by
  exact VoteFrame.of_kept (frame_processExecutionPayload computed)
    (kept_processExecutionPayload computed)

/-- From Gloas, the payload of the parent sets no target flag.

It needs the registry within its limit, so that a 64-bit index names the validator it reads. -/
theorem voteFrame_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork} (within : state.RegistryWithinLimit)
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    VoteFrame config checks (fun _ => False) state after := by
  exact VoteFrame.of_kept (frame_processParentExecutionPayload computed)
    (kept_processParentExecutionPayload (small_of_within fun _ => within) computed)

theorem voteFrame_processExecutionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    VoteFrame config checks (fun _ => False) state after := by
  exact VoteFrame.of_kept (frame_processExecutionPayloadBid computed)
    (kept_processExecutionPayloadBid computed)

theorem voteFrame_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    VoteFrame config checks (fun _ => False) state after := by
  exact VoteFrame.of_kept (frame_processBlockExecution computed)
    (kept_processBlockExecution computed)

theorem voteFrame_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    VoteFrame config checks (fun _ => False) state after := by
  exact VoteFrame.of_kept (frame_processSyncAggregate computed) (kept_processSyncAggregate computed)

/-! ## Folds -/

/-- A fold whose every step sets no target flag sets none. -/
private theorem VoteFrame.foldlM_none {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (frame : ∀ s x s', step s x = .ok s' → VoteFrame config checks (fun _ => False) s s')
    {items : List α} (computed : items.foldlM step state = .ok after) :
    VoteFrame config checks (fun _ => False) state after :=
  foldlM_ok_invariant (VoteFrame config checks (fun _ => False) state)
    (fun _ _ _ before ok => before.trans_none (frame _ _ _ ok)) (VoteFrame.refl state) computed

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

/-- The operations of a block set target flags only from signed votes.

Each of those votes holds the data of an attestation of the body. -/
theorem voteFrame_processOperations {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    ∃ votes, VoteFrame config checks votes state after ∧
      ∀ vote, votes vote → ∃ attestation ∈ body.attestations.data, vote.2 = attestation.data := by
  unfold processOperations at computed
  split at computed
  · unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
    obtain ⟨votes, attested, data⟩ := voteFrame_foldlM_processAttestation attestedOk
    refine ⟨votes, VoteFrame.around ?_ attested ?_, fun vote chosen => ?_⟩
    · exact (VoteFrame.foldlM_none (fun _ _ _ ok => voteFrame_processProposerSlashing ok)
        proposersOk).trans_none
        (VoteFrame.foldlM_none (fun _ _ _ ok => voteFrame_processAttesterSlashing ok) attestersOk)
    · exact (VoteFrame.foldlM_none (fun _ _ _ ok => voteFrame_processVoluntaryExit ok)
        exitsOk).trans_none <|
        (VoteFrame.foldlM_none (fun _ _ _ ok => voteFrame_processBlsToExecutionChange ok)
          changesOk).trans_none <|
        VoteFrame.foldlM_none (fun _ _ _ ok => by
          rw [processPayloadAttestation_eq ok]
          exact VoteFrame.refl _) paid
    · obtain ⟨attestation, member, same⟩ := data vote chosen
      exact ⟨attestation, Array.mem_toList_iff.mp member, same⟩
  rename_i gloas
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, exited,
    exitsOk, changed, changesOk, requestsOk⟩ := computed
  have changes : VoteFrame config checks (fun _ => False) exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact VoteFrame.foldlM_none (fun _ _ _ ok => voteFrame_processBlsToExecutionChange ok)
        changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ VoteFrame.refl _
  have requests : VoteFrame config checks (fun _ => False) changed after := by
    split at requestsOk
    · exact voteFrame_processExecutionRequests requestsOk
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact requestsOk ▸ VoteFrame.refl _
  obtain ⟨votes, attested, data⟩ := voteFrame_foldlM_processAttestation attestedOk
  refine ⟨votes, VoteFrame.around ?_ attested ?_, fun vote chosen => ?_⟩
  · exact (VoteFrame.foldlM_none (fun _ _ _ ok => voteFrame_processProposerSlashing ok)
      proposersOk).trans_none
      (VoteFrame.foldlM_none (fun _ _ _ ok => voteFrame_processAttesterSlashing ok) attestersOk)
  · exact (VoteFrame.foldlM_none
      (fun _ _ _ ok => voteFrame_processDeposit (fun later => absurd later gloas) ok)
      depositedOk).trans_none <|
      (VoteFrame.foldlM_none (fun _ _ _ ok => voteFrame_processVoluntaryExit ok)
        exitsOk).trans_none <| changes.trans_none requests
  · obtain ⟨attestation, member, same⟩ := data vote chosen
    exact ⟨attestation, Array.mem_toList_iff.mp member, same⟩

/-- A block sets target flags only from signed votes.

Each of those votes holds the data of an attestation of its body.

From Gloas it needs the registry within its limit. -/
theorem voteFrame_processBlock {block : BeaconBlock preset fork}
    (within : .glamsterdam ≤ fork → state.RegistryWithinLimit)
    (computed : processBlock config checks engine state block = .ok after) :
    ∃ votes, VoteFrame config checks votes state after ∧
      ∀ vote, votes vote →
        ∃ attestation ∈ block.body.attestations.data, vote.2 = attestation.data := by
  unfold processBlock at computed
  split at computed
  · unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, _, operatedOk, synced⟩ := computed
    have paidFrame : VoteFrame config checks (fun _ => False) state paid := by
      split at paidOk
      · rename_i gloas
        exact voteFrame_processParentExecutionPayload (within gloas) paidOk
      · cases paidOk
        exact VoteFrame.refl _
    have executedFrame : VoteFrame config checks (fun _ => False) headed executed := by
      split at executedOk
      · exact voteFrame_processBlockExecution executedOk
      · cases executedOk
        exact VoteFrame.refl _
    have votedFrame : VoteFrame config checks (fun _ => False) revealed voted := by
      split at votedOk
      · exact voteFrame_processEth1Data votedOk
      · cases votedOk
        exact VoteFrame.refl _
    obtain ⟨votes, operated, data⟩ := voteFrame_processOperations operatedOk
    exact ⟨votes, VoteFrame.around (paidFrame.trans_none <|
      (voteFrame_processBlockHeader headedOk).trans_none <| executedFrame.trans_none <|
      (voteFrame_processRandao revealedOk).trans_none votedFrame) operated
      (voteFrame_processSyncAggregate synced), data⟩
  simp only [bind_ok_iff] at computed
  obtain ⟨_, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := computed
  obtain ⟨votes, operated, data⟩ := voteFrame_processOperations operationsOk
  exact ⟨votes, VoteFrame.around ((voteFrame_processBlockHeader headerOk).trans_none <|
    (voteFrame_processRandao randaoOk).trans_none (voteFrame_processEth1Data eth1Ok)) operated
    (VoteFrame.refl _), data⟩

end EthLib.Consensus
