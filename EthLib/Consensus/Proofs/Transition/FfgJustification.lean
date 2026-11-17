module

public import EthLib.Consensus.Proofs.Transition.FfgStake
public import EthLib.Consensus.Proofs.Transition.FfgVotes
public import EthLib.Consensus.Proofs.Transition.TargetPending

/-!
# Proofs: justification in the beacon chain as a supermajority link of Casper FFG

The epoch step justifies the previous or the current epoch from the stake of its attesters.

In the model of Casper FFG, a supermajority link counts the stake of the voters of a link.

The voters belong to the validator set of the target, which here is the active set of its epoch.

Each attester that the step counts is active in the epoch of the target.

It cast a vote of a set whose source is the justified checkpoint of that epoch.

The target of that vote is the checkpoint of the epoch.

Its root is the block root that the state records for the first slot of the epoch.

From Altair the target flags give that, and before Altair the pending attestations do.

The meaningful set holds the votes that the attestations of applied blocks cast.

A block accepts an attestation only when the signature checks accept its aggregate signature.

Reading such a vote as signed by its validator assumes the BLS checks and unforgeable aggregates.

The step drops slashed attesters, so the attesters are a subset of the voters of the model.

The step divides by the active stake of the current epoch, not of the epoch of the target.

For the previous epoch, the validators that exit at the current epoch count in the target set.

They do not count in that total, so their stake enters the bound as a term of churn.

For the current epoch that term is the stake of the empty set, zero.

Gasper §4.4, Definitions 4.5 and 4.6, justify a checkpoint by a supermajority link.

Gasper §8.6 lets the validator set change, with a set for each block.

The term of churn is the stake of the exited set of Gasper §8.6, Definition 8.1.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Models.Ffg

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork} {β : Type*}
  {attested : Set (ValidatorIndex × AttestationData)}

/-- The stake bound of a supermajority link of Casper FFG, up to a term of churn.

The validator set is the active set of the given epoch.

The caller must give the epoch of the target, which this does not check.

Each validator weighs its effective balance in the state.

The model needs that set and those stakes fixed across states, which this does not show.

Twice the stake of that set is at most three times the stake of its voters for the link.

The term of churn adds twice the stake of that set outside the active set of the current epoch.

A supermajority link of the model asks for the bound without that term; a slack link takes it.

Both ask for a source epoch below the target epoch.

Both also ask for the source block in the chain of the target block. -/
def LinkWithChurn (state : BeaconState preset fork) (votes : Set (Vote ValidatorIndex β))
    (epoch : Epoch) (source target : Models.Ffg.Checkpoint β) : Prop :=
  2 * stake (fun index => balanceAt state index.toNat)
      (getActiveValidatorIndices state epoch).toFinset ≤
    3 * stake (fun index => balanceAt state index.toNat)
        (signers (getActiveValidatorIndices state epoch).toFinset votes source target) +
      2 * stake (fun index => balanceAt state index.toNat)
        ((getActiveValidatorIndices state epoch).toFinset \
          (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset)

/-- A vote of the set for the link of an epoch, by an active validator, is a voter of the model.

The vote of the model goes from the justified checkpoint of the epoch to its checkpoint.

The root of that checkpoint is the block root that the state records for its first slot.

The voter belongs to the active set of that epoch. -/
theorem mem_signers_of_linkVote {block : Root → β} {votes : Set (Vote ValidatorIndex β)}
    (contains : ffgVotes block attested ⊆ votes)
    {current : Bool} {root : Root}
    (rootOk : getBlockRoot state
      (if current then getCurrentEpoch state else getPreviousEpoch state) = .ok root)
    {index : ValidatorIndex}
    (active : index ∈ getActiveValidatorIndices state
      (if current then getCurrentEpoch state else getPreviousEpoch state))
    {vote : ValidatorIndex × AttestationData} (link : LinkVote state current index.toNat vote)
    (cast : vote ∈ attested) :
    index ∈ signers
      (getActiveValidatorIndices state
        (if current then getCurrentEpoch state else getPreviousEpoch state)).toFinset votes
      ((if current then state.currentJustifiedCheckpoint
        else state.previousJustifiedCheckpoint).toFfg block)
      (Checkpoint.toFfg block
        ⟨if current then getCurrentEpoch state else getPreviousEpoch state, root⟩) := by
  obtain ⟨position, epoch, source, targetRoot⟩ := link
  obtain ⟨validator, data⟩ := vote
  have same : validator = index := UInt64.toNat_inj.mp position
  subst same
  dsimp only at epoch source targetRoot
  rw [epoch, rootOk, Except.ok.injEq] at targetRoot
  have target : data.target =
      ⟨if current then getCurrentEpoch state else getPreviousEpoch state, root⟩ := by
    rw [← epoch, targetRoot]
  simp only [signers, Finset.mem_filter, List.mem_toFinset]
  refine ⟨active, contains ⟨(validator, data), cast, ?_⟩⟩
  simp [AttestationData.toFfgVote, source, target]

/-- A validator active in the previous epoch and not in the current one exits at the current one.

The registry must stay below 2^64 validators, so that an index names one validator. -/
theorem exists_exitEpoch_eq_of_mem_sdiff_active (within : state.RegistryWithinLimit)
    {index : ValidatorIndex}
    (member : index ∈ (getActiveValidatorIndices state (getPreviousEpoch state)).toFinset \
      (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset) :
    ∃ validator, state.validators.data[index.toNat]? = some validator ∧
      validator.exitEpoch = getCurrentEpoch state := by
  simp only [Finset.mem_sdiff, List.mem_toFinset, mem_getActiveValidatorIndices within] at member
  obtain ⟨⟨validator, found, active⟩, inactive⟩ := member
  refine ⟨validator, found, ?_⟩
  have previous := getPreviousEpoch_toNat state
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le,
    UInt64.lt_iff_toNat_lt] at active
  have notActive : ¬(validator.activationEpoch.toNat ≤ (getCurrentEpoch state).toNat ∧
      (getCurrentEpoch state).toNat < validator.exitEpoch.toNat) := fun h =>
    inactive ⟨validator, found, by
      simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le,
        UInt64.lt_iff_toNat_lt]
      exact h⟩
  apply UInt64.toNat_inj.mp
  omega

/-- A passing test of justification bounds the stake of a target set by the stake of a vote set.

The attesters must lie in the vote set.

The test divides by the active stake of the current epoch, so the bound adds a term.

That term is twice the stake of the target set outside the active set of the current epoch.

The active stake must be more than one and a half increments. -/
private theorem stake_le_of_justificationTest {attesting : List ValidatorIndex}
    {total balance threshold weight : Gwei} {target voters : Finset ValidatorIndex}
    (totalOk : getTotalActiveBalance state = .ok total)
    (balanceOk : getTotalBalance state attesting = .ok balance)
    (thresholdOk : mulChecked total 2 = .ok threshold)
    (weightOk : mulChecked balance 3 = .ok weight) (passed : threshold ≤ weight)
    (large : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun index => balanceAt state index.toNat)
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset)
    (subset : attesting.toFinset ⊆ voters) :
    2 * stake (fun index => balanceAt state index.toNat) target ≤
      3 * stake (fun index => balanceAt state index.toNat) voters +
        2 * stake (fun index => balanceAt state index.toNat)
          (target \ (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset) := by
  have test := (justificationTest_iff_stake (getTotalActiveBalance_ok totalOk) balanceOk
    thresholdOk weightOk large).mp passed
  have attesters := stake_mono (w := fun index => balanceAt state index.toNat) subset
  have split := stake_add_stake_sdiff (w := fun index => balanceAt state index.toNat)
    (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset target
  omega

/-- From Altair, each attester that justification counts for an epoch cast a vote of the set.

That vote is for the link of the epoch.

The epoch is the current one when asked, and the previous one otherwise.

The attesters are the unslashed validators with the timely target flag for that epoch.

Each of them is active in that epoch.

Justification must run, so the current epoch must be past the first two. -/
theorem TargetFlagsVoted.attester (altair : .altair ≤ fork)
    (holds : TargetFlagsVoted attested state)
    (late : ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1) (current : Bool)
    {indices : List ValidatorIndex}
    (counted : getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
      (if current then getCurrentEpoch state else getPreviousEpoch state) = .ok indices)
    {index : ValidatorIndex} (member : index ∈ indices) :
    index ∈ getActiveValidatorIndices state
        (if current then getCurrentEpoch state else getPreviousEpoch state) ∧
      ∃ vote, LinkVote state current index.toNat vote ∧ vote ∈ attested := by
  -- After the first two epochs, the previous epoch is not the current one.
  have distinct : getPreviousEpoch state ≠ getCurrentEpoch state := by
    intro same
    have := congrArg UInt64.toNat same
    rw [getPreviousEpoch_toNat] at this
    exact late (UInt64.le_iff_toNat_le.mpr (by simp [GENESIS_EPOCH]; omega))
  obtain ⟨active, -, flags, read, set⟩ := mem_getUnslashedParticipatingIndices counted index member
  have link := holds altair current index.toNat ⟨flags, ?_, set⟩
  · obtain ⟨vote, cast, linked⟩ := link
    exact ⟨active, vote, linked, cast⟩
  · cases current
    · simpa [recentParticipation, distinct] using read
    · simpa [recentParticipation] using read

/-- A passing test of justification for an epoch gives the stake bound of its link, with churn.

The epoch is the current one when asked, and the previous one otherwise.

The test passes when twice the total active balance is at most three times the target balance.

The target balance is the total balance of a list of attesters.

Each of them must be active in that epoch, and have cast a vote of the set for its link.

The active stake of the current epoch must be more than one and a half increments.

The votes of the model must hold those of the data that the state signs, with blocks for roots.

The link goes from the justified checkpoint of the epoch to the checkpoint of the epoch.

The root of that checkpoint is the block root that the state records for its first slot. -/
theorem linkWithChurn_of_test (large : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun index => balanceAt state index.toNat)
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset)
    (block : Root → β) {votes : Set (Vote ValidatorIndex β)}
    (contains : ffgVotes block attested ⊆ votes)
    {current : Bool} {attesting : List ValidatorIndex} {total balance threshold weight : Gwei}
    {root : Root} (totalOk : getTotalActiveBalance state = .ok total)
    (balanceOk : getTotalBalance state attesting = .ok balance)
    (thresholdOk : mulChecked total 2 = .ok threshold)
    (weightOk : mulChecked balance 3 = .ok weight) (passed : threshold ≤ weight)
    (rootOk : getBlockRoot state
      (if current then getCurrentEpoch state else getPreviousEpoch state) = .ok root)
    (counted : ∀ index ∈ attesting,
      index ∈ getActiveValidatorIndices state
          (if current then getCurrentEpoch state else getPreviousEpoch state) ∧
        ∃ vote, LinkVote state current index.toNat vote ∧ vote ∈ attested) :
    LinkWithChurn state votes
      (if current then getCurrentEpoch state else getPreviousEpoch state)
      ((if current then state.currentJustifiedCheckpoint
        else state.previousJustifiedCheckpoint).toFfg block)
      (Checkpoint.toFfg block
        ⟨if current then getCurrentEpoch state else getPreviousEpoch state, root⟩) := by
  unfold LinkWithChurn
  refine stake_le_of_justificationTest totalOk balanceOk thresholdOk weightOk passed large
    fun index member => ?_
  obtain ⟨active, vote, link, signed⟩ := counted index (List.mem_toFinset.mp member)
  exact mem_signers_of_linkVote contains rootOk active link signed

/-- The counted attesters of each epoch whose test passes are voters of the link of that epoch.

The total is the active balance, and the two lists of attesters give the two target balances.

Each attester of an epoch must be active then and have cast a vote of the set for its link. -/
private theorem linkWithChurn_of_weigh (large : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun index => balanceAt state index.toNat)
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset)
    (block : Root → β) {votes : Set (Vote ValidatorIndex β)}
    (contains : ffgVotes block attested ⊆ votes)
    {total previousBalance currentBalance : Gwei} {previous current : List ValidatorIndex}
    (totalOk : getTotalActiveBalance state = .ok total)
    (previousOk : getTotalBalance state previous = .ok previousBalance)
    (currentOk : getTotalBalance state current = .ok currentBalance)
    (counted : ∀ (recent : Bool), ∀ index ∈ (if recent then current else previous),
      index ∈ getActiveValidatorIndices state
          (if recent then getCurrentEpoch state else getPreviousEpoch state) ∧
        ∃ vote, LinkVote state recent index.toNat vote ∧ vote ∈ attested)
    (recent : Bool) (threshold weight : Gwei) (root : Root)
    (thresholdOk : mulChecked total 2 = .ok threshold)
    (weightOk : mulChecked (if recent then currentBalance else previousBalance) 3 = .ok weight)
    (passed : threshold ≤ weight)
    (rootOk : getBlockRoot state
      (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok root) :
    LinkWithChurn state votes
      (if recent then getCurrentEpoch state else getPreviousEpoch state)
      ((if recent then state.currentJustifiedCheckpoint
        else state.previousJustifiedCheckpoint).toFfg block)
      (Checkpoint.toFfg block
        ⟨if recent then getCurrentEpoch state else getPreviousEpoch state, root⟩) := by
  have balanceOk : getTotalBalance state (if recent then current else previous) =
      .ok (if recent then currentBalance else previousBalance) := by
    cases recent
    · exact previousOk
    · exact currentOk
  exact linkWithChurn_of_test large block contains totalOk balanceOk thresholdOk weightOk passed
    rootOk (counted recent)

/-- Justification changes nothing, or weighs target balances that bound the links of passing tests.

From Altair each target flag must come from a vote of a set for the link of its epoch.

Before Altair each pending attestation of the two epochs must be a vote of the set for its link.

The active stake of the current epoch must be more than one and a half increments.

The votes of the model must hold those of the data that the state signs, with blocks for roots.

In the first two epochs the step leaves the state as it is.

Otherwise it weighs the total active balance and two target balances.

Each recent epoch whose test passes then gives the stake bound of its link, with churn.

A test passes when twice the total balance is at most three times the target balance.

The source of the link is the justified checkpoint of the epoch.

Its target is the checkpoint of the epoch, with the root the state records for its first slot. -/
theorem processJustificationAndFinalization_weighed
    (flagsVoted : TargetFlagsVoted attested state)
    (pendingVoted : PendingVoted attested state)
    (large : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun index => balanceAt state index.toNat)
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset)
    (block : Root → β) {votes : Set (Vote ValidatorIndex β)}
    (contains : ffgVotes block attested ⊆ votes)
    (computed : processJustificationAndFinalization state = .ok after) :
    (getCurrentEpoch state ≤ GENESIS_EPOCH + 1 ∧ after = state) ∨
      GENESIS_EPOCH + 1 < getCurrentEpoch state ∧ ∃ total previousBalance currentBalance : Gwei,
        getTotalActiveBalance state = .ok total ∧
        weighJustificationAndFinalization state total previousBalance currentBalance = .ok after ∧
          ∀ (recent : Bool) (threshold weight : Gwei) (root : Root),
            mulChecked total 2 = .ok threshold →
            mulChecked (if recent then currentBalance else previousBalance) 3 = .ok weight →
            threshold ≤ weight →
            getBlockRoot state
                (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok root →
              LinkWithChurn state votes
                (if recent then getCurrentEpoch state else getPreviousEpoch state)
                ((if recent then state.currentJustifiedCheckpoint
                  else state.previousJustifiedCheckpoint).toFfg block)
                (Checkpoint.toFfg block
                  ⟨if recent then getCurrentEpoch state else getPreviousEpoch state, root⟩) := by
  rcases processJustificationAndFinalization_reads computed with early | ⟨late, previous, current,
    total, previousBalance, currentBalance, previousOk, currentOk, totalOk, previousBalanceOk,
    currentBalanceOk, weighed⟩
  · exact .inl early
  refine .inr ⟨late, total, previousBalance, currentBalance, totalOk, weighed,
    linkWithChurn_of_weigh large block contains totalOk previousBalanceOk currentBalanceOk
      fun recent index member => ?_⟩
  have counted : targetIndices state
      (if recent then getCurrentEpoch state else getPreviousEpoch state) =
        .ok (if recent then current else previous) := by
    cases recent
    · exact previousOk
    · exact currentOk
  rcases targetIndices_ok counted with ⟨altair, counted⟩ |
    ⟨before, pending, pendingOk, indicesOk⟩
  · -- From Altair the counted attesters hold the target flag of the epoch.
    exact TargetFlagsVoted.attester altair flagsVoted (UInt64.not_le.mpr late) recent counted
      member
  · -- Before Altair the counted attesters cast a pending attestation of the epoch.
    have early : JustifiedEarly state := fun first => absurd first (UInt64.not_le.mpr late)
    obtain ⟨active, data, link, signed⟩ := PendingVoted.attester before
      pendingVoted early recent pendingOk indicesOk member
    exact ⟨active, (index, data), link, signed⟩

/-- Justification in the beacon chain gives the stake bound of a supermajority link of Casper FFG.

From Altair each target flag must come from a vote of a set for the link of its epoch.

Before Altair each pending attestation of the two epochs must be a vote of the set for its link.

The active stake of the current epoch must be more than one and a half increments.

The votes of the model must hold those of the data that the state signs, with blocks for roots.

Then the step keeps the current justified checkpoint.

Or it replaces it by the checkpoint of the previous or the current epoch, whose test passes.

In the second case, take the active set of that epoch as the validator set of the target.

When both epochs pass, this says nothing of the previous one.

The source is the justified checkpoint of that epoch, and the target is the new checkpoint.

Twice the stake of the target set is at most three times the stake of the voters of the link.

A term of churn adds twice the stake of the target set outside the current active set.

Each validator weighs its effective balance in the state before the step. -/
theorem processJustificationAndFinalization_linkWithChurn
    (flagsVoted : TargetFlagsVoted attested state)
    (pendingVoted : PendingVoted attested state)
    (large : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun index => balanceAt state index.toNat)
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset)
    (block : Root → β) {votes : Set (Vote ValidatorIndex β)}
    (contains : ffgVotes block attested ⊆ votes)
    (computed : processJustificationAndFinalization state = .ok after) :
    after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∨
      ∃ current : Bool,
        after.currentJustifiedCheckpoint.epoch =
            (if current then getCurrentEpoch state else getPreviousEpoch state) ∧
          getBlockRoot state after.currentJustifiedCheckpoint.epoch =
            .ok after.currentJustifiedCheckpoint.root ∧
          LinkWithChurn state votes
            (if current then getCurrentEpoch state else getPreviousEpoch state)
            ((if current then state.currentJustifiedCheckpoint
              else state.previousJustifiedCheckpoint).toFfg block)
            (after.currentJustifiedCheckpoint.toFfg block) := by
  rcases processJustificationAndFinalization_weighed (votes := votes) flagsVoted pendingVoted
    large block contains computed with ⟨-, same⟩ | ⟨-, _, _, _, -, weighed, link⟩
  · exact .inl (same ▸ rfl)
  rcases weighJustificationAndFinalization_currentJustified weighed with ⟨same, -⟩ | ⟨recent,
    threshold, weight, thresholdOk, weightOk, passed, epoch, rootOk⟩
  · exact .inl same
  refine .inr ⟨recent, epoch, rootOk, ?_⟩
  rw [epoch] at rootOk
  have checkpoint : after.currentJustifiedCheckpoint =
      ⟨if recent then getCurrentEpoch state else getPreviousEpoch state,
        after.currentJustifiedCheckpoint.root⟩ := by
    rw [← epoch]
  rw [checkpoint]
  exact link recent threshold weight _ thresholdOk weightOk passed rootOk

/-- The validators whose votes a state can count for a target.

Each is active in the epoch of the state or in the one before, and is not slashed. -/
def quorumVoters (state : BeaconState preset fork) : Finset ValidatorIndex :=
  {v ∈ (getActiveValidatorIndices state (getCurrentEpoch state) ++
      getActiveValidatorIndices state (getPreviousEpoch state)).toFinset |
    (state.validators.data[v.toNat]?.map (·.slashed)).getD true = false}

/-- The votes for the links of the two recent epochs have a target epoch at most the current one.

A target flag comes from a vote for the link of the current or the previous epoch.

A pending attestation is a vote for the link of the epoch of its list.

Either epoch is at most the current one.

So every such vote lies in the set of votes whose target epoch is at most the current epoch. -/
theorem TargetFlagsVoted.earlier {votes : Set (ValidatorIndex × AttestationData)}
    {state : BeaconState preset fork}
    (flags : TargetFlagsVoted votes state) (pending : PendingVoted votes state) :
    TargetFlagsVoted {vote | vote.2.target.epoch ≤ getCurrentEpoch state} state ∧
      PendingVoted {vote | vote.2.target.epoch ≤ getCurrentEpoch state} state := by
  -- The current and the previous epoch are both at most the current one.
  have recent : ∀ current : Bool,
      (if current then getCurrentEpoch state else getPreviousEpoch state) ≤
        getCurrentEpoch state := fun current => by
    cases current
    · exact getPreviousEpoch_le state
    · exact UInt64.le_refl _
  refine ⟨fun altair current position flagged => ?_, fun before current attestation member => ?_⟩
  · -- The vote behind a flag has the target epoch of the flag.
    obtain ⟨vote, -, link⟩ := flags altair current position flagged
    exact ⟨vote, show _ ≤ _ from link.2.1 ▸ recent current, link⟩
  · -- Each vote of a pending attestation holds its data, whose target epoch is that of its list.
    obtain ⟨epoch, slot, source, -⟩ := pending before current attestation member
    exact ⟨epoch, slot, source, fun _ _ _ _ => show _ ≤ _ from epoch ▸ recent current⟩

/-- Each attester that justification counts for a recent epoch is a quorum voter with a vote.

It is active in that epoch, the current or the previous one, and not slashed.

It cast a vote of the set for the link of that epoch.

From Altair the target flags give the vote, and before Altair the pending attestations do.

Justification must run, so the current epoch must be past the first two. -/
private theorem counted_quorumVoter {attested : Set (ValidatorIndex × AttestationData)}
    {state : BeaconState preset fork}
    (flagsVoted : TargetFlagsVoted attested state) (pendingVoted : PendingVoted attested state)
    (late : GENESIS_EPOCH + 1 < getCurrentEpoch state) (current : Bool)
    {indices : List ValidatorIndex}
    (counted : targetIndices state
      (if current then getCurrentEpoch state else getPreviousEpoch state) = .ok indices)
    {index : ValidatorIndex} (member : index ∈ indices) :
    index ∈ quorumVoters state ∧
      ∃ vote ∈ attested, LinkVote state current index.toNat vote := by
  -- An active validator of a recent epoch that is not slashed is a quorum voter.
  have voter : index ∈ getActiveValidatorIndices state
        (if current then getCurrentEpoch state else getPreviousEpoch state) →
      (∃ validator, getValidator state index = .ok validator ∧ validator.slashed = false) →
      index ∈ quorumVoters state := by
    rintro active ⟨validator, found, unslashed⟩
    rw [getValidator_eq_ok_iff] at found
    simp only [quorumVoters, Finset.mem_filter, List.mem_toFinset, List.mem_append, found,
      Option.map_some, Option.getD_some, unslashed, and_true]
    cases current
    · exact .inr active
    · exact .inl active
  rcases targetIndices_ok counted with ⟨altair, counted⟩ |
    ⟨before, pending, pendingOk, indicesOk⟩
  · -- From Altair the counted attesters are unslashed and hold the target flag of the epoch.
    obtain ⟨active, unslashed, -⟩ := mem_getUnslashedParticipatingIndices counted index member
    obtain ⟨-, vote, link, cast⟩ := TargetFlagsVoted.attester altair flagsVoted
      (UInt64.not_le.mpr late) current counted member
    exact ⟨voter active unslashed, vote, cast, link⟩
  · -- Before Altair the counted attesters cast a pending attestation of the epoch.
    have early : JustifiedEarly state := fun first => absurd first (UInt64.not_le.mpr late)
    obtain ⟨active, data, link, cast⟩ := PendingVoted.attester before
      pendingVoted early current pendingOk indicesOk member
    -- The filter of unslashed attesters kept the attester, so its validator is not slashed.
    simp only [getUnslashedAttestingIndices, bind_ok_iff, unslashedAmong] at indicesOk
    obtain ⟨_, _, filtered⟩ := indicesOk
    have passes := passes_of_mem_filterM_ok filtered member
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at passes
    obtain ⟨validator, found, fresh⟩ := passes
    exact ⟨voter active ⟨validator, found, by simpa using fresh⟩, (index, data), cast, link⟩

/-- When justification moves the current justified checkpoint, a voter with a property voted for it.

The property must leave out too little stake to justify alone.

That is, three times the stake of the quorum voters without the property is below twice the total.

The step justifies the checkpoint of the current or the previous epoch only when its test passes.

That is the justification rule of `process_justification_and_finalization`.

It follows Gasper §4.4, Definition 4.5, a supermajority link to the checkpoint.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).

The test asks twice the total active balance to be at most three times the target balance.

The target balance counts unslashed attesters that are active in that epoch.

So they are quorum voters.

If none of them had the property, the test would fail by the bound on the voters without it.

So one of them has it, and it cast a vote of the set for the link of the epoch.

The target of that vote is the new checkpoint.

Its epoch is that epoch, and its root is the block root that the state records for that epoch.

The active stake of the current epoch must be more than one and a half increments.

Then the test compares stakes, without the floor of one increment on each balance. -/
theorem processJustificationAndFinalization_exists_voter
    {attested : Set (ValidatorIndex × AttestationData)} {state after : BeaconState preset fork}
    (p : ValidatorIndex → Prop) [DecidablePred p]
    (flagsVoted : TargetFlagsVoted attested state) (pendingVoted : PendingVoted attested state)
    (large : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun index => balanceAt state index.toNat)
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset)
    (few : ∀ total, getTotalActiveBalance state = .ok total →
      3 * stake (fun index => balanceAt state index.toNat) {v ∈ quorumVoters state | ¬p v} <
        2 * total.toNat)
    (computed : processJustificationAndFinalization state = .ok after)
    (changed : after.currentJustifiedCheckpoint ≠ state.currentJustifiedCheckpoint) :
    ∃ current : Bool, ∃ vote ∈ attested, p vote.1 ∧
      LinkVote state current vote.1.toNat vote ∧
      vote.2.target = after.currentJustifiedCheckpoint := by
  -- In the first two epochs the step changes nothing, so justification ran.
  rcases processJustificationAndFinalization_reads computed with ⟨-, same⟩ | ⟨late, previous,
    current, total, previousBalance, currentBalance, previousOk, currentOk, totalOk,
    previousBalanceOk, currentBalanceOk, weighed⟩
  · exact absurd (same ▸ rfl) changed
  -- The checkpoint moved, so the test of a recent epoch passed, and the checkpoint is its own.
  rcases weighJustificationAndFinalization_currentJustified weighed with ⟨same, -⟩ | ⟨recent,
    threshold, weight, thresholdOk, weightOk, passed, epoch, rootOk⟩
  · exact absurd same changed
  have counted : targetIndices state
      (if recent then getCurrentEpoch state else getPreviousEpoch state) =
        .ok (if recent then current else previous) := by
    cases recent
    · exact previousOk
    · exact currentOk
  have balanceOk : getTotalBalance state (if recent then current else previous) =
      .ok (if recent then currentBalance else previousBalance) := by
    cases recent
    · exact previousBalanceOk
    · exact currentBalanceOk
  by_cases found : ∃ index ∈ (if recent then current else previous), p index
  · obtain ⟨index, member, holds⟩ := found
    obtain ⟨-, vote, cast, link⟩ :=
      counted_quorumVoter flagsVoted pendingVoted late recent counted member
    -- The vote is cast by the attester itself.
    have voter : vote.1 = index := UInt64.toNat_inj.mp link.1
    refine ⟨recent, vote, cast, voter ▸ holds, voter ▸ link, ?_⟩
    -- The target has the epoch of the new checkpoint, and the root the state records for it.
    obtain ⟨-, targetEpoch, -, targetRoot⟩ := link
    have sameEpoch : vote.2.target.epoch = after.currentJustifiedCheckpoint.epoch :=
      targetEpoch.trans epoch.symm
    rw [sameEpoch, rootOk, Except.ok.injEq] at targetRoot
    -- Two checkpoints with the same epoch and the same root are equal.
    cases target : vote.2.target
    cases checkpoint : after.currentJustifiedCheckpoint
    rw [target] at sameEpoch targetRoot
    rw [checkpoint] at sameEpoch targetRoot
    simp only at sameEpoch targetRoot
    rw [sameEpoch, targetRoot]
  · -- Otherwise every counted attester is a quorum voter without the property.
    exfalso
    have subset : (if recent then current else previous).toFinset ⊆
        {v ∈ quorumVoters state | ¬p v} := fun index member => by
      have listed := List.mem_toFinset.mp member
      exact Finset.mem_filter.mpr
        ⟨(counted_quorumVoter flagsVoted pendingVoted late recent counted listed).1,
          fun holds => found ⟨index, listed, holds⟩⟩
    -- Above one and a half increments, the passing test bounds the active stake.
    have test := (justificationTest_iff_stake (getTotalActiveBalance_ok totalOk) balanceOk
      thresholdOk weightOk large).mp passed
    have attesters := stake_mono (w := fun index => balanceAt state index.toNat) subset
    -- The total is the active stake, since that is above one increment.
    obtain ⟨-, -, totalEq⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok totalOk)
    have bound := few total totalOk
    rw [totalEq] at bound
    omega

end EthLib.Consensus
