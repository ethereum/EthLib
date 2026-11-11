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
  unfold processJustificationAndFinalization at computed
  split at computed
  · rename_i altair
    unfold processJustificationAndFinalizationAltair at computed
    split at computed
    · rename_i early
      simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact .inl ⟨early, computed.symm⟩
    rename_i late
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨previous, previousOk, current, currentOk, total, totalOk, previousBalance,
      previousBalanceOk, currentBalance, currentBalanceOk, weighed⟩ := computed
    refine .inr ⟨UInt64.not_le.mp late, total, previousBalance, currentBalance, totalOk,
      weighed, linkWithChurn_of_weigh large block contains totalOk previousBalanceOk
        currentBalanceOk fun recent index member => ?_⟩
    -- From Altair the counted attesters hold the target flag of the epoch.
    cases recent
    · exact TargetFlagsVoted.attester altair flagsVoted late false previousOk member
    · exact TargetFlagsVoted.attester altair flagsVoted late true currentOk member
  · rename_i notAltair
    split at computed
    · rename_i early
      simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact .inl ⟨early, computed.symm⟩
    rename_i late
    simp only [bind_ok_iff, liftAccessor_ok, getAttestingBalance] at computed
    obtain ⟨previous, previousOk, current, currentOk, total, totalOk, previousBalance,
      ⟨previousIndices, previousIndicesOk, previousBalanceOk⟩, currentBalance,
      ⟨currentIndices, currentIndicesOk, currentBalanceOk⟩, weighed⟩ := computed
    refine .inr ⟨UInt64.not_le.mp late, total, previousBalance, currentBalance, totalOk,
      weighed, linkWithChurn_of_weigh large block contains totalOk previousBalanceOk
        currentBalanceOk fun recent index member => ?_⟩
    -- Before Altair the counted attesters cast a pending attestation of the epoch.
    have early : JustifiedEarly state := fun first => absurd first late
    have attester : index ∈ getActiveValidatorIndices state
          (if recent then getCurrentEpoch state else getPreviousEpoch state) ∧
        ∃ data, LinkVote state recent index.toNat (index, data) ∧
          (index, data) ∈ attested := by
      cases recent
      · exact PendingVoted.attester (Nat.lt_of_not_le notAltair) pendingVoted early false
          previousOk previousIndicesOk member
      · exact PendingVoted.attester (Nat.lt_of_not_le notAltair) pendingVoted early true
          currentOk currentIndicesOk member
    obtain ⟨active, data, link, signed⟩ := attester
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

end EthLib.Consensus
