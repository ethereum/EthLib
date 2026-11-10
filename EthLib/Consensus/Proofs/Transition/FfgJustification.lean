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

It signed a vote whose source is the justified checkpoint of that epoch.

The target of that vote is the checkpoint of the epoch.

Its root is the block root that the state records for the first slot of the epoch.

From Altair the target flags give that, and before Altair the pending attestations do.

The step drops slashed attesters, so the attesters are a subset of the voters of the model.

The step divides by the active stake of the current epoch, not of the epoch of the target.

For the previous epoch, the validators that exit at the current epoch count in the target set.

They do not count in that total, so their stake enters the bound as a term of churn.

For the current epoch that term is the stake of the empty set, zero.

Gasper §4.4, Definitions 4.5 and 4.6, justify a checkpoint by a supermajority link.

Gasper §8.6, Lemma 8.2, gives each justified checkpoint its own validator set.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Models.Ffg

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork} {β : Type*}

/-- The stake bound of a supermajority link of Casper FFG, up to a term of churn.

The validator set is the active set of the given epoch, which should be the epoch of the target.

Each validator weighs its effective balance in the state.

The model needs that set and those stakes fixed across states, which this does not show.

Twice the stake of that set is at most three times the stake of its voters for the link.

The term of churn adds twice the stake of that set outside the active set of the current epoch.

The model asks for the bound without that term, and also orders the source before the target. -/
def LinkWithChurn (state : BeaconState preset fork) (votes : Set (Vote ValidatorIndex β))
    (epoch : Epoch) (source target : Models.Ffg.Checkpoint β) : Prop :=
  2 * stake (fun index => balanceAt state index.toNat)
      (getActiveValidatorIndices state epoch).toFinset ≤
    3 * stake (fun index => balanceAt state index.toNat)
        (signers (getActiveValidatorIndices state epoch).toFinset votes source target) +
      2 * stake (fun index => balanceAt state index.toNat)
        ((getActiveValidatorIndices state epoch).toFinset \
          (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset)

/-- A signed vote for the link of an epoch, by an active validator, is a voter of the model.

The vote of the model goes from the justified checkpoint of the epoch to its checkpoint.

The root of that checkpoint is the block root that the state records for its first slot.

The voter belongs to the active set of that epoch. -/
theorem mem_signers_of_linkVote {block : Root → β} {votes : Set (Vote ValidatorIndex β)}
    (contains : ffgVotes block {vote | SignedVote config checks state vote} ⊆ votes)
    {current : Bool} {root : Root}
    (rootOk : getBlockRoot state
      (if current then getCurrentEpoch state else getPreviousEpoch state) = .ok root)
    {index : ValidatorIndex}
    (active : index ∈ getActiveValidatorIndices state
      (if current then getCurrentEpoch state else getPreviousEpoch state))
    {vote : ValidatorIndex × AttestationData} (link : LinkVote state current index.toNat vote)
    (signed : SignedVote config checks state vote) :
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
  refine ⟨active, contains ⟨(validator, data), signed, ?_⟩⟩
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
  have test := (justificationTest_iff_stake totalOk balanceOk thresholdOk weightOk large).mp passed
  have attesters := stake_mono (w := fun index => balanceAt state index.toNat) subset
  have split := stake_add_stake_sdiff (w := fun index => balanceAt state index.toNat)
    (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset target
  omega

/-- A passing test of justification for an epoch gives the stake bound of its link, with churn.

The epoch is the current one when asked, and the previous one otherwise.

The test passes when twice the total active balance is at most three times the target balance.

The target balance is the total balance of a list of attesters.

Each of them must be active in that epoch, and have signed a vote for the link of the epoch.

The active stake of the current epoch must be more than one and a half increments.

The votes of the model must hold those of the data that the state signs, with blocks for roots.

The link goes from the justified checkpoint of the epoch to the checkpoint of the epoch.

The root of that checkpoint is the block root that the state records for its first slot. -/
theorem linkWithChurn_of_test (large : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun index => balanceAt state index.toNat)
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset)
    (block : Root → β) {votes : Set (Vote ValidatorIndex β)}
    (contains : ffgVotes block {vote | SignedVote config checks state vote} ⊆ votes)
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
        ∃ vote, LinkVote state current index.toNat vote ∧ SignedVote config checks state vote) :
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

Each attester of an epoch must be active then and have signed a vote for the link of the epoch. -/
private theorem linkWithChurn_of_weigh (large : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun index => balanceAt state index.toNat)
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset)
    (block : Root → β) {votes : Set (Vote ValidatorIndex β)}
    (contains : ffgVotes block {vote | SignedVote config checks state vote} ⊆ votes)
    {total previousBalance currentBalance : Gwei} {previous current : List ValidatorIndex}
    (totalOk : getTotalActiveBalance state = .ok total)
    (previousOk : getTotalBalance state previous = .ok previousBalance)
    (currentOk : getTotalBalance state current = .ok currentBalance)
    (counted : ∀ (recent : Bool), ∀ index ∈ (if recent then current else previous),
      index ∈ getActiveValidatorIndices state
          (if recent then getCurrentEpoch state else getPreviousEpoch state) ∧
        ∃ vote, LinkVote state recent index.toNat vote ∧ SignedVote config checks state vote)
    (weighed : weighJustificationAndFinalization state total previousBalance currentBalance =
      .ok after) :
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
  rcases weighJustificationAndFinalization_currentJustified weighed with ⟨same, -⟩ | ⟨recent,
    threshold, weight, thresholdOk, weightOk, passed, epoch, rootOk⟩
  · exact .inl same
  refine .inr ⟨recent, epoch, rootOk, ?_⟩
  have balanceOk : getTotalBalance state (if recent then current else previous) =
      .ok (if recent then currentBalance else previousBalance) := by
    cases recent
    · exact previousOk
    · exact currentOk
  rw [epoch] at rootOk
  have checkpoint : after.currentJustifiedCheckpoint =
      ⟨if recent then getCurrentEpoch state else getPreviousEpoch state,
        after.currentJustifiedCheckpoint.root⟩ := by
    rw [← epoch]
  rw [checkpoint]
  exact linkWithChurn_of_test large block contains totalOk balanceOk thresholdOk weightOk passed
    rootOk (counted recent)

/-- Justification in the beacon chain gives the stake bound of a supermajority link of Casper FFG.

From Altair each target flag must come from a signed vote for the link of its epoch.

Before Altair each pending attestation of the two epochs must be a signed vote for its link.

The active stake of the current epoch must be more than one and a half increments.

The votes of the model must hold those of the data that the state signs, with blocks for roots.

Then the step keeps the current justified checkpoint.

Or it replaces it by the checkpoint of the newest epoch whose test passes, the previous or current.

In the second case, take the active set of that epoch as the validator set of the target.

When both epochs pass, this says nothing of the previous one.

The source is the justified checkpoint of that epoch, and the target is the new checkpoint.

Twice the stake of the target set is at most three times the stake of the voters of the link.

A term of churn adds twice the stake of the target set outside the current active set.

Each validator weighs its effective balance in the state before the step. -/
theorem processJustificationAndFinalization_linkWithChurn
    (flagsSigned : TargetFlagsSigned config checks state)
    (pendingSigned : PendingSigned config checks state)
    (large : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun index => balanceAt state index.toNat)
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset)
    (block : Root → β) {votes : Set (Vote ValidatorIndex β)}
    (contains : ffgVotes block {vote | SignedVote config checks state vote} ⊆ votes)
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
  unfold processJustificationAndFinalization at computed
  split at computed
  · rename_i altair
    unfold processJustificationAndFinalizationAltair at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact .inl (computed ▸ rfl)
    rename_i late
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨previous, previousOk, current, currentOk, total, totalOk, previousBalance,
      previousBalanceOk, currentBalance, currentBalanceOk, weighed⟩ := computed
    refine linkWithChurn_of_weigh large block contains totalOk previousBalanceOk
      currentBalanceOk (fun recent index member => ?_) weighed
    -- From Altair the counted attesters hold the target flag of the epoch.
    have distinct : getPreviousEpoch state ≠ getCurrentEpoch state := by
      intro same
      have := congrArg UInt64.toNat same
      rw [getPreviousEpoch_toNat] at this
      exact late (UInt64.le_iff_toNat_le.mpr (by simp [GENESIS_EPOCH]; omega))
    have flagged : ∀ {epoch : Epoch} {indices : List ValidatorIndex},
        getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX epoch =
          .ok indices →
        epoch = (if recent then getCurrentEpoch state else getPreviousEpoch state) →
        index ∈ indices →
        index ∈ getActiveValidatorIndices state
            (if recent then getCurrentEpoch state else getPreviousEpoch state) ∧
          ∃ vote, LinkVote state recent index.toNat vote ∧
            SignedVote config checks state vote := by
      intro epoch indices indicesOk same inside
      obtain ⟨active, -, flags, read, set⟩ := mem_getUnslashedParticipatingIndices indicesOk index
        inside
      subst same
      refine ⟨active, flagsSigned altair recent index.toNat ⟨flags, ?_, set⟩⟩
      cases recent
      · simpa [recentParticipation, distinct] using read
      · simpa [recentParticipation] using read
    cases recent
    · exact flagged previousOk rfl member
    · exact flagged currentOk rfl member
  · rename_i notAltair
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact .inl (computed ▸ rfl)
    rename_i late
    simp only [bind_ok_iff, liftAccessor_ok, getAttestingBalance] at computed
    obtain ⟨previous, previousOk, current, currentOk, total, totalOk, previousBalance,
      ⟨previousIndices, previousIndicesOk, previousBalanceOk⟩, currentBalance,
      ⟨currentIndices, currentIndicesOk, currentBalanceOk⟩, weighed⟩ := computed
    refine linkWithChurn_of_weigh large block contains totalOk previousBalanceOk
      currentBalanceOk (fun recent index member => ?_) weighed
    -- Before Altair the counted attesters signed a pending attestation of the epoch.
    have early : JustifiedEarly state := fun first => absurd first late
    have attester : index ∈ getActiveValidatorIndices state
          (if recent then getCurrentEpoch state else getPreviousEpoch state) ∧
        ∃ data, LinkVote state recent index.toNat (index, data) ∧
          SignedVote config checks state (index, data) := by
      cases recent
      · exact PendingSigned.attester (Nat.lt_of_not_le notAltair) pendingSigned early false
          previousOk previousIndicesOk member
      · exact PendingSigned.attester (Nat.lt_of_not_le notAltair) pendingSigned early true
          currentOk currentIndicesOk member
    obtain ⟨active, data, link, signed⟩ := attester
    exact ⟨active, (index, data), link, signed⟩

end EthLib.Consensus
