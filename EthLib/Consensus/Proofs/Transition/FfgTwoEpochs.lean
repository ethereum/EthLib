module

public import EthLib.Consensus.Proofs.Transition.EpochJustification
public import EthLib.Consensus.Proofs.Transition.FfgStake

/-!
# Proofs: two epochs of honest target votes finalize the first

This is the step of plausible liveness that turns votes into finality, Theorem 2 of Casper FFG.

The paper is [arXiv 1710.09437v4](https://arxiv.org/abs/1710.09437v4).

Each test is read here from honest validators with two thirds of the active stake.

They must all be among the validators that justification counts for the target of the epoch.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-- A test of the current epoch that passes justifies that epoch and sets the newest bit.

A test passes when twice the total balance is at most three times the target balance. -/
theorem weighJustificationAndFinalization_currentPassed {total previous current : Gwei}
    (computed : weighJustificationAndFinalization state total previous current = .ok after)
    (quorum : 2 * total.toNat ≤ 3 * current.toNat) :
    after.justificationBits.bits[0] = true ∧
      after.currentJustifiedCheckpoint.epoch = getCurrentEpoch state := by
  -- At the end of an epoch, justification tests the target balance of that epoch.
  --
  -- The test passes when three times that balance reaches twice the active balance.
  --
  -- Then the epoch becomes the current justified one, and the newest bit of justification is set.
  simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨previousWeight, previousOk, threshold, thresholdOk, first, firstOk, currentWeight,
    currentOk, second, secondOk, _, _, _, _, _, _, _, _, rfl⟩ := computed
  have thresholdEq := (mulChecked_ok_iff.mp thresholdOk).2
  have currentEq := (mulChecked_ok_iff.mp currentOk).2
  have passed : threshold ≤ currentWeight := by
    simp only [UInt64.le_iff_toNat_le]
    simp only [UInt64.toNat_ofNat] at thresholdEq currentEq
    omega
  have secondEpoch := (justifyCheckpoint_ok secondOk).resolve_right
    (by simp [decide_eq_true passed])
  exact ⟨by simp [passed], secondEpoch.2.1⟩

/-- A test of the current epoch that passes finalizes the old current justified checkpoint.

That checkpoint must be one epoch back, with the newest bit set before the step.

The bit says that the test of that epoch passed at its end. -/
theorem weighJustificationAndFinalization_finalizesCurrent {total previous current : Gwei}
    (computed : weighJustificationAndFinalization state total previous current = .ok after)
    (bit : state.justificationBits.bits[0] = true)
    (gap : state.currentJustifiedCheckpoint.epoch.toNat + 1 = (getCurrentEpoch state).toNat)
    (quorum : 2 * total.toNat ≤ 3 * current.toNat) :
    after.finalizedCheckpoint = state.currentJustifiedCheckpoint := by
  simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨previousWeight, previousOk, threshold, thresholdOk, first, firstOk, currentWeight,
    currentOk, second, secondOk, _, _, _, _, _, _, oneBack, oneBackOk, rfl⟩ := computed
  have thresholdEq := (mulChecked_ok_iff.mp thresholdOk).2
  have currentEq := (mulChecked_ok_iff.mp currentOk).2
  have passed : threshold ≤ currentWeight := by
    simp only [UInt64.le_iff_toNat_le]
    simp only [UInt64.toNat_ofNat] at thresholdEq currentEq
    omega
  -- The newest bit is set now, and the old newest bit moved to the second place.
  have shifted : (shiftJustificationBits state.justificationBits)[1] = true := by
    simp [shiftJustificationBits, bit]
  have justified : oneBack = true := by
    simp only [passed, decide_true, shifted, Bool.or_true] at oneBackOk
    -- The sum of the old epoch and one fits, since it is the current epoch.
    have sumOk : addChecked state.currentJustifiedCheckpoint.epoch 1 =
        .ok (getCurrentEpoch state) := addChecked_ok_iff.mpr ⟨by
          simp only [UInt64.reduceToNat]; have := (getCurrentEpoch state).toNat_lt; omega,
        by simp only [UInt64.reduceToNat]; omega⟩
    simp only [finalizes, liftArith, sumOk, pure, Except.pure] at oneBackOk
    simpa [Except.mapError, liftAccessor, bind, Except.bind] using oneBackOk.symm
  simp [justified]

/-- Honest validators with two thirds of the active stake pass the test of the current epoch.

The active stake is that of the current epoch, with effective balances.

Every target index that justification counts for the epoch must include the honest set. -/
private theorem weighJustificationAndFinalization_of_honest
    (computed : processJustificationAndFinalization state = .ok after)
    (late : GENESIS_EPOCH + 1 < getCurrentEpoch state)
    {honest : Finset ValidatorIndex}
    -- From Altair, justification counts the unslashed validators with the timely target flag.
    (counted : ∀ indices, targetIndices state (getCurrentEpoch state) = .ok indices →
      honest ⊆ indices.toFinset)
    (quorum : 2 * stake (fun index => balanceAt state index.toNat)
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset ≤
      3 * stake (fun index => balanceAt state index.toNat) honest) :
    ∃ total previous current : Gwei,
      weighJustificationAndFinalization state total previous current = .ok after ∧
        2 * total.toNat ≤ 3 * current.toNat := by
  rcases processJustificationAndFinalization_reads computed with ⟨early, -⟩ | ⟨-, _, indices, total,
    previousBalance, currentBalance, -, currentOk, totalOk, -, balanceOk, weighed⟩
  · exact absurd early (UInt64.not_le.mpr late)
  refine ⟨total, previousBalance, currentBalance, weighed, ?_⟩
  -- The honest stake bounds the target stake, and each balance is a stake raised to one increment.
  have more := stake_mono (w := fun index => balanceAt state index.toNat)
    (counted indices currentOk)
  obtain ⟨-, -, totalEq⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok totalOk)
  obtain ⟨-, -, balanceEq⟩ := getTotalBalance_ok_iff_stake.mp balanceOk
  rw [totalEq, balanceEq]
  omega

/-- Honest validators with two thirds of the active stake justify the current epoch at its end.

The newest bit of justification is then set.

The active stake is that of the current epoch, with effective balances.

Justification must run, after the first two epochs.

Every target index that justification counts for the epoch must include the honest set. -/
theorem processJustificationAndFinalization_justifiesCurrent
    (computed : processJustificationAndFinalization state = .ok after)
    (late : GENESIS_EPOCH + 1 < getCurrentEpoch state)
    {honest : Finset ValidatorIndex}
    -- Every target index that justification counts for the epoch must include the honest set.
    (counted : ∀ indices, targetIndices state (getCurrentEpoch state) = .ok indices →
      honest ⊆ indices.toFinset)
    (quorum : 2 * stake (fun index => balanceAt state index.toNat)
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset ≤
      3 * stake (fun index => balanceAt state index.toNat) honest) :
    after.justificationBits.bits[0] = true ∧
      after.currentJustifiedCheckpoint.epoch = getCurrentEpoch state := by
  obtain ⟨_, _, _, weighed, passed⟩ :=
    weighJustificationAndFinalization_of_honest computed late counted quorum
  exact weighJustificationAndFinalization_currentPassed weighed passed

/-- Two epochs of honest target votes justify both epochs and finalize the first.

The first step ends an epoch, and the second step ends the next one.

Between them the current justified checkpoint and the bits of justification stay as they are.

In each step, honest validators with two thirds of the active stake count for the target.

Justification must run in the first step, after the first two epochs.

Then the second step finalizes the checkpoint of the first epoch.

The current justified checkpoint after the second step is that of the second epoch.

The two states may be at different forks, as when an upgrade comes between the two steps. -/
theorem processJustificationAndFinalization_finalizesTwoEpochs {fork' : Base.Fork}
    {first firstAfter : BeaconState preset fork} {second secondAfter : BeaconState preset fork'}
    {firstHonest secondHonest : Finset ValidatorIndex}
    (firstComputed : processJustificationAndFinalization first = .ok firstAfter)
    -- Justification must run in the first step, after the first two epochs.
    (late : GENESIS_EPOCH + 1 < getCurrentEpoch first)
    (firstCounted : ∀ indices, targetIndices first (getCurrentEpoch first) = .ok indices →
      firstHonest ⊆ indices.toFinset)
    (firstQuorum : 2 * stake (fun index => balanceAt first index.toNat)
        (getActiveValidatorIndices first (getCurrentEpoch first)).toFinset ≤
      3 * stake (fun index => balanceAt first index.toNat) firstHonest)
    -- Between the steps the current justified checkpoint and the bits of justification stay.
    (justifiedKept : second.currentJustifiedCheckpoint = firstAfter.currentJustifiedCheckpoint)
    (bitsKept : second.justificationBits = firstAfter.justificationBits)
    (next : (getCurrentEpoch second).toNat = (getCurrentEpoch first).toNat + 1)
    (secondComputed : processJustificationAndFinalization second = .ok secondAfter)
    (secondCounted : ∀ indices, targetIndices second (getCurrentEpoch second) = .ok indices →
      secondHonest ⊆ indices.toFinset)
    (secondQuorum : 2 * stake (fun index => balanceAt second index.toNat)
        (getActiveValidatorIndices second (getCurrentEpoch second)).toFinset ≤
      3 * stake (fun index => balanceAt second index.toNat) secondHonest) :
    secondAfter.finalizedCheckpoint = firstAfter.currentJustifiedCheckpoint ∧
      secondAfter.finalizedCheckpoint.epoch = getCurrentEpoch first ∧
      secondAfter.currentJustifiedCheckpoint.epoch = getCurrentEpoch second := by
  obtain ⟨firstBit, firstEpoch⟩ := processJustificationAndFinalization_justifiesCurrent
    firstComputed late firstCounted firstQuorum
  have secondLate : GENESIS_EPOCH + 1 < getCurrentEpoch second := by
    rw [UInt64.lt_iff_toNat_lt, next]
    exact Nat.lt_succ_of_lt (UInt64.lt_iff_toNat_lt.mp late)
  obtain ⟨_, _, _, weighed, passed⟩ := weighJustificationAndFinalization_of_honest
    secondComputed secondLate secondCounted secondQuorum
  -- At the end of the next epoch the newest bit of the first step is the second newest.
  --
  -- The test of that next epoch passes too, so a rule of finalization applies.
  --
  -- It finalizes the justified checkpoint of the first epoch, one epoch back.
  have finalized := weighJustificationAndFinalization_finalizesCurrent weighed
    (by rw [bitsKept]; exact firstBit)
    (by rw [justifiedKept, firstEpoch, next]) passed
  rw [justifiedKept] at finalized
  -- The current justified checkpoint after the second step is that of the second epoch.
  exact ⟨finalized, by rw [finalized, firstEpoch],
    (weighJustificationAndFinalization_currentPassed weighed passed).2⟩

end EthLib.Consensus
