module

public import EthLib.Consensus.Proofs.Transition.EpochParticipation

/-!
# Proofs: one epoch of an inactivity leak, from Altair

The chain leaks when the finalized epoch is over four epochs behind the previous one, on mainnet.

Then the update of the inactivity scores runs, and then the rewards and penalties.

These proofs state what the two steps do to each validator in such an epoch.

Each step changes one field: the scores, then the balances.

An eligible validator that set the target flag loses one point of score, stopping at zero.

Any other eligible validator gains the score bias, 4 on mainnet.

In a leak no flag earns a reward, so no balance rises in these two steps.

Proposers and sync committees still earn rewards in the blocks.

A validator pays the weight of each of the source and target flags that it did not set.

That weight is a share of its base reward, 14/64 for the source and 26/64 for the target.

A validator that did not set the target flag also pays an inactivity penalty.

That penalty is its effective balance times its new score, over the score bias times a quotient.

The quotient is `3 * 2^24` at Altair and `2^24` from Bellatrix, on mainnet.

So the divisor is `3 * 2^26` at Altair and `2^26` from Bellatrix.

A validator that set the source and target flags thus keeps its balance.

This is the discrete rule behind the model of [Pavloff et al.][pat].

Its Section 4.1, Equation 1, gives the score, and its Section 4.2, Equation 2, the penalty.

That model differs from the rule in several ways.

It ignores the penalties of the flags, and the rounding of each quotient.

It uses the stake where the rule uses the effective balance.

Its Equation 2 charges every validator with a score, where the rule spares those with the target.

Its divisor `2^26` is that from Bellatrix.

Its leak starts after four epochs without finality, where the rule asks for a delay above four.

Its active validator votes for the right target.

The rule asks for the timely target flag, from an unslashed active validator.

So a slashed validator that is still eligible always counts as absent.

The update at the end of an epoch reads the flags of the epoch before it.

In the rule the penalty uses the score already raised in the same epoch.

[pat]: https://arxiv.org/abs/2404.16363v2
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {state scored after : BeaconState preset fork}

/-- On mainnet the divisor of the inactivity penalty is `3 * 2^26` at Altair.

From Bellatrix it is `2^26`.

The divisor is the score bias times the penalty quotient of the fork. -/
theorem scoreBias_mul_inactivityPenaltyQuotient_mainnet (altair : .altair ≤ fork) :
    Config.mainnet.INACTIVITY_SCORE_BIAS.toNat *
        (parameters Preset.mainnet fork).INACTIVITY_PENALTY_QUOTIENT.toNat =
      if .bellatrix ≤ fork then 2 ^ 26 else 3 * 2 ^ 26 := by
  have notPhase0 : ¬ fork < .altair := Nat.not_lt_of_le altair
  unfold parameters
  by_cases bellatrix : .bellatrix ≤ fork <;> simp [bellatrix, altair] <;> decide

/-- From Altair and after the first epoch, a successful step finds a balance for each validator.

The registry is that of the state before the step. -/
private theorem balances_present_of_altair {config : Config} (altair : .altair ≤ fork)
    (later : getCurrentEpoch state ≠ GENESIS_EPOCH)
    (computed : processRewardsAndPenalties config state = .ok after) :
    ∀ j < state.validators.data.size, ∃ balance, state.balances.data[j]? = some balance := by
  intro j inside
  simp only [processRewardsAndPenalties, later, altair, ↓reduceIte, ↓reduceDIte,
    bind_ok_iff] at computed
  obtain ⟨flagDeltas, _, inactivityDeltas, _, applied⟩ := computed
  obtain ⟨⟨rewards, penalties⟩, rest, split⟩ :
      ∃ first rest, flagDeltas ++ [inactivityDeltas] = first :: rest := by
    cases flagDeltas with
    | nil => exact ⟨_, _, rfl⟩
    | cons first rest => exact ⟨_, _, rfl⟩
  rw [split, List.foldlM_cons, bind_ok_iff] at applied
  obtain ⟨_, first, _⟩ := applied
  obtain ⟨balance, found, -⟩ := (applyAllDeltas_balances first j).1 inside
  exact ⟨balance, found⟩

/-- A leak never holds in the first epoch. -/
theorem getCurrentEpoch_ne_genesis_of_leak (leak : isInInactivityLeak state = .ok true) :
    getCurrentEpoch state ≠ GENESIS_EPOCH := by
  intro genesis
  obtain ⟨delay, delayOk, big⟩ := isInInactivityLeak_ok_iff.mp leak
  obtain ⟨le, eq⟩ := getFinalityDelay_ok_iff.mp delayOk
  have lt := big.mp rfl
  have prev : getPreviousEpoch state = 0 := by unfold getPreviousEpoch; rw [genesis]; decide
  rw [prev] at eq
  have zero : delay = 0 := UInt64.toNat_inj.mp (by simpa using eq)
  subst zero
  exact absurd lt (by simp [UInt64.lt_iff_toNat_lt])

/-- One epoch of a leak from Altair: the update of the scores, then the rewards and penalties.

This holds when both steps succeed, for a registry within its limit.

The leak test is that of the state before the score update, after justification and finalization.

A validator that is not eligible keeps its balance and its score.

An eligible validator that set the target flag loses one point of score, stopping at zero.

Any other eligible validator gains the score bias.

No eligible validator earns a reward.

It pays the weight of the source flag in its base reward if it did not set that flag.

It pays the weight of the target flag in its base reward if it did not set that flag.

In that case it also pays its effective balance times its new score.

That product is divided by the score bias times the penalty quotient of the fork.

Each quotient rounds down, and the balance stops at zero.

The flags are those of the previous epoch, set by an unslashed active validator. -/
theorem processRewardsAndPenalties_of_leak {config : Config} (altair : .altair ≤ fork)
    (within : state.RegistryWithinLimit) (leak : isInInactivityLeak state = .ok true)
    (updated : processInactivityUpdates config state altair = .ok scored)
    (computed : processRewardsAndPenalties config scored = .ok after) :
    ∃ total source target, getTotalActiveBalance state = .ok total ∧
      getUnslashedParticipatingIndices state altair TIMELY_SOURCE_FLAG_INDEX
        (getPreviousEpoch state) = .ok source ∧
      getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
        (getPreviousEpoch state) = .ok target ∧
      ∀ j (inside : j < state.validators.data.size), ∃ eligible,
        isEligibleValidator (getPreviousEpoch state) state.validators.data[j] = .ok eligible ∧
        (eligible = false → after.balances.data[j]? = state.balances.data[j]? ∧
          (after.inactivityScores altair).data[j]? = (state.inactivityScores altair).data[j]?) ∧
        (eligible = true → ∃ base balance balance' score score',
          getBaseReward state total j.toUInt64 = .ok base ∧
          state.balances.data[j]? = some balance ∧ after.balances.data[j]? = some balance' ∧
          (state.inactivityScores altair).data[j]? = some score ∧
          (after.inactivityScores altair).data[j]? = some score' ∧
          score'.toNat = (if j.toUInt64 ∈ target then score.toNat - 1
            else score.toNat + config.INACTIVITY_SCORE_BIAS.toNat) ∧
          balance'.toNat = balance.toNat -
            ((if j.toUInt64 ∈ source then 0
                else base.toNat * TIMELY_SOURCE_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat) +
              (if j.toUInt64 ∈ target then 0
                else base.toNat * TIMELY_TARGET_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat +
                  state.validators.data[j].effectiveBalance.toNat * score'.toNat /
                    (config.INACTIVITY_SCORE_BIAS.toNat *
                      (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat)))) := by
  have later := getCurrentEpoch_ne_genesis_of_leak leak
  have scoresOf := processInactivityUpdates_scores later updated
  unfold processInactivityUpdates at updated
  simp only [later, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at updated
  obtain ⟨_, _, scores, _, rfl⟩ := updated
  obtain ⟨flagDeltas, inactivityDeltas, flagged, penalized, balances⟩ :=
    processRewardsAndPenalties_balances_of_altair altair (by exact later) computed
  have finRange : List.finRange PARTICIPATION_FLAG_WEIGHTS.length =
      [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩] := rfl
  rw [finRange] at flagged
  simp only [List.mapM_cons, List.mapM_nil, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at flagged
  obtain ⟨⟨sourceRewards, sourcePenalties⟩, sourceOk, _, ⟨⟨targetRewards, targetPenalties⟩,
    targetOk, _, ⟨⟨headRewards, headPenalties⟩, headOk, _, rfl, rfl⟩, rfl⟩, rfl⟩ := flagged
  obtain ⟨inactivityRewards, inactivityPenalties⟩ := inactivityDeltas
  have keptScores := congrFun (congrArg (fun s => s.inactivityScores)
    (processRewardsAndPenalties_frame computed)) altair
  have present := balances_present_of_altair altair (by exact later) computed
  obtain ⟨source, _, total, sourceOk', -, totalOk, sourceFacts⟩ :=
    getFlagIndexDeltas_getD (by exact within) sourceOk
  obtain ⟨target, _, total', targetOk', -, totalOk', targetFacts⟩ :=
    getFlagIndexDeltas_getD (by exact within) targetOk
  obtain ⟨head, _, total'', -, -, totalOk'', headFacts⟩ :=
    getFlagIndexDeltas_getD (by exact within) headOk
  obtain rfl : total = total' := Except.ok.inj (totalOk.symm.trans totalOk')
  obtain rfl : total = total'' := Except.ok.inj (totalOk.symm.trans totalOk'')
  obtain ⟨matching, matchingOk, inactivityFacts⟩ :=
    getInactivityPenaltyDeltas_getD_of_altair altair (by exact within) penalized
  obtain rfl : target = matching :=
    (Except.ok.inj (matchingOk.symm.trans (by exact targetOk'))).symm
  obtain ⟨eligibleList, eligibleOk, unlisted, listed⟩ := scoresOf
  obtain ⟨-, decided⟩ := getEligibleValidatorIndices_ok eligibleOk
  refine ⟨total, source, target, totalOk, sourceOk', targetOk',
    fun j inside => ?_⟩
  obtain ⟨eligible, eligibleOk', sourceNo, sourceYes⟩ := sourceFacts j inside
  obtain ⟨eligible₂, eligibleOk₂, targetNo, targetYes⟩ := targetFacts j inside
  obtain ⟨eligible₃, eligibleOk₃, headNo, headYes⟩ := headFacts j inside
  obtain ⟨eligible₄, eligibleOk₄, inactivityReward, inactivityExempt, inactivityPaid⟩ :=
    inactivityFacts j inside
  obtain ⟨eligible₅, eligibleOk₅, named⟩ := decided j inside
  obtain rfl : eligible = eligible₂ := Except.ok.inj (eligibleOk'.symm.trans eligibleOk₂)
  obtain rfl : eligible = eligible₃ := Except.ok.inj (eligibleOk'.symm.trans eligibleOk₃)
  obtain rfl : eligible = eligible₄ := Except.ok.inj (eligibleOk'.symm.trans eligibleOk₄)
  obtain rfl : eligible = eligible₅ := Except.ok.inj (eligibleOk'.symm.trans eligibleOk₅)
  obtain ⟨balance, found⟩ := present j inside
  have after_j := (balances j).1 inside
  rw [found] at after_j
  simp only [List.cons_append, List.nil_append, List.foldl_cons, List.foldl_nil,
    Option.map_some] at after_j
  have small := toNat_toUInt64_of_lt within inside
  have scoresAfter : after.inactivityScores altair = scores := keptScores
  refine ⟨eligible, eligibleOk', fun no => ?_, fun yes => ?_⟩
  · -- A validator that is not eligible has no delta, and no index of the score update names it.
    obtain ⟨sourceReward, sourcePenalty⟩ := sourceNo no
    obtain ⟨targetReward, targetPenalty⟩ := targetNo no
    obtain ⟨headReward, headPenalty⟩ := headNo no
    have inactivityPenalty := inactivityExempt (.inl no)
    refine ⟨?_, ?_⟩
    · rw [after_j, show state.balances.data[j]? = some balance from found]
      simp [sourceReward, sourcePenalty, targetReward, targetPenalty, headReward, headPenalty,
        inactivityReward, inactivityPenalty]
      apply UInt64.toNat_inj.mp
      simp [toNat_saturatingSub]
    · rw [scoresAfter]
      exact unlisted j fun index member same =>
        Bool.false_ne_true (no ▸ named.mp ⟨index, member, same⟩)
  · -- The score update names the validator, and its new score follows the leak.
    obtain ⟨index, member, same⟩ := named.mpr yes
    obtain rfl : index = j.toUInt64 := UInt64.toNat_inj.mp (same.trans small.symm)
    obtain ⟨hitters, leaking, score, score', hitOk, leakOk, scoreBefore, scoreNext, scoreEq⟩ :=
      listed _ member
    obtain rfl : target = hitters :=
      (Except.ok.inj (hitOk.symm.trans (by exact targetOk'))).symm
    obtain rfl : leaking = true := Except.ok.inj (leakOk.symm.trans leak)
    rw [small] at scoreBefore scoreNext
    simp only [↓reduceIte, Nat.sub_zero] at scoreEq
    obtain ⟨base, baseOk, sourceIn, sourceOut⟩ := sourceYes yes
    obtain ⟨base₂, baseOk₂, targetIn, targetOut⟩ := targetYes yes
    obtain ⟨base₃, baseOk₃, headIn, headOut⟩ := headYes yes
    obtain rfl : base = base₂ := Except.ok.inj (baseOk.symm.trans baseOk₂)
    obtain rfl : base = base₃ := Except.ok.inj (baseOk.symm.trans baseOk₃)
    -- In a leak no flag earns a reward, and a missed source or target costs its weight.
    have sourceDelta : sourceRewards.getD j 0 = 0 ∧ (sourcePenalties.getD j 0).toNat =
        if j.toUInt64 ∈ source then 0
        else base.toNat * TIMELY_SOURCE_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat := by
      by_cases mem : j.toUInt64 ∈ source
      · obtain ⟨leaking, leakOk, reward, penalty⟩ := sourceIn mem
        obtain rfl : leaking = true := Except.ok.inj (leakOk.symm.trans leak)
        exact ⟨UInt64.toNat_inj.mp (by simpa using reward), by simp [mem, penalty]⟩
      · obtain ⟨reward, penalty⟩ := sourceOut mem
        exact ⟨reward, by rw [penalty, ite_eq_right mem]; rfl⟩
    have targetDelta : targetRewards.getD j 0 = 0 ∧ (targetPenalties.getD j 0).toNat =
        if j.toUInt64 ∈ target then 0
        else base.toNat * TIMELY_TARGET_WEIGHT.toNat / WEIGHT_DENOMINATOR.toNat := by
      by_cases mem : j.toUInt64 ∈ target
      · obtain ⟨leaking, leakOk, reward, penalty⟩ := targetIn (by exact mem)
        obtain rfl : leaking = true := Except.ok.inj (leakOk.symm.trans leak)
        exact ⟨UInt64.toNat_inj.mp (by simpa using reward), by simp [mem, penalty]⟩
      · obtain ⟨reward, penalty⟩ := targetOut (by exact mem)
        exact ⟨reward, by rw [penalty, ite_eq_right mem]; rfl⟩
    have headDelta : headRewards.getD j 0 = 0 ∧ (headPenalties.getD j 0).toNat = 0 := by
      by_cases mem : j.toUInt64 ∈ head
      · obtain ⟨leaking, leakOk, reward, penalty⟩ := headIn mem
        obtain rfl : leaking = true := Except.ok.inj (leakOk.symm.trans leak)
        exact ⟨UInt64.toNat_inj.mp (by simpa using reward), by simp [penalty]⟩
      · obtain ⟨reward, penalty⟩ := headOut mem
        exact ⟨reward, by rw [penalty]; rfl⟩
    -- A missed target also costs the inactivity penalty of the new score.
    have inactivityDelta : (inactivityPenalties.getD j 0).toNat =
        if j.toUInt64 ∈ target then 0
        else state.validators.data[j].effectiveBalance.toNat * score'.toNat /
          (config.INACTIVITY_SCORE_BIAS.toNat *
            (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) := by
      by_cases mem : j.toUInt64 ∈ target
      · rw [inactivityExempt (.inr mem), ite_eq_left mem]
        rfl
      · obtain ⟨score'', found'', penalty⟩ := inactivityPaid yes mem
        obtain rfl : score' = score'' := Option.some.inj (scoreNext.symm.trans found'')
        rw [penalty, ite_eq_right mem]
    refine ⟨base, balance, _, score, score', by exact baseOk, by exact found, after_j,
      scoreBefore, by rw [scoresAfter]; exact scoreNext, scoreEq, ?_⟩
    rw [sourceDelta.1, targetDelta.1, headDelta.1, inactivityReward]
    simp only [UInt64.add_zero, toNat_saturatingSub]
    rw [sourceDelta.2, targetDelta.2, headDelta.2, inactivityDelta]
    split <;> split <;> omega

/-- In a leak epoch from Altair, a validator with the source and target flags keeps its balance.

This holds when both steps succeed, for a registry within its limit.

The flags are those of the previous epoch, set by an unslashed active validator. -/
theorem processRewardsAndPenalties_of_leak_voter {config : Config} (altair : .altair ≤ fork)
    (within : state.RegistryWithinLimit) (leak : isInInactivityLeak state = .ok true)
    (updated : processInactivityUpdates config state altair = .ok scored)
    (computed : processRewardsAndPenalties config scored = .ok after)
    {source target : List ValidatorIndex}
    (sourced : getUnslashedParticipatingIndices state altair TIMELY_SOURCE_FLAG_INDEX
      (getPreviousEpoch state) = .ok source)
    (targeted : getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
      (getPreviousEpoch state) = .ok target)
    {j : Nat} (inside : j < state.validators.data.size) (voted : j.toUInt64 ∈ source)
    (hit : j.toUInt64 ∈ target) :
    after.balances.data[j]? = state.balances.data[j]? := by
  obtain ⟨total, source', target', _, sourceOk, targetOk, facts⟩ :=
    processRewardsAndPenalties_of_leak altair within leak updated computed
  obtain rfl : source = source' := Except.ok.inj (sourced.symm.trans sourceOk)
  obtain rfl : target = target' := Except.ok.inj (targeted.symm.trans targetOk)
  obtain ⟨eligible, _, notEligible, isEligible⟩ := facts j inside
  cases eligible with
  | false => exact (notEligible rfl).1
  | true =>
    obtain ⟨base, balance, balance', score, score', _, before, later, _, _, _, paid⟩ :=
      isEligible rfl
    simp only [voted, hit, ↓reduceIte] at paid
    rw [before, later]
    exact congrArg some (UInt64.toNat_inj.mp (by omega))

end EthLib.Consensus
