module

public import EthLib.Consensus.Proofs.Transition.InactivityLeakBound
public import EthLib.Consensus.Proofs.Transition.FfgStake

/-!
# Proofs: the voters hold two thirds of the active stake after a leak

Justification needs the voters to hold two thirds of the active balance.

The trace bound caps the effective balance of an absent validator after the epochs of a leak.

Under the assumptions of that bound, a leak brings that about.

For the discrete rule, this bounds the epoch that [Pavloff et al.][pat], Section 5.1, estimates.

Their Equation 6 gives it in a continuous model.

The condition of that model on the threshold is Equation 5 at two thirds.

Here the share enters only through the threshold, which the balance of the voters sets.

[pat]: https://arxiv.org/abs/2404.16363v2
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models

variable {preset : Preset} {fork : Base.Fork} {state : BeaconState preset fork}

/-- The voters hold two thirds of the active balance when the absent stake is small.

That happens once a leak brings the effective balance of each absent validator low enough.

Twice the active balance is then at most three times the balance of the voters. -/
theorem twoThirds_of_effectiveBalance_le {voters : List ValidatorIndex} {absents : List Nat}
    -- The registry must stay within its limit, so that each position is its own index.
    {threshold : Nat} {total voterTotal : Gwei} (within : state.RegistryWithinLimit)
    -- The active balance counts the effective balance of each active validator.
    (active : getTotalActiveBalance state = .ok total)
    (voting : getTotalBalance state voters = .ok voterTotal)
    -- Each active validator is a voter or an absent validator.
    (covered : ∀ j (inside : j < state.validators.data.size),
      isActiveValidator state.validators.data[j] (getCurrentEpoch state) = true →
        j.toUInt64 ∈ voters ∨ j ∈ absents)
    -- Each absent validator has an effective balance at most a threshold.
    (low : ∀ j ∈ absents, ∀ inside : j < state.validators.data.size,
      state.validators.data[j].effectiveBalance.toNat ≤ threshold)
    -- Their number times twice the threshold is at most the balance of the voters.
    (strong : 2 * absents.length * threshold ≤ voterTotal.toNat) :
    2 * total.toNat ≤ 3 * voterTotal.toNat := by
  classical
  obtain ⟨-, -, activeEq⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok active)
  obtain ⟨-, -, voterEq⟩ := getTotalBalance_ok_iff_stake.mp voting
  set weight : ValidatorIndex → ℕ := fun index => balanceAt state index.toNat with hweight
  set absentSet : Finset ValidatorIndex :=
    ((absents.filter (· < state.validators.data.size)).toFinset).image Nat.toUInt64 with habsent
  have subset : (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset ⊆
      voters.toFinset ∪ absentSet := by
    intro index listed
    obtain ⟨validator, found, isActive⟩ :=
      (mem_getActiveValidatorIndices within).mp (List.mem_toFinset.mp listed)
    have lt : index.toNat < state.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
    have same : index.toNat.toUInt64 = index := by simp
    rw [Array.getElem?_eq_getElem lt, Option.some.injEq] at found
    subst found
    rcases covered index.toNat lt isActive with voter | absent
    · rw [same] at voter
      exact Finset.mem_union_left _ (List.mem_toFinset.mpr voter)
    · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨index.toNat, ?_, same⟩)
      exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨absent, by simpa using lt⟩)
  -- The absent stake is at most the number of absent validators times the threshold.
  have absentLe : stake weight absentSet ≤ absents.length * threshold := by
    refine (Finset.sum_le_card_nsmul absentSet weight threshold fun index member => ?_).trans ?_
    · obtain ⟨j, listed, rfl⟩ := Finset.mem_image.mp member
      obtain ⟨absent, lt⟩ := List.mem_filter.mp (List.mem_toFinset.mp listed)
      have lt : j < state.validators.data.size := by simpa using lt
      simp only [hweight, toNat_toUInt64_of_lt within lt, balanceAt,
        Array.getElem?_eq_getElem lt, Option.map_some, Option.getD_some]
      exact low j absent lt
    · refine Nat.mul_le_mul_right _ ((Finset.card_image_le).trans ?_)
      exact (List.toFinset_card_le _).trans (List.length_filter_le _ _)
  -- The active stake is at most the stake of the voters plus the absent stake.
  have bound : stake weight (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset ≤
      stake weight voters.toFinset + absents.length * threshold :=
    (stake_mono subset).trans ((stake_union_le _ _).trans (Nat.add_le_add_left absentLe _))
  -- So once twice that bound is at most the balance of the voters, they hold two thirds.
  rw [Nat.mul_assoc] at strong
  rw [activeEq]
  rw [voterEq] at strong ⊢
  simp only [Nat.max_def] at strong ⊢
  split_ifs at strong ⊢ <;> omega

/-- After an explicit number of leak epochs, the voters hold two thirds of the active balance.

Each absent validator follows a trace of the leak, as in the bound on its effective balance.

The traces are assumptions, not derived from the state transition. -/
theorem twoThirds_of_leak {voters : List ValidatorIndex} {absents : List Nat}
    {total voterTotal : Gwei} {balance settled effective : Nat → Nat → Gwei}
    {score : Nat → Nat → Nat} {largest : Nat → Gwei}
    {bias divisor start threshold epochs : Nat}
    -- The bias and the divisor must be positive.
    (biasPos : 0 < bias) (divisorPos : 0 < divisor)
    -- The increment must be positive and at most the upward band, as on mainnet.
    (bands : preset.IncrementWithinUpwardBand)
    -- The registry must stay within its limit.
    --
    -- Each total balance is at least one increment, as in the justification test.
    (within : state.RegistryWithinLimit) (active : getTotalActiveBalance state = .ok total)
    -- The voters are meant to be the unslashed attesters of the target, but any list works.
    --
    -- The voters need not be active, so their balance may count inactive validators.
    (voting : getTotalBalance state voters = .ok voterTotal)
    -- Each active validator of the final state is a voter or an absent validator.
    (covered : ∀ j (inside : j < state.validators.data.size),
      isActiveValidator state.validators.data[j] (getCurrentEpoch state) = true →
        j.toUInt64 ∈ voters ∨ j ∈ absents)
    -- The effective balance of an absent validator in the final state is the last one of its trace.
    (final : ∀ j ∈ absents, ∀ inside : j < state.validators.data.size,
      state.validators.data[j].effectiveBalance = effective j epochs)
    -- The first effective balance of each trace is a whole number of increments.
    (startAligned : ∀ j ∈ absents, effective j 0 % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    -- The largest effective balance of each absent validator is a whole number of increments.
    (largestAligned : ∀ j ∈ absents, largest j % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    -- The threshold is a whole number of increments.
    (thresholdAligned : threshold % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (startAbove : ∀ j ∈ absents,
      (balance j 0).toNat ≤ (effective j 0).toNat + preset.upwardBand ∨ largest j ≤ effective j 0)
    -- The balance of each absent validator never rises.
    --
    -- Within an epoch, the settled balance is at most the balance.
    (stays : ∀ j ∈ absents, ∀ t < epochs, (settled j t).toNat ≤ (balance j t).toNat)
    -- While an absent effective balance is above the threshold, each epoch is a leak epoch for it.
    (scored : ∀ j ∈ absents, ∀ t < epochs, threshold < (effective j t).toNat →
      score j (t + 1) = score j t + bias)
    -- In such an epoch, it loses at least the inactivity penalty.
    (penalized : ∀ j ∈ absents, ∀ t < epochs, threshold < (effective j t).toNat →
      (settled j t).toNat ≤
        (balance j t).toNat - (effective j t).toNat * (score j t + bias) / divisor)
    (updated : ∀ j ∈ absents, ∀ t < epochs, updatedEffectiveBalance preset (largest j)
      (settled j t) (effective j t) = .ok (effective j (t + 1)))
    -- Nor does its balance rise from the settled balance to the next epoch.
    (between : ∀ j ∈ absents, ∀ t < epochs, (balance j (t + 1)).toNat ≤ (settled j t).toNat)
    -- Its balance starts at most at a bound, the same for all.
    (bounded : ∀ j ∈ absents, (balance j 0).toNat ≤ start)
    -- Take twice the number of absent validators times the threshold.
    --
    -- That product is at most the balance of the voters.
    (strong : 2 * absents.length * threshold ≤ voterTotal.toNat)
    -- With an increment, the threshold exceeds the downward band.
    (wide : preset.downwardBand < threshold + preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    -- The leak lasts at least a bound on its epochs.
    --
    -- The bound depends on the start bound, threshold, bias, divisor and preset.
    --
    -- On mainnet from Bellatrix, a threshold of 16 ETH takes at most 5,488 epochs from 32 ETH.
    --
    -- The bound does not wait for the ejection, whose exit queue can be long.
    --
    -- A validator in that queue still counts, but its effective balance has fallen.
    --
    -- The second term of Equation 6, the ejection at epoch 4,685, assumes an immediate exit.
    (long : leakEpochs (threshold + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) bias divisor
      (start + preset.downwardBand + 1 - (threshold + preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
        epochs) :
    -- After that many epochs or more, take twice the active balance.
    --
    -- It is at most three times the balance of the voters.
    2 * total.toNat ≤ 3 * voterTotal.toNat := by
  refine twoThirds_of_effectiveBalance_le (threshold := threshold) within active voting covered
    (fun j absent inside => ?_) strong
  rw [final j absent inside]
  have := bounded j absent
  -- Under the assumptions of the trace bound, the leak brings it to the threshold.
  exact effectiveBalance_le_of_leakEpochs biasPos divisorPos wide bands (startAligned j absent)
    (largestAligned j absent) thresholdAligned (startAbove j absent) (stays j absent)
    (scored j absent) (penalized j absent) (updated j absent) (between j absent)
    (Nat.le_trans (leakEpochs_mono (by omega)) long)

end EthLib.Consensus
