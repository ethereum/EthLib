module

public import EthLib.Consensus.Proofs.Transition.InactivityLeakBound
public import EthLib.Consensus.Proofs.Transition.FfgStake

/-!
# Proofs: the voters hold two thirds of the active stake after a leak

Justification needs the voters to hold two thirds of the active balance.

The active balance counts the effective balance of each active validator.

Split the active validators into voters and absent validators.

If each absent validator has an effective balance at most a threshold, the absent stake is small.

It is at most their number times the threshold.

So once twice that bound is at most the balance of the voters, they hold two thirds.

Under the assumptions of the trace bound, a leak brings each absent validator to such a threshold.

For the discrete rule, this bounds the epoch that [Pavloff et al.][pat], Section 5.1, estimates.

Their Equation 6 gives it in a continuous model.

Its condition on the threshold is that of Equation 5 at two thirds.

Here the share enters only through the threshold, which the balance of the voters sets.

The bound does not wait for the ejection, whose exit queue can be long.

A validator in that queue still counts, but its effective balance has fallen.

The second term of Equation 6, the ejection at epoch 4,685, assumes an immediate exit.

[pat]: https://arxiv.org/abs/2404.16363v2
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models

variable {preset : Preset} {fork : Base.Fork} {state : BeaconState preset fork}

/-- The voters hold two thirds of the active balance when the absent stake is small.

Each active validator is a voter or an absent validator.

Each absent validator has an effective balance at most a threshold.

Their number times twice the threshold is at most the balance of the voters.

Then twice the active balance is at most three times the balance of the voters.

The registry must stay within its limit, so that each position is its own index. -/
theorem twoThirds_of_effectiveBalance_le {voters : List ValidatorIndex} {absents : List Nat}
    {threshold : Nat} {total voterTotal : Gwei} (within : state.RegistryWithinLimit)
    (active : getTotalActiveBalance state = .ok total)
    (voting : getTotalBalance state voters = .ok voterTotal)
    (covered : ∀ j (inside : j < state.validators.data.size),
      isActiveValidator state.validators.data[j] (getCurrentEpoch state) = true →
        j.toUInt64 ∈ voters ∨ j ∈ absents)
    (low : ∀ j ∈ absents, ∀ inside : j < state.validators.data.size,
      state.validators.data[j].effectiveBalance.toNat ≤ threshold)
    (strong : 2 * absents.length * threshold ≤ voterTotal.toNat) :
    2 * total.toNat ≤ 3 * voterTotal.toNat := by
  classical
  unfold getTotalActiveBalance at active
  obtain ⟨-, -, activeEq⟩ := getTotalBalance_ok_iff_stake.mp active
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
  have bound : stake weight (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset ≤
      stake weight voters.toFinset + absents.length * threshold :=
    (stake_mono subset).trans ((stake_union_le _ _).trans (Nat.add_le_add_left absentLe _))
  rw [Nat.mul_assoc] at strong
  rw [activeEq]
  rw [voterEq] at strong ⊢
  simp only [Nat.max_def] at strong ⊢
  split_ifs at strong ⊢ <;> omega

/-- After an explicit number of leak epochs, the voters hold two thirds of the active balance.

Each active validator of the final state is a voter or an absent validator.

Each absent validator follows a trace of the leak, as in the bound on its effective balance.

The traces are assumptions, not derived from the state transition.

While its effective balance is above the threshold, each epoch is a leak epoch for it.

Its balance never rises.

The first and the largest effective balances are whole numbers of increments.

Its effective balance in the final state is the last one of its trace.

Its balance starts at most at a bound, the same for all.

Twice the number of absent validators times a threshold is at most the balance of the voters.

The voters are meant to be the unslashed attesters of the target, but any list works.

The voters need not be active, so their balance may count inactive validators.

Each total balance is at least one increment, as in the justification test.

The threshold is a whole number of increments, and with an increment it exceeds the downward band.

On mainnet from Bellatrix, a threshold of 16 ETH takes at most 5,488 epochs from 32 ETH.

The number of epochs depends on the start bound, threshold, bias, divisor and preset.

The bias and the divisor must be positive.

After that many epochs or more, twice the active balance is at most three times that of the voters.

The increment must be positive and at most the upward band, as on mainnet.

The registry must stay within its limit. -/
theorem twoThirds_of_leak {voters : List ValidatorIndex} {absents : List Nat}
    {total voterTotal : Gwei} {balance settled effective : Nat → Nat → Gwei}
    {score : Nat → Nat → Nat} {largest : Nat → Gwei}
    {bias divisor start threshold epochs : Nat}
    (biasPos : 0 < bias) (divisorPos : 0 < divisor)
    (bands : preset.IncrementWithinUpwardBand)
    (within : state.RegistryWithinLimit) (active : getTotalActiveBalance state = .ok total)
    (voting : getTotalBalance state voters = .ok voterTotal)
    (covered : ∀ j (inside : j < state.validators.data.size),
      isActiveValidator state.validators.data[j] (getCurrentEpoch state) = true →
        j.toUInt64 ∈ voters ∨ j ∈ absents)
    (final : ∀ j ∈ absents, ∀ inside : j < state.validators.data.size,
      state.validators.data[j].effectiveBalance = effective j epochs)
    (startAligned : ∀ j ∈ absents, effective j 0 % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (largestAligned : ∀ j ∈ absents, largest j % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (thresholdAligned : threshold % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (startAbove : ∀ j ∈ absents,
      (balance j 0).toNat ≤ (effective j 0).toNat + preset.upwardBand ∨ largest j ≤ effective j 0)
    (stays : ∀ j ∈ absents, ∀ t < epochs, (settled j t).toNat ≤ (balance j t).toNat)
    (scored : ∀ j ∈ absents, ∀ t < epochs, threshold < (effective j t).toNat →
      score j (t + 1) = score j t + bias)
    (penalized : ∀ j ∈ absents, ∀ t < epochs, threshold < (effective j t).toNat →
      (settled j t).toNat ≤
        (balance j t).toNat - (effective j t).toNat * (score j t + bias) / divisor)
    (updated : ∀ j ∈ absents, ∀ t < epochs, updatedEffectiveBalance preset (largest j)
      (settled j t) (effective j t) = .ok (effective j (t + 1)))
    (between : ∀ j ∈ absents, ∀ t < epochs, (balance j (t + 1)).toNat ≤ (settled j t).toNat)
    (bounded : ∀ j ∈ absents, (balance j 0).toNat ≤ start)
    (strong : 2 * absents.length * threshold ≤ voterTotal.toNat)
    (wide : preset.downwardBand < threshold + preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (long : leakEpochs (threshold + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) bias divisor
      (start + preset.downwardBand + 1 - (threshold + preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
        epochs) :
    2 * total.toNat ≤ 3 * voterTotal.toNat := by
  refine twoThirds_of_effectiveBalance_le (threshold := threshold) within active voting covered
    (fun j absent inside => ?_) strong
  rw [final j absent inside]
  have := bounded j absent
  exact effectiveBalance_le_of_leakEpochs biasPos divisorPos wide bands (startAligned j absent)
    (largestAligned j absent) thresholdAligned (startAbove j absent) (stays j absent)
    (scored j absent) (penalized j absent) (updated j absent) (between j absent)
    (Nat.le_trans (leakEpochs_mono (by omega)) long)

end EthLib.Consensus
