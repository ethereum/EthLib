module

public import EthLib.Consensus.Proofs.Transition.Totality.Rewards

/-!
# Proofs: the horizon of a run of slots

A run of slots without blocks stops finalizing, and after a few epochs the chain leaks.

From Altair, in each epoch each inactivity score grows by at most the score bias.

The inactivity penalty multiplies an effective balance by a score, and that product must fit.

So a bound on the scores holds only for a number of epochs, the horizon.

It counts the epochs before the largest cap on an effective balance times a score reaches `2^64`.

From scores of zero on mainnet, it is at least `2.25 * 10^6` epochs, about 27 years.
-/

@[expose] public section

namespace EthLib.Consensus

/-- The horizon in epochs of a run of slots whose scores start at or below a bound.

It is the room between that bound and the largest score that fits with the largest cap.

That room is divided by the score bias, which must be positive; at zero the horizon is zero.

The bound at the start must fit with the largest cap, else the horizon is zero too. -/
def Preset.horizon (preset : Preset) (config : Config) (scoreStart : Nat) : Nat :=
  ((2 ^ 64 - 1) / preset.largestEffectiveBalance - scoreStart) /
    config.INACTIVITY_SCORE_BIAS.toNat

/-- Within the horizon, the scores still fit with the largest cap.

The scores are the bound at the start plus the bias for each epoch.

The bound at the start must fit with the largest cap. -/
theorem Preset.largestEffectiveBalance_mul_lt_of_le_horizon {preset : Preset} {config : Config}
    {scoreStart epochs : Nat} (start : preset.largestEffectiveBalance * scoreStart < 2 ^ 64)
    (within : epochs ≤ preset.horizon config scoreStart) :
    preset.largestEffectiveBalance *
      (scoreStart + config.INACTIVITY_SCORE_BIAS.toNat * epochs) < 2 ^ 64 := by
  unfold Preset.horizon at within
  rcases Nat.eq_zero_or_pos preset.largestEffectiveBalance with zero | positive
  · rw [zero, Nat.zero_mul]
    exact Nat.two_pow_pos 64
  -- The start is at most the largest score that fits.
  have startLe : scoreStart ≤ (2 ^ 64 - 1) / preset.largestEffectiveBalance :=
    (Nat.le_div_iff_mul_le positive).mpr (by rw [Nat.mul_comm]; omega)
  have grown : config.INACTIVITY_SCORE_BIAS.toNat * epochs ≤
      (2 ^ 64 - 1) / preset.largestEffectiveBalance - scoreStart := by
    rcases Nat.eq_zero_or_pos config.INACTIVITY_SCORE_BIAS.toNat with none | some
    · rw [none, Nat.zero_mul]
      exact Nat.zero_le _
    · rw [Nat.mul_comm]
      exact (Nat.le_div_iff_mul_le some).mp within
  have total : scoreStart + config.INACTIVITY_SCORE_BIAS.toNat * epochs ≤
      (2 ^ 64 - 1) / preset.largestEffectiveBalance := by omega
  calc preset.largestEffectiveBalance *
        (scoreStart + config.INACTIVITY_SCORE_BIAS.toNat * epochs)
      ≤ preset.largestEffectiveBalance * ((2 ^ 64 - 1) / preset.largestEffectiveBalance) :=
        Nat.mul_le_mul_left _ total
    _ ≤ 2 ^ 64 - 1 := Nat.mul_div_le _ _
    _ < 2 ^ 64 := by decide

/-- Past the horizon, the scores no longer fit with the largest cap.

So the horizon is the longest run that the bound on the scores allows.

The score bias and the largest cap must be positive. -/
theorem Preset.le_largestEffectiveBalance_mul_of_horizon_lt {preset : Preset} {config : Config}
    {scoreStart epochs : Nat} (bias : config.INACTIVITY_SCORE_BIAS ≠ 0)
    (cap : preset.largestEffectiveBalance ≠ 0)
    (past : preset.horizon config scoreStart < epochs) :
    2 ^ 64 ≤ preset.largestEffectiveBalance *
      (scoreStart + config.INACTIVITY_SCORE_BIAS.toNat * epochs) := by
  unfold Preset.horizon at past
  have biasPositive : 0 < config.INACTIVITY_SCORE_BIAS.toNat := by
    have := UInt64.toNat_inj.not.mpr bias
    simp only [UInt64.toNat_zero] at this
    omega
  have capPositive : 0 < preset.largestEffectiveBalance := Nat.pos_of_ne_zero cap
  -- The bias for each epoch passes the room above the start.
  have grown : (2 ^ 64 - 1) / preset.largestEffectiveBalance - scoreStart <
      config.INACTIVITY_SCORE_BIAS.toNat * epochs := by
    rw [Nat.mul_comm]
    exact (Nat.div_lt_iff_lt_mul biasPositive).mp past
  have above : (2 ^ 64 - 1) / preset.largestEffectiveBalance <
      scoreStart + config.INACTIVITY_SCORE_BIAS.toNat * epochs := by omega
  have := (Nat.div_lt_iff_lt_mul capPositive).mp above
  rw [Nat.mul_comm] at this
  omega

/-- Within the horizon, the rewards fit at the bound on the scores of the next epoch.

Before an epoch the scores are at most the start bound plus the bias for each epoch so far.

After it they gain at most one more bias, so the epoch needs the fit at that larger bound. -/
theorem RewardsFit.of_lt_horizon {preset : Preset} {config : Config}
    {budget scoreBound scoreStart epochs : Nat} (fit : RewardsFit preset config budget scoreBound)
    (start : preset.largestEffectiveBalance * scoreStart < 2 ^ 64)
    (within : epochs < preset.horizon config scoreStart) :
    RewardsFit preset config budget
      (scoreStart + config.INACTIVITY_SCORE_BIAS.toNat * epochs +
        config.INACTIVITY_SCORE_BIAS.toNat) := by
  have fits := Preset.largestEffectiveBalance_mul_lt_of_le_horizon start (Nat.succ_le_of_lt within)
  rw [Nat.mul_succ, ← Nat.add_assoc] at fits
  exact { fit with scorePenalty := fits }

/-- The rewards still fit under another score bound, if it fits with the largest cap. -/
theorem RewardsFit.of_scoreBound {preset : Preset} {config : Config}
    {budget scoreBound other : Nat} (fit : RewardsFit preset config budget scoreBound)
    (fits : preset.largestEffectiveBalance * other < 2 ^ 64) :
    RewardsFit preset config budget other :=
  { fit with scorePenalty := fits }

/-- On mainnet, from scores of zero, the horizon is at least `2.25 * 10^6` epochs.

An epoch of mainnet lasts 6.4 minutes, so that is about 27 years. -/
theorem Preset.horizon_mainnet : 2250000 ≤ Preset.mainnet.horizon Config.mainnet 0 := by
  decide

/-- On minimal, from scores of zero, the horizon is at least `2.25 * 10^6` epochs too. -/
theorem Preset.horizon_minimal : 2250000 ≤ Preset.minimal.horizon Config.minimal 0 := by
  decide

end EthLib.Consensus
