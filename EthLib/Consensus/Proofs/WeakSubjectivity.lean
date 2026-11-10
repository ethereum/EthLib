module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.WeakSubjectivity

/-!
# Proofs: weak subjectivity

From Electra, the period has a closed form on natural numbers.

For a total active balance `t` and a churn `c`, it is the withdrawal delay plus `10 t / (200 c)`.

The 64-bit computation gives that value exactly when nothing reaches `2^64` and `c` is not zero.

Its epochs of churn, the period less the delay, times `c` are at most `SAFETY_DECAY / 200` of `t`.

So a change of at most `3 c` for each of them, in total, keeps a margin of `1/3 - SAFETY_DECAY/100`.

In Phase 0, a computed period is one of the two expressions of the rule, on natural numbers.

In Phase 0, the period is at most the delay plus the larger of two terms.

Both terms grow with the number of validators.

At every fork, the period is at least the withdrawal delay.

In Electra and Fulu, the period is at most a bound of the parameters alone: 3558 epochs on mainnet.

From Gloas, the period is at most a bound of the parameters alone: 1658 epochs on mainnet.

The check of a checkpoint needs a state that holds its root and is at its epoch.

It then answers whether the current epoch is at most the end of the period.

So a checkpoint within its period at some slot is within it at every earlier slot.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork}

/-- Two errors with one code come from one constructor. -/
theorem WeakSubjectivityError.code_injective (e₁ e₂ : WeakSubjectivityError)
    (h : e₁.code = e₂.code) : e₁.ctorIdx = e₂.ctorIdx := by
  -- Each code is one more than the index of its constructor.
  have back : ∀ e : WeakSubjectivityError, e.code.toNat - 1 = e.ctorIdx := by
    intro e
    cases e <;> rfl
  rw [← back e₁, ← back e₂, h]

/-! ## The closed forms -/

/-- From Electra: the period of a balance and a churn succeeds exactly when nothing overflows.

The churn must also be nonzero, and the period is then the delay plus `10 t / (200 c)`. -/
theorem balanceChurnPeriod_eq_ok_iff {minDelay total churn period : UInt64} :
    balanceChurnPeriod minDelay total churn = .ok period ↔
      10 * total.toNat < 2 ^ 64 ∧ 200 * churn.toNat < 2 ^ 64 ∧ 0 < churn.toNat ∧
        minDelay.toNat + 10 * total.toNat / (200 * churn.toNat) < 2 ^ 64 ∧
        period.toNat = minDelay.toNat + 10 * total.toNat / (200 * churn.toNat) := by
  have hD : SAFETY_DECAY.toNat = 10 := rfl
  unfold balanceChurnPeriod
  simp only [bind_ok_iff, mulChecked_ok_iff, divChecked_ok_iff, addChecked_ok_iff, hD,
    UInt64.toNat_ofNat, ne_eq, ← UInt64.toNat_inj]
  constructor
  · rintro ⟨a, ⟨h₁, ha⟩, b, ⟨h₂, hb⟩, c, ⟨h₃, hc⟩, d, ⟨h₄, hd⟩, h₅, h₆⟩
    rw [hb] at hc h₃
    rw [ha, hc] at hd
    rw [hc] at h₄
    rw [hd] at h₅ h₆
    -- The divisor is `2 * churn * 100`, which is `200 * churn`.
    have hdivisor : 2 * churn.toNat * 100 = 200 * churn.toNat := by omega
    rw [hdivisor] at h₅ h₆
    exact ⟨h₁, by omega, by omega, h₅, h₆⟩
  · rintro ⟨h₁, h₂, h₃, h₄, h₅⟩
    obtain ⟨a, ha⟩ := exists_toNat_eq h₁
    obtain ⟨b, hb⟩ := exists_toNat_eq (n := 2 * churn.toNat) (by omega)
    obtain ⟨c, hc⟩ := exists_toNat_eq h₂
    obtain ⟨d, hd⟩ := exists_toNat_eq (n := 10 * total.toNat / (200 * churn.toNat)) (by omega)
    refine ⟨a, ⟨h₁, ha⟩, b, ⟨by omega, hb⟩, c, ⟨by omega, by omega⟩, d, ⟨by omega, ?_⟩, ?_, ?_⟩
    · rw [hd, ha, hc]
    · rwa [hd]
    · rwa [hd]

/-- From Electra: the period of a balance and a churn is at least the delay. -/
theorem le_of_balanceChurnPeriod_eq_ok {minDelay total churn period : UInt64}
    (h : balanceChurnPeriod minDelay total churn = .ok period) : minDelay ≤ period := by
  obtain ⟨-, -, -, -, hperiod⟩ := balanceChurnPeriod_eq_ok_iff.mp h
  exact UInt64.le_iff_toNat_le.mpr (hperiod ▸ Nat.le_add_right _ _)

/-- From Electra: the epochs of churn of a period, the period less the delay, are few enough.

That many epochs, at `churn` each, total at most `SAFETY_DECAY / 200` of the total balance. -/
theorem churn_le_of_balanceChurnPeriod_eq_ok {minDelay total churn period : UInt64}
    (h : balanceChurnPeriod minDelay total churn = .ok period) :
    200 * ((period.toNat - minDelay.toNat) * churn.toNat) ≤ SAFETY_DECAY.toNat * total.toNat := by
  obtain ⟨-, -, -, -, hperiod⟩ := balanceChurnPeriod_eq_ok_iff.mp h
  have hD : SAFETY_DECAY.toNat = 10 := rfl
  rw [hperiod, Nat.add_sub_cancel_left, hD, ← Nat.mul_assoc, Nat.mul_comm 200, Nat.mul_assoc]
  exact Nat.div_mul_le_self _ _

/-- From Electra: the period keeps a safety margin of `1/3 - SAFETY_DECAY/100` of the balance.

Take a stake `x` and the epochs `n` of churn of the period, the period less the delay.

Assume the total balance is at most `3 x + 2 n k`, with `k` three times the churn.

Accountable safety gives that bound when each set changes by at most `n k` since the checkpoint.

Then `x` is at least `1/3 - SAFETY_DECAY/100` of the total balance.

With `SAFETY_DECAY` at 10 that is `7/30`, about 23.3%. -/
theorem safetyMargin_of_balanceChurnPeriod_eq_ok {minDelay total churn period : UInt64} {x : Nat}
    (h : balanceChurnPeriod minDelay total churn = .ok period)
    (bound : total.toNat ≤
      3 * x + 2 * ((period.toNat - minDelay.toNat) * (3 * churn.toNat))) :
    (100 - 3 * SAFETY_DECAY.toNat) * total.toNat ≤ 300 * x := by
  have hchurn := churn_le_of_balanceChurnPeriod_eq_ok h
  have hD : SAFETY_DECAY.toNat = 10 := rfl
  rw [hD] at hchurn ⊢
  rw [Nat.mul_left_comm (period.toNat - minDelay.toNat)] at bound
  omega

/-- Electra and Fulu: the period is the closed form, for the total active balance and its churn.

It succeeds exactly when both have values and the closed form does. -/
theorem computeWeakSubjectivityPeriodElectra_eq_ok_iff {config : Config}
    {state : BeaconState preset fork} {period : Epoch} :
    computeWeakSubjectivityPeriodElectra config state = .ok period ↔
      ∃ total churn, getTotalActiveBalance state = .ok total ∧
        getBalanceChurnLimit config state = .ok churn ∧
        balanceChurnPeriod config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY total churn = .ok period := by
  unfold computeWeakSubjectivityPeriodElectra
  simp only [bind_ok_iff, mapError_ok_iff]
  exact ⟨fun ⟨a, ha, b, hb, hc⟩ => ⟨a, b, ha, hb, hc⟩, fun ⟨a, b, ha, hb, hc⟩ => ⟨a, ha, b, hb, hc⟩⟩

/-- From Gloas: the weighted churn succeeds when its three churns do and nothing overflows.

It equals two thirds of the exit churn, one third of the activation churn, plus consolidations. -/
theorem gloasWeightedChurn_eq_ok_iff {config : Config} {state : BeaconState preset fork}
    {churn : Gwei} :
    gloasWeightedChurn config state = .ok churn ↔
      ∃ exit activation consolidation,
        getExitChurnLimit config state = .ok exit ∧
        getActivationChurnLimit config state = .ok activation ∧
        getConsolidationChurnLimit config state = .ok consolidation ∧
        2 * exit.toNat < 2 ^ 64 ∧
        (2 * exit.toNat) / 3 + activation.toNat / 3 + consolidation.toNat < 2 ^ 64 ∧
        churn.toNat = (2 * exit.toNat) / 3 + activation.toNat / 3 + consolidation.toNat := by
  unfold gloasWeightedChurn
  have h2 : (2 : UInt64).toNat = 2 := rfl
  have h3 : (3 : UInt64).toNat = 3 := rfl
  simp only [bind_ok_iff, mapError_ok_iff, mulChecked_ok_iff, addChecked_ok_iff, UInt64.toNat_div,
    h2, h3]
  constructor
  · rintro ⟨exit, hex, act, hac, cons, hco, twoExit, ⟨h₂, hte⟩, sum, ⟨hsum, hs⟩, hfin, hch⟩
    rw [hte] at hs hsum
    rw [hs] at hfin hch
    exact ⟨exit, act, cons, hex, hac, hco, h₂, hfin, hch⟩
  · rintro ⟨exit, act, cons, hex, hac, hco, h₂, hfin, hch⟩
    obtain ⟨twoExit, hte⟩ := exists_toNat_eq h₂
    obtain ⟨sum, hs⟩ := exists_toNat_eq (n := (2 * exit.toNat) / 3 + act.toNat / 3) (by omega)
    refine ⟨exit, hex, act, hac, cons, hco, twoExit, ⟨h₂, hte⟩, sum, ⟨by omega, ?_⟩,
      by omega, ?_⟩
    · rw [hs, hte]
    · rw [hch, hs]

/-- From Gloas: the period is the closed form, for the total active balance and the weighted churn.

It succeeds exactly when both have values and the closed form does. -/
theorem computeWeakSubjectivityPeriodGloas_eq_ok_iff {config : Config}
    {state : BeaconState preset fork} {period : Epoch} :
    computeWeakSubjectivityPeriodGloas config state = .ok period ↔
      ∃ total churn, getTotalActiveBalance state = .ok total ∧
        gloasWeightedChurn config state = .ok churn ∧
        balanceChurnPeriod config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY total churn = .ok period := by
  unfold computeWeakSubjectivityPeriodGloas
  simp only [bind_ok_iff, mapError_ok_iff]
  exact ⟨fun ⟨a, ha, b, hb, hc⟩ => ⟨a, b, ha, hb, hc⟩, fun ⟨a, b, ha, hb, hc⟩ => ⟨a, ha, b, hb, hc⟩⟩

/-- From Electra: the period is the balance churn period of the total active balance.

Its churn is the weighted churn from Gloas, and the balance churn in Electra and Fulu. -/
theorem balanceChurnPeriod_of_computeWeakSubjectivityPeriod_eq_ok {config : Config}
    {state : BeaconState preset fork} (electra : .pectra ≤ fork) {period churn : UInt64}
    (periodOk : computeWeakSubjectivityPeriod config state = .ok period)
    (churnOk : if .glamsterdam ≤ fork then gloasWeightedChurn config state = .ok churn
      else getBalanceChurnLimit config state = .ok churn) :
    ∃ total, getTotalActiveBalance state = .ok total ∧
      balanceChurnPeriod config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY total churn = .ok period := by
  unfold computeWeakSubjectivityPeriod at periodOk
  -- The split also discharges the Phase 0 branch with `electra`.
  split at periodOk <;> rename_i gloas <;> simp only [gloas, ↓reduceIte] at churnOk
  · obtain ⟨total, churn', totalOk, churnOk', periodOk⟩ :=
      computeWeakSubjectivityPeriodGloas_eq_ok_iff.mp periodOk
    rw [churnOk, Except.ok.injEq] at churnOk'
    exact ⟨total, totalOk, churnOk' ▸ periodOk⟩
  · obtain ⟨total, churn', totalOk, churnOk', periodOk⟩ :=
      computeWeakSubjectivityPeriodElectra_eq_ok_iff.mp periodOk
    rw [churnOk, Except.ok.injEq] at churnOk'
    exact ⟨total, totalOk, churnOk' ▸ periodOk⟩

/-- Phase 0: computed epochs are one of the two expressions of the rule, on natural numbers.

With large average balances, they are the longer of the churn bound and the top-up bound.

With small ones, they are the top-up bound for small balances. -/
theorem phase0PeriodEpochs_eq_ok {N t T delta Delta epochs : UInt64}
    (h : phase0PeriodEpochs N t T delta Delta = .ok epochs) :
    if 230 * T.toNat < 320 * t.toNat then
      epochs.toNat = max (N.toNat * (320 * t.toNat - 230 * T.toNat) /
          (600 * delta.toNat * (2 * t.toNat + T.toNat)))
        (230 * N.toNat / (600 * Delta.toNat))
    else epochs.toNat = 30 * N.toNat * t.toNat / (200 * Delta.toNat * (T.toNat - t.toNat)) := by
  have hD : SAFETY_DECAY = 10 := rfl
  unfold phase0PeriodEpochs at h
  simp only [hD, bind_ok_iff, mulChecked_ok_iff] at h
  have h230 : (200 + 3 * 10 : UInt64).toNat = 230 := rfl
  have h320 : (200 + 12 * 10 : UInt64).toNat = 320 := rfl
  obtain ⟨low, ⟨-, hlow⟩, high, ⟨-, hhigh⟩, h⟩ := h
  rw [h230] at hlow
  rw [h320] at hhigh
  split at h
  · -- The churn branch: the longer of the two bounds.
    rename_i hgt
    have hlt : 230 * T.toNat < 320 * t.toNat := by
      have := UInt64.lt_iff_toNat_lt.mp hgt
      omega
    simp only [hlt, ↓reduceIte]
    simp only [bind_ok_iff, mulChecked_ok_iff, addChecked_ok_iff, divChecked_ok_iff, pure,
      Except.pure, Except.ok.injEq, UInt64.toNat_ofNat, h230] at h
    obtain ⟨a, ⟨-, ha⟩, b, ⟨-, hb⟩, c, ⟨-, hc⟩, d, ⟨-, hd⟩, e, ⟨-, he⟩, f, ⟨-, hf⟩, g, ⟨-, hg⟩,
      k, ⟨-, hk⟩, l, ⟨-, hl⟩, rfl⟩ := h
    have hsub : (high - low).toNat = high.toNat - low.toNat :=
      UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hgt)
    rw [hsub, hhigh, hlow] at he
    rw [he, hd, ha, hc, hb] at hf
    rw [hg, hk] at hl
    rw [toNat_max, hf, hl]
    -- The two forms differ only in the order of their factors.
    have hchurn : t.toNat * 320 - T.toNat * 230 = 320 * t.toNat - 230 * T.toNat := by omega
    have htopUp : N.toNat * 230 = 230 * N.toNat := by omega
    rw [hchurn, htopUp]
  · -- The top-up branch for small balances.
    rename_i hle
    have hnot : ¬ 230 * T.toNat < 320 * t.toNat := by
      have := UInt64.not_lt.mp hle
      have := UInt64.le_iff_toNat_le.mp this
      omega
    simp only [hnot, ↓reduceIte]
    simp only [bind_ok_iff, mulChecked_ok_iff, subChecked_ok_iff, divChecked_ok_iff,
      UInt64.toNat_ofNat] at h
    obtain ⟨a, ⟨-, ha⟩, b, ⟨-, hb⟩, c, ⟨-, hc⟩, d, ⟨-, hd⟩, e, ⟨-, he⟩, f, ⟨-, hf⟩, -, hg⟩ := h
    rw [hg, hc, hb, ha, hf, hd, he]
    have hfactor : 3 % 2 ^ 64 * N.toNat * (10 % 2 ^ 64) = 30 * N.toNat := by
      simp only [Nat.reducePow, Nat.reduceMod]
      omega
    rw [hfactor]

/-- Phase 0: the epochs are at most the longer of two bounds that grow with the validators.

The first is `160 N / (600 delta)`, the churn of validators with the balance term dropped.

The second is `230 N / (600 Delta)`, the top-up term, which also bounds the case of small balances.

There is no condition beyond success of the computation. -/
theorem phase0PeriodEpochs_le {N t T delta Delta epochs : UInt64}
    (h : phase0PeriodEpochs N t T delta Delta = .ok epochs) :
    epochs.toNat ≤ max (160 * N.toNat / (600 * delta.toNat))
      (230 * N.toNat / (600 * Delta.toNat)) := by
  have closed := phase0PeriodEpochs_eq_ok h
  generalize N.toNat = n at *
  generalize t.toNat = t' at *
  generalize T.toNat = T' at *
  generalize delta.toNat = d at *
  generalize Delta.toNat = D at *
  split at closed
  · -- Large balances: the churn term is at most `160 n / (600 d)`, or the top-up term is the max.
    rename_i hlt
    rw [closed]
    refine Nat.max_le.mpr ⟨Nat.le_trans ?_ (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
    by_cases hz : 600 * d * (2 * t' + T') = 0
    · rw [hz, Nat.div_zero]
      exact Nat.zero_le _
    · have hd : 0 < 600 * d := Nat.pos_of_ne_zero fun zero => hz (by rw [zero, Nat.zero_mul])
      have hw : 0 < 2 * t' + T' := Nat.pos_of_ne_zero fun zero => hz (by rw [zero, Nat.mul_zero])
      apply (Nat.le_div_iff_mul_le hd).mpr
      have hq := Nat.div_mul_le_self (n * (320 * t' - 230 * T')) (600 * d * (2 * t' + T'))
      generalize n * (320 * t' - 230 * T') / (600 * d * (2 * t' + T')) = x at hq ⊢
      refine Nat.le_of_mul_le_mul_right (c := 2 * t' + T') ?_ hw
      calc x * (600 * d) * (2 * t' + T') = x * (600 * d * (2 * t' + T')) := by ac_rfl
        _ ≤ n * (320 * t' - 230 * T') := hq
        _ ≤ n * (160 * (2 * t' + T')) := Nat.mul_le_mul_left n (by omega)
        _ = 160 * n * (2 * t' + T') := by ac_rfl
  · -- Small balances: the top-up term for small balances.
    rename_i hle
    rw [closed]
    refine Nat.le_trans ?_ (Nat.le_max_right _ _)
    by_cases hz : 200 * D * (T' - t') = 0
    · rw [hz, Nat.div_zero]
      exact Nat.zero_le _
    · have hD : 0 < 600 * D := by
        refine Nat.pos_of_ne_zero fun zero => hz ?_
        have : D = 0 := by omega
        rw [this]
        simp
      have hs : 0 < T' - t' := Nat.pos_of_ne_zero fun zero => hz (by rw [zero, Nat.mul_zero])
      apply (Nat.le_div_iff_mul_le hD).mpr
      have hq := Nat.div_mul_le_self (30 * n * t') (200 * D * (T' - t'))
      generalize 30 * n * t' / (200 * D * (T' - t')) = x at hq ⊢
      refine Nat.le_of_mul_le_mul_right (c := T' - t') ?_ hs
      have hbal : 90 * t' ≤ 230 * (T' - t') := by omega
      have hthree : x * (600 * D) * (T' - t') = 3 * (x * (200 * D * (T' - t'))) := by
        rw [show 600 * D = 3 * (200 * D) by omega]
        ac_rfl
      calc x * (600 * D) * (T' - t') = 3 * (x * (200 * D * (T' - t'))) := hthree
        _ ≤ 3 * (30 * n * t') := Nat.mul_le_mul_left 3 hq
        _ = n * (90 * t') := by ac_rfl
        _ ≤ n * (230 * (T' - t')) := Nat.mul_le_mul_left n hbal
        _ = 230 * n * (T' - t') := by ac_rfl

/-- Phase 0: the period is at most the withdrawal delay plus the longer of two bounds.

The first is `160 N / (600 delta)` and the second is `230 N / (600 Delta)`.

Here `N` is the number of active validators.

The churn of validators in one epoch is `delta`, and `Delta` is the deposits that fit in one epoch.

The bound needs no condition beyond success of the computation. -/
theorem computeWeakSubjectivityPeriodPhase0_le {config : Config}
    {state : BeaconState preset fork} {period : Epoch}
    (h : computeWeakSubjectivityPeriodPhase0 config state = .ok period) :
    period.toNat ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat +
      max (160 * (getActiveValidatorIndices state (getCurrentEpoch state)).length.toUInt64.toNat /
          (600 * (getValidatorChurnLimit config state).toNat))
        (230 * (getActiveValidatorIndices state (getCurrentEpoch state)).length.toUInt64.toNat /
          (600 * (preset.MAX_DEPOSITS.toNat * preset.SLOTS_PER_EPOCH.toNat))) := by
  unfold computeWeakSubjectivityPeriodPhase0 at h
  simp only [bind_ok_iff, mapError_ok_iff] at h
  obtain ⟨_, _, _, _, Delta, hDelta, epochs, hepochs, hadd⟩ := h
  have hsum := (addChecked_ok_iff.mp hadd).2
  have hbound := phase0PeriodEpochs_le hepochs
  rw [hsum, (mulChecked_ok_iff.mp hDelta).2] at *
  exact Nat.add_le_add_left hbound _

/-! ## The withdrawal delay is a lower bound -/

/-- At every fork, a period is at least the delay before a validator can withdraw. -/
theorem min_le_computeWeakSubjectivityPeriod {config : Config}
    {state : BeaconState preset fork} {period : Epoch}
    (h : computeWeakSubjectivityPeriod config state = .ok period) :
    config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY ≤ period := by
  unfold computeWeakSubjectivityPeriod at h
  split at h
  · obtain ⟨_, _, -, -, hperiod⟩ := computeWeakSubjectivityPeriodGloas_eq_ok_iff.mp h
    exact le_of_balanceChurnPeriod_eq_ok hperiod
  split at h
  · obtain ⟨_, _, -, -, hperiod⟩ := computeWeakSubjectivityPeriodElectra_eq_ok_iff.mp h
    exact le_of_balanceChurnPeriod_eq_ok hperiod
  -- Phase 0 adds its epochs to the delay last.
  unfold computeWeakSubjectivityPeriodPhase0 at h
  simp only [bind_ok_iff, mapError_ok_iff] at h
  obtain ⟨_, _, _, _, _, _, _, _, hadd⟩ := h
  have hsum := (addChecked_ok_iff.mp hadd).2
  exact UInt64.le_iff_toNat_le.mpr (hsum ▸ Nat.le_add_right _ _)

/-! ## An upper bound from Electra -/

/-- An amount rounded down to whole increments has the value of the rounded amount. -/
theorem toNat_roundToIncrement (preset : Preset) (amount : Gwei) :
    (roundToIncrement preset amount).toNat =
      amount.toNat - amount.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  unfold roundToIncrement
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
    rw [UInt64.toNat_mod]
    exact Nat.mod_le _ _)), UInt64.toNat_mod]

/-- An amount rounded down to whole increments is more than the amount less one increment.

It is at least any whole number of increments up to the amount. -/
theorem roundToIncrement_bounds {amount floor increment : Nat} (hincrement : 0 < increment)
    (hfloor : floor % increment = 0) (hle : floor ≤ amount) :
    floor ≤ amount - amount % increment ∧ amount < amount - amount % increment + increment := by
  have hmod := Nat.mod_lt amount hincrement
  have hsplit := Nat.div_add_mod amount increment
  have hfloorSplit := Nat.div_add_mod floor increment
  rw [hfloor, Nat.add_zero] at hfloorSplit
  -- Whole increments up to the amount are at most the whole increments of the amount.
  have hcount : floor / increment ≤ amount / increment := Nat.div_le_div_right hle
  have hwhole : increment * (floor / increment) ≤ increment * (amount / increment) :=
    Nat.mul_le_mul_left _ hcount
  omega

/-- In Electra and Fulu: the period is at most a bound that depends only on the parameters.

The churn is at least its minimum, and at least the total over the quotient, less one increment.

So the total is less than the quotient times the churn plus one increment.

The epochs that the churn needs are then at most `10 Q (m + i) / (200 m)`.

Here `Q` is the churn quotient, `m` the minimum churn and `i` the increment.

The minimum must be a positive whole number of increments, and the quotient positive. -/
theorem computeWeakSubjectivityPeriodElectra_le {config : Config}
    {state : BeaconState preset fork} {period : Epoch}
    (hminimum : 0 < config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat)
    (hwhole : config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat %
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (hquotient : 0 < config.CHURN_LIMIT_QUOTIENT.toNat)
    (h : computeWeakSubjectivityPeriodElectra config state = .ok period) :
    period.toNat ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat +
      10 * config.CHURN_LIMIT_QUOTIENT.toNat *
          (config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) /
        (200 * config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat) := by
  obtain ⟨total, churn, htotal, hchurn, hperiod⟩ :=
    computeWeakSubjectivityPeriodElectra_eq_ok_iff.mp h
  obtain ⟨-, -, hpos, -, hvalue⟩ := balanceChurnPeriod_eq_ok_iff.mp hperiod
  -- The churn is the rounded maximum of the minimum and the share of the total.
  simp only [getBalanceChurnLimit, htotal, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at hchurn
  subst hchurn
  generalize hQ : config.CHURN_LIMIT_QUOTIENT.toNat = Q at *
  generalize hm : config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat = m at *
  generalize hi : preset.EFFECTIVE_BALANCE_INCREMENT.toNat = i at *
  generalize ht : total.toNat = t at *
  -- A zero increment would make the minimum churn zero, since `m % 0 = m`.
  have hincrement : 0 < i := Nat.pos_of_ne_zero fun zero => by
    rw [zero, Nat.mod_zero] at hwhole
    omega
  rw [toNat_roundToIncrement, toNat_max, UInt64.toNat_div, hQ, hm, hi, ht] at hvalue hpos
  rw [hvalue]
  refine Nat.add_le_add_left ?_ _
  generalize hx : max m (t / Q) = x at hvalue hpos
  obtain ⟨hlow, hhigh⟩ := roundToIncrement_bounds hincrement hwhole (hx ▸ Nat.le_max_left m (t / Q))
  generalize hc : x - x % i = c at hlow hhigh hpos
  -- The total is less than the quotient times one more than its share, so less than `Q (c + i)`.
  have hshare : t / Q < c + i := Nat.lt_of_le_of_lt (hx ▸ Nat.le_max_right m (t / Q)) hhigh
  have htotalLt : t < Q * (c + i) := by
    have := Nat.lt_mul_div_succ t hquotient
    exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_left Q hshare)
  -- Write `q` for the epochs; then `q (200 c) ≤ 10 t < 10 Q (c + i)`.
  apply (Nat.le_div_iff_mul_le (by omega)).mpr
  generalize hq : 10 * t / (200 * c) = q
  have hqc : q * (200 * c) ≤ 10 * t := hq ▸ Nat.div_mul_le_self _ _
  -- Since `m ≤ c`, the ratio `(c + i) / c` is at most `(m + i) / m`.
  have hcross : (c + i) * m ≤ (m + i) * c := by
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_comm c m]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left i hlow) _
  have hstep : q * (200 * m) * c ≤ 10 * Q * (m + i) * c := by
    calc q * (200 * m) * c = q * (200 * c) * m := by ac_rfl
      _ ≤ 10 * t * m := Nat.mul_le_mul_right m hqc
      _ ≤ 10 * (Q * (c + i)) * m :=
        Nat.mul_le_mul_right m (Nat.mul_le_mul_left 10 (Nat.le_of_lt htotalLt))
      _ = 10 * Q * ((c + i) * m) := by ac_rfl
      _ ≤ 10 * Q * ((m + i) * c) := Nat.mul_le_mul_left _ hcross
      _ = 10 * Q * (m + i) * c := by ac_rfl
  exact Nat.le_of_mul_le_mul_right hstep hpos

/-- In Electra and Fulu, at the mainnet parameters, the period is at most 3558 epochs. -/
theorem computeWeakSubjectivityPeriodElectra_le_mainnet
    {state : BeaconState Preset.mainnet fork} {period : Epoch}
    (h : computeWeakSubjectivityPeriodElectra Config.mainnet state = .ok period) :
    period.toNat ≤ 3558 :=
  Nat.le_trans (computeWeakSubjectivityPeriodElectra_le (by decide) (by decide) (by decide) h)
    (by decide)

/-- The smaller of two 64-bit integers has the smaller value. -/
private theorem toNat_min_eq (a b : UInt64) : (min a b).toNat = min a.toNat b.toNat := by
  rw [UInt64.min_def, Nat.min_def]
  by_cases h : a ≤ b
  · simp [h, UInt64.le_iff_toNat_le.mp h]
  · simp [h, mt UInt64.le_iff_toNat_le.mpr h]

/-- From Gloas: the three churns follow from the total active balance, and bound it above.

Let `Qe` and `Qc` be the quotients, `m` the minimum, `M` the cap and `i` the increment.

When `m` is a multiple of `i`, the exit churn `e` is at least `m` and activations take `min M e`.

Rounding loses less than `i` in each share, so `(2 Qc + 3 Qe) t < Qe Qc (2 e + 3 c + 5 i)`. -/
private theorem gloasWeightedChurn_bounds {config : Config} {state : BeaconState preset fork}
    {total churn : Gwei} (gloas : .glamsterdam ≤ fork)
    (hincrement : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (hwhole : config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat %
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (hexitQ : 0 < config.CHURN_LIMIT_QUOTIENT_GLOAS.toNat)
    (hconsQ : 0 < config.CONSOLIDATION_CHURN_LIMIT_QUOTIENT.toNat)
    (htotal : getTotalActiveBalance state = .ok total)
    (hchurn : gloasWeightedChurn config state = .ok churn) :
    ∃ e c : Nat,
      config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat ≤ e ∧
      total.toNat < config.CHURN_LIMIT_QUOTIENT_GLOAS.toNat *
        (e + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ∧
      (2 * config.CONSOLIDATION_CHURN_LIMIT_QUOTIENT.toNat +
          3 * config.CHURN_LIMIT_QUOTIENT_GLOAS.toNat) * total.toNat <
        config.CHURN_LIMIT_QUOTIENT_GLOAS.toNat *
          config.CONSOLIDATION_CHURN_LIMIT_QUOTIENT.toNat *
          (2 * e + 3 * c + 5 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ∧
      churn.toNat = (2 * e) / 3 +
        min config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS.toNat e / 3 + c := by
  obtain ⟨exit, act, cons, hex, hac, hco, -, -, hch⟩ := gloasWeightedChurn_eq_ok_iff.mp hchurn
  simp only [getActivationChurnLimit, hex, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at hac
  simp only [getExitChurnLimit, htotal, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at hex
  simp only [getConsolidationChurnLimit, gloas, ↓reduceIte, htotal, bind, Except.bind, pure,
    Except.pure, Except.ok.injEq] at hco
  subst hac hex hco
  generalize hQe : config.CHURN_LIMIT_QUOTIENT_GLOAS.toNat = Qe at *
  generalize hQc : config.CONSOLIDATION_CHURN_LIMIT_QUOTIENT.toNat = Qc at *
  generalize hm : config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat = m at *
  generalize hM : config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS.toNat = M at *
  generalize hi : preset.EFFECTIVE_BALANCE_INCREMENT.toNat = i at *
  generalize ht : total.toNat = t at *
  rw [toNat_min_eq, toNat_roundToIncrement, toNat_roundToIncrement, toNat_max, UInt64.toNat_div,
    UInt64.toNat_div, hQe, hQc, hm, hM, hi, ht] at hch
  generalize hx : max m (t / Qe) = x at hch
  obtain ⟨hem, hexHi⟩ :=
    roundToIncrement_bounds hincrement hwhole (hx ▸ Nat.le_max_left m (t / Qe))
  obtain ⟨-, hcoHi⟩ := roundToIncrement_bounds hincrement (Nat.zero_mod i) (Nat.zero_le (t / Qc))
  generalize he : x - x % i = e at hem hexHi hch
  generalize hc : t / Qc - (t / Qc) % i = c at hcoHi hch
  have hexShare : t / Qe < e + i := Nat.lt_of_le_of_lt (hx ▸ Nat.le_max_right m (t / Qe)) hexHi
  have htQe : t < Qe * (e + i) :=
    Nat.lt_of_lt_of_le (Nat.lt_mul_div_succ t hexitQ) (Nat.mul_le_mul_left Qe hexShare)
  have htQc : t < Qc * (c + i) :=
    Nat.lt_of_lt_of_le (Nat.lt_mul_div_succ t hconsQ) (Nat.mul_le_mul_left Qc hcoHi)
  refine ⟨e, c, hem, htQe, ?_, hch⟩
  have hleft : 2 * Qc * t < 2 * Qe * Qc * (e + i) := by
    calc 2 * Qc * t = 2 * Qc * t := rfl
      _ < 2 * Qc * (Qe * (e + i)) := Nat.mul_lt_mul_of_pos_left htQe (by omega)
      _ = 2 * Qe * Qc * (e + i) := by ac_rfl
  have hright : 3 * Qe * t < 3 * Qe * Qc * (c + i) := by
    calc 3 * Qe * t < 3 * Qe * (Qc * (c + i)) := Nat.mul_lt_mul_of_pos_left htQc (by omega)
      _ = 3 * Qe * Qc * (c + i) := by ac_rfl
  calc (2 * Qc + 3 * Qe) * t = 2 * Qc * t + 3 * Qe * t := Nat.add_mul _ _ _
    _ < 2 * Qe * Qc * (e + i) + 3 * Qe * Qc * (c + i) := Nat.add_lt_add hleft hright
    _ = Qe * Qc * (2 * e + 3 * c + 5 * i) := by
      have : 2 * (e + i) + 3 * (c + i) = 2 * e + 3 * c + 5 * i := by omega
      calc 2 * Qe * Qc * (e + i) + 3 * Qe * Qc * (c + i)
          = Qe * Qc * (2 * (e + i)) + Qe * Qc * (3 * (c + i)) := by ac_rfl
        _ = Qe * Qc * (2 * (e + i) + 3 * (c + i)) := (Nat.mul_add _ _ _).symm
        _ = Qe * Qc * (2 * e + 3 * c + 5 * i) := by rw [this]

/-- From Gloas: the period is at most a bound that depends only on the parameters.

The exit churn is at least its minimum `m` and exceeds `t / Qe - i`.

The consolidation churn exceeds `t / Qc - i`.

When `5 i + 2 ≤ 3 (min M m / 3)`, activations cover the rounding: `2 e + 3 c + 5 i ≤ 3 churn`.

The epochs that the churn needs are then at most `30 Qe Qc / (200 (2 Qc + 3 Qe))`. -/
theorem computeWeakSubjectivityPeriodGloas_le {config : Config}
    {state : BeaconState preset fork} {period : Epoch} (gloas : .glamsterdam ≤ fork)
    (hwhole : config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat %
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (hexitQ : 0 < config.CHURN_LIMIT_QUOTIENT_GLOAS.toNat)
    (hconsQ : 0 < config.CONSOLIDATION_CHURN_LIMIT_QUOTIENT.toNat)
    (hactFloor : 5 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 2 ≤
      3 * (min config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS.toNat
        config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat / 3))
    (h : computeWeakSubjectivityPeriodGloas config state = .ok period) :
    period.toNat ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat +
      30 * config.CHURN_LIMIT_QUOTIENT_GLOAS.toNat *
          config.CONSOLIDATION_CHURN_LIMIT_QUOTIENT.toNat /
        (200 * (2 * config.CONSOLIDATION_CHURN_LIMIT_QUOTIENT.toNat +
          3 * config.CHURN_LIMIT_QUOTIENT_GLOAS.toNat)) := by
  obtain ⟨total, churn, htotal, hchurn, hperiod⟩ :=
    computeWeakSubjectivityPeriodGloas_eq_ok_iff.mp h
  obtain ⟨-, -, hpos, -, hvalue⟩ := balanceChurnPeriod_eq_ok_iff.mp hperiod
  -- A zero increment would make the minimum churn zero, and the activation floor then fails.
  have hincrement : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    Nat.pos_of_ne_zero fun zero => by
      rw [zero, Nat.mod_zero] at hwhole
      rw [zero, hwhole] at hactFloor
      omega
  obtain ⟨e, c, hem, -, hsum, hch⟩ :=
    gloasWeightedChurn_bounds gloas hincrement hwhole hexitQ hconsQ htotal hchurn
  generalize hQe : config.CHURN_LIMIT_QUOTIENT_GLOAS.toNat = Qe at *
  generalize hQc : config.CONSOLIDATION_CHURN_LIMIT_QUOTIENT.toNat = Qc at *
  generalize hm : config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat = m at *
  generalize hM : config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS.toNat = M at *
  generalize hi : preset.EFFECTIVE_BALANCE_INCREMENT.toNat = i at *
  generalize ht : total.toNat = t at *
  generalize hchNat : churn.toNat = w at *
  rw [hvalue]
  refine Nat.add_le_add_left ?_ _
  have hminLe : min M m ≤ min M e := by omega
  have hactLe : 5 * i + 2 ≤ 3 * (min M e / 3) :=
    Nat.le_trans hactFloor (Nat.mul_le_mul_left 3 (Nat.div_le_div_right hminLe))
  have hthree : 2 * e + 3 * c + 5 * i ≤ 3 * w := by omega
  have htotalBound : (2 * Qc + 3 * Qe) * t < Qe * Qc * (3 * w) :=
    Nat.lt_of_lt_of_le hsum (Nat.mul_le_mul_left (Qe * Qc) hthree)
  apply (Nat.le_div_iff_mul_le (by omega)).mpr
  generalize hq : 10 * t / (200 * w) = q
  have hqw : q * (200 * w) ≤ 10 * t := hq ▸ Nat.div_mul_le_self _ _
  have hstep : q * (200 * (2 * Qc + 3 * Qe)) * w ≤ 30 * Qe * Qc * w := by
    calc q * (200 * (2 * Qc + 3 * Qe)) * w
        = (2 * Qc + 3 * Qe) * (q * (200 * w)) := by ac_rfl
      _ ≤ (2 * Qc + 3 * Qe) * (10 * t) := Nat.mul_le_mul_left _ hqw
      _ = 10 * ((2 * Qc + 3 * Qe) * t) := by ac_rfl
      _ ≤ 10 * (Qe * Qc * (3 * w)) := Nat.mul_le_mul_left 10 (Nat.le_of_lt htotalBound)
      _ = 30 * Qe * Qc * w := by ac_rfl
  exact Nat.le_of_mul_le_mul_right hstep hpos

/-- From Gloas, at the mainnet parameters, the period is at most 1658 epochs.

Below the activation cap of 256 ether, the exit churn is below 256 ether and `t < 8,421,376` ether.

At or above the cap, the activation third contributes 256 / 3 ether, about 85.3.

The precondition `10 t < 2^64` then bounds the total `t`. -/
theorem computeWeakSubjectivityPeriodGloas_le_mainnet
    {state : BeaconState Preset.mainnet fork} {period : Epoch} (gloas : .glamsterdam ≤ fork)
    (h : computeWeakSubjectivityPeriodGloas Config.mainnet state = .ok period) :
    period.toNat ≤ 1658 := by
  obtain ⟨total, churn, htotal, hchurn, hperiod⟩ :=
    computeWeakSubjectivityPeriodGloas_eq_ok_iff.mp h
  obtain ⟨htOverflow, -, hpos, -, hvalue⟩ := balanceChurnPeriod_eq_ok_iff.mp hperiod
  obtain ⟨e, c, hem, htQe, hsum, hch⟩ :=
    gloasWeightedChurn_bounds gloas (by decide) (by decide) (by decide) (by decide) htotal hchurn
  have hdelay : Config.mainnet.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat = 256 := rfl
  have hQe : Config.mainnet.CHURN_LIMIT_QUOTIENT_GLOAS.toNat = 32768 := rfl
  have hQc : Config.mainnet.CONSOLIDATION_CHURN_LIMIT_QUOTIENT.toNat = 65536 := rfl
  have hm : Config.mainnet.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat = 128000000000 := rfl
  have hM : Config.mainnet.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS.toNat = 256000000000 := rfl
  have hi : Preset.mainnet.EFFECTIVE_BALANCE_INCREMENT.toNat = 1000000000 := rfl
  simp only [hQe, hQc, hm, hM, hi] at hem htQe hsum hch
  rw [hvalue, hdelay]
  generalize total.toNat = t at htOverflow htQe hsum ⊢
  generalize churn.toNat = w at hpos hch ⊢
  have hdiv : 10 * t / (200 * w) < 1403 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
  omega

/-! ## The staleness check -/

/-- A checkpoint is within its period exactly when every step of the check succeeds.

The state holds the checkpoint's root at its epoch, and is at that epoch.

The period and the current slot have values, and the end of the period is below `2^64`.

The answer is then whether the current epoch is at most the end of the period. -/
theorem isWithinWeakSubjectivityPeriod_eq_ok_iff {storeFork : Base.Fork} {config : Config}
    {store : Store preset storeFork} {wsState : BeaconState preset fork}
    {wsCheckpoint : Checkpoint} {within : Bool} :
    isWithinWeakSubjectivityPeriod config store wsState wsCheckpoint = .ok within ↔
      getBlockRoot wsState wsCheckpoint.epoch = .ok wsCheckpoint.root ∧
        computeEpochAtSlot preset wsState.slot = wsCheckpoint.epoch ∧
        ∃ period slot, computeWeakSubjectivityPeriod config wsState = .ok period ∧
          store.getCurrentSlot config = .ok slot ∧
          wsCheckpoint.epoch.toNat + period.toNat < 2 ^ 64 ∧
          within = decide ((computeEpochAtSlot preset slot).toNat ≤
            wsCheckpoint.epoch.toNat + period.toNat) := by
  unfold isWithinWeakSubjectivityPeriod
  simp only [bind_ok_iff, mapError_ok_iff]
  constructor
  · rintro ⟨root, hroot, h⟩
    -- Each failed check throws, so the root and the epoch match.
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    rename_i hrootEq
    simp only [ne_eq, Decidable.not_not] at hrootEq
    subst hrootEq
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    rename_i hepoch
    simp only [ne_eq, Decidable.not_not] at hepoch
    simp only [bind_ok_iff, mapError_ok_iff, addChecked_ok_iff, pure, Except.pure,
      Except.ok.injEq] at h
    obtain ⟨period, hperiod, slot, hslot, last, ⟨hlt, hlast⟩, rfl⟩ := h
    rw [hepoch] at hlt hlast
    exact ⟨hroot, hepoch, period, slot, hperiod, hslot, hlt, by
      simp [UInt64.le_iff_toNat_le, hlast]⟩
  · rintro ⟨hroot, hepoch, period, slot, hperiod, hslot, hlt, rfl⟩
    refine ⟨wsCheckpoint.root, hroot, ?_⟩
    simp [hepoch, hperiod, hslot, addChecked_of_lt hlt, bind, Except.bind, pure, Except.pure,
      Except.mapError, UInt64.le_iff_toNat_le, toNat_add_of_lt hlt]

/-- A checkpoint within its period at the current slot of a store is within it at earlier slots.

So a checkpoint that is stale at some time stays stale at every later time. -/
theorem isWithinWeakSubjectivityPeriod_of_slot_le {storeFork storeFork' : Base.Fork}
    {config : Config} {store : Store preset storeFork} {store' : Store preset storeFork'}
    {wsState : BeaconState preset fork} {wsCheckpoint : Checkpoint} {slot slot' : Slot}
    (hwithin : isWithinWeakSubjectivityPeriod config store wsState wsCheckpoint = .ok true)
    (hslot : store.getCurrentSlot config = .ok slot)
    (hslot' : store'.getCurrentSlot config = .ok slot') (hle : slot' ≤ slot) :
    isWithinWeakSubjectivityPeriod config store' wsState wsCheckpoint = .ok true := by
  obtain ⟨hroot, hepoch, period, slot₀, hperiod, hslot₀, hlt, hdecide⟩ :=
    isWithinWeakSubjectivityPeriod_eq_ok_iff.mp hwithin
  rw [hslot] at hslot₀
  cases hslot₀
  -- An earlier slot is in an epoch no later.
  have hepochLe :
      (computeEpochAtSlot preset slot').toNat ≤ (computeEpochAtSlot preset slot).toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp hle)
  refine isWithinWeakSubjectivityPeriod_eq_ok_iff.mpr
    ⟨hroot, hepoch, period, slot', hperiod, hslot', hlt, ?_⟩
  have := of_decide_eq_true hdecide.symm
  exact (decide_eq_true (Nat.le_trans hepochLe this)).symm

end EthLib.Consensus
