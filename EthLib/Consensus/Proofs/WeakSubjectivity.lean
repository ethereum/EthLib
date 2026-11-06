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

In Phase 0, a computed period is one of the two expressions of the rule, on natural numbers.

At every fork, the period is at least the withdrawal delay.

In Electra and Fulu, the period is at most a bound of the parameters alone: 3558 epochs on mainnet.

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
    (hincrement : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
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
  Nat.le_trans (computeWeakSubjectivityPeriodElectra_le (by decide) (by decide) (by decide)
    (by decide) h) (by decide)

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
