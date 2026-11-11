module

public import EthLib.Consensus.Proofs.Models.Ffg.AccountableSafety
public import EthLib.Consensus.Proofs.Transition.FfgStake
public import EthLib.Consensus.Proofs.WeakSubjectivity

/-!
# Proofs: the weak subjectivity period keeps a slashable fraction of the stake

A node that starts from a weak subjectivity checkpoint trusts the active validators of its state.

Their effective balances are the stake of the Casper FFG model, and the trusted set is `V₀`.

Take two conflicting finalized checkpoints, and the justified sets between their epochs.

Measure the change of a set since `V₀` as the stake that joined plus twice the stake that left.

Assume each change is at most `3 c` for each epoch of churn of the period, with `c` its churn.

The epochs of churn are the epochs of the period less the delay before a validator can withdraw.

Then validators with at least `1/3 - SAFETY_DECAY/100` of the stake of `V₀` are slashable.

The bound follows Gasper Theorem 8.3, [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).

Why `3 c` for each epoch, from Electra, with [EIP-7251] and its balance churn `c`.

- Deposits and exits each take at most the churn `a ≤ c` of activations and exits.
- Consolidations take the rest of `c`, and their sources leave the set.
- So an epoch adds at most `a` and removes at most `c`, a change of at most `a + 2 c ≤ 3 c`.

From Gloas, [EIP-8061] weighs exits two thirds, activations one third and consolidations one.

There an epoch changes the set by at most three times the weighted churn.

Rounding can add 4 Gwei to that when the churn of consolidations is zero.

The queues carry unused churn to later epochs, so the bound can hold over a window, not each epoch.

No theorem yet derives that bound from the state transition, so it is an assumption here.

The rule spends the delay on keeping exits slashable, and the other epochs of the period on churn.

The assumption takes the change over those other epochs as given.

Activations have no such delay, and a validator outside the registry of the checkpoint weighs zero.

The stake of each validator stays its effective balance at the checkpoint, as the model needs.

From Phase 0 to Deneb, the rule counts `N` validators of average balance `t` and largest `T`.

It takes the churn of `delta` validators in an epoch, and `Delta` top-ups in an epoch.

A top-up raises the balance of a validator that already exists, and the model has no such change.

So the theorem assumes that the sets gain and lose at most `delta` validators per epoch of churn.

With each stake at most `T`, that is a change of at most `3 delta T` for each epoch of churn.

The churn of later epochs can grow with the validators.

The assumption takes the churn at the checkpoint for every epoch of churn.

With large balances, `230 T < 320 t`, the rule's epochs for churn always fit the decayed margin.

The rule takes the longer of those and its epochs for top-ups, so the top-ups must fit too.

When they do not, or with small balances, the period can exceed what the churn allows.

Then the theorem gives nothing, and a model with top-ups would be needed.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251
[EIP-8061]: https://eips.ethereum.org/EIPS/eip-8061#churn-computations
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Models.Ffg

variable {preset : Preset} {fork : Base.Fork} {β : Type*} [Preorder β]

open scoped Classical in
/-- From Electra: a slow change of the validator sets keeps a slashable fraction of the stake.

The trusted set is the active validators of the state at the checkpoint, weighed by its balances.

Its stake must be at least one increment, so that it is the total active balance.

The churn is the one the period uses: weighted from Gloas, the balance churn before.

Take two finalized checkpoints whose blocks conflict.

Take each justified checkpoint whose epoch lies between theirs.

Its set changes since the trusted set by at most three times the churn per epoch of churn.

The change counts the stake that joined plus twice the stake that left.

Then two justified checkpoints `l` and `r` in that range have slashable validators of both sets.

They hold at least `1/3 - SAFETY_DECAY/100` of the trusted stake.

No epoch of the model is tied to the checkpoint's epoch; the assumed change carries the window. -/
theorem accountable_safety_of_weakSubjectivityPeriod {config : Config}
    {state : BeaconState preset fork} (electra : .pectra ≤ fork) {period churn : UInt64}
    (periodOk : computeWeakSubjectivityPeriod config state = .ok period)
    (churnOk : if .glamsterdam ≤ fork then gloasWeightedChurn config state = .ok churn
      else getBalanceChurnLimit config state = .ok churn)
    (large : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      stake (fun index => balanceAt state index.toNat)
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset)
    {V : Models.Ffg.Checkpoint β → Finset ValidatorIndex} {genesis : β}
    {votes : Set (Vote ValidatorIndex β)} {c₁ c₂ : Models.Ffg.Checkpoint β}
    (h₁ : Finalized V (fun index => balanceAt state index.toNat) genesis votes c₁)
    (h₂ : Finalized V (fun index => balanceAt state index.toNat) genesis votes c₂)
    (hc : Conflicting c₁.block c₂.block)
    (change : ∀ c : Models.Ffg.Checkpoint β, min c₁.epoch c₂.epoch ≤ c.epoch →
      c.epoch ≤ max c₁.epoch c₂.epoch →
      Justified V (fun index => balanceAt state index.toNat) genesis votes c →
      stake (fun index => balanceAt state index.toNat)
          (V c \ (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset) +
        2 * stake (fun index => balanceAt state index.toNat)
          ((getActiveValidatorIndices state (getCurrentEpoch state)).toFinset \ V c) ≤
        (period.toNat - config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) * (3 * churn.toNat)) :
    ∃ l r : Models.Ffg.Checkpoint β,
      min c₁.epoch c₂.epoch ≤ l.epoch ∧ l.epoch ≤ max c₁.epoch c₂.epoch ∧
      min c₁.epoch c₂.epoch ≤ r.epoch ∧ r.epoch ≤ max c₁.epoch c₂.epoch ∧
      Justified V (fun index => balanceAt state index.toNat) genesis votes l ∧
      Justified V (fun index => balanceAt state index.toNat) genesis votes r ∧
      (100 - 3 * SAFETY_DECAY.toNat) *
          stake (fun index => balanceAt state index.toNat)
            (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset ≤
        300 * stake (fun index => balanceAt state index.toNat)
          {v ∈ V l ∩ V r | Slashable votes v} := by
  obtain ⟨l, r, lo₁, hi₁, lo₂, hi₂, hl, hr, bound⟩ :=
    accountable_safety_of_change h₁ h₂ hc _ _ change
  refine ⟨l, r, lo₁, hi₁, lo₂, hi₂, hl, hr, ?_⟩
  obtain ⟨total, totalOk, periodOk⟩ :=
    balanceChurnPeriod_of_computeWeakSubjectivityPeriod_eq_ok electra periodOk churnOk
  -- With at least one increment of stake, the total active balance is that stake.
  obtain ⟨-, -, totalEq⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok totalOk)
  rw [Nat.max_eq_right large] at totalEq
  rw [← totalEq] at bound ⊢
  exact safetyMargin_of_balanceChurnPeriod_eq_ok periodOk bound

/-! ## Phase 0 to Deneb -/

open scoped Classical in
/-- Phase 0 to Deneb: a slow change of the validator sets keeps a slashable fraction of the stake.

The trusted set is the active validators of the state at the checkpoint, weighed by its balances.

Its stake must be at least one increment, so that it is the total active balance.

Assume each balance at most the largest effective balance, a whole number `T` of ether.

The rule counts `N` active validators of average balance `t` in ether, rounded down.

Assume large balances, `230 T < 320 t`, so that the rule weighs churn against top-ups.

Assume its epochs for top-ups move at most `N t / 20` ether at the churn of validators.

Take two finalized checkpoints whose blocks conflict.

Take each justified checkpoint whose epoch lies between theirs.

At most the churn of validators per epoch of churn joined its set since the trusted set.

At most as many left it.

The epochs of churn leave out the withdrawal delay, as from Electra.

Then two justified checkpoints `l` and `r` in that range have slashable validators of both sets.

They hold at least `1/3 - SAFETY_DECAY/100` of the trusted stake. -/
theorem accountable_safety_of_weakSubjectivityPeriod_of_lt_electra {config : Config}
    {state : BeaconState preset fork} (before : fork < .pectra) {period total : UInt64} (periodOk : computeWeakSubjectivityPeriod config state = .ok period)
    (totalOk : getTotalActiveBalance state = .ok total)
    (large : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      stake (fun index => balanceAt state index.toNat)
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset)
    (capped : ∀ index, balanceAt state index ≤ preset.MAX_EFFECTIVE_BALANCE.toNat)
    (wholeEther : preset.MAX_EFFECTIVE_BALANCE.toNat % ETH_TO_GWEI.toNat = 0)
    {N t T : ℕ} (hN : N = (getActiveValidatorIndices state (getCurrentEpoch state)).length)
    (ht : t = total.toNat / N / ETH_TO_GWEI.toNat)
    (hT : T = preset.MAX_EFFECTIVE_BALANCE.toNat / ETH_TO_GWEI.toNat)
    (largeBalances : 230 * T < 320 * t)
    (topUps : 20 * (230 * N / (600 * (preset.MAX_DEPOSITS.toNat * preset.SLOTS_PER_EPOCH.toNat)) *
      (getValidatorChurnLimit config state).toNat * T) ≤ N * t)
    {V : Models.Ffg.Checkpoint β → Finset ValidatorIndex} {genesis : β}
    {votes : Set (Vote ValidatorIndex β)} {c₁ c₂ : Models.Ffg.Checkpoint β}
    (h₁ : Finalized V (fun index => balanceAt state index.toNat) genesis votes c₁)
    (h₂ : Finalized V (fun index => balanceAt state index.toNat) genesis votes c₂)
    (hc : Conflicting c₁.block c₂.block)
    (change : ∀ c : Models.Ffg.Checkpoint β, min c₁.epoch c₂.epoch ≤ c.epoch →
      c.epoch ≤ max c₁.epoch c₂.epoch →
      Justified V (fun index => balanceAt state index.toNat) genesis votes c →
      (V c \ (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset).card ≤
          (period.toNat - config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) *
            (getValidatorChurnLimit config state).toNat ∧
        ((getActiveValidatorIndices state (getCurrentEpoch state)).toFinset \ V c).card ≤
          (period.toNat - config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) *
            (getValidatorChurnLimit config state).toNat) :
    ∃ l r : Models.Ffg.Checkpoint β,
      min c₁.epoch c₂.epoch ≤ l.epoch ∧ l.epoch ≤ max c₁.epoch c₂.epoch ∧
      min c₁.epoch c₂.epoch ≤ r.epoch ∧ r.epoch ≤ max c₁.epoch c₂.epoch ∧
      Justified V (fun index => balanceAt state index.toNat) genesis votes l ∧
      Justified V (fun index => balanceAt state index.toNat) genesis votes r ∧
      (100 - 3 * SAFETY_DECAY.toNat) *
          stake (fun index => balanceAt state index.toNat)
            (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset ≤
        300 * stake (fun index => balanceAt state index.toNat)
          {v ∈ V l ∩ V r | Slashable votes v} := by
  -- Before Electra the period is the Phase 0 rule.
  have notElectra : ¬ Base.Fork.pectra ≤ fork := Nat.not_le_of_lt before
  have notGloas : ¬ Base.Fork.glamsterdam ≤ fork :=
    Nat.not_le_of_lt (Nat.lt_trans before (by decide))
  have within : state.RegistryWithinLimit :=
    state.validators.bound (Nat.lt_trans before (by decide))
  simp only [computeWeakSubjectivityPeriod, notGloas, notElectra, ↓reduceIte,
    computeWeakSubjectivityPeriodPhase0, bind_ok_iff, mapError_ok_iff] at periodOk
  obtain ⟨total', totalOk', average, averageOk, Delta, DeltaOk, epochs, epochsOk, periodOk⟩ :=
    periodOk
  rw [totalOk, Except.ok.injEq] at totalOk'
  subst totalOk'
  -- The arguments of the rule, read as natural numbers.
  have hNat : (getActiveValidatorIndices state (getCurrentEpoch state)).length.toUInt64.toNat = N :=
    hN ▸ toNat_length_getActiveValidatorIndices within _
  obtain ⟨-, hAverage⟩ := divChecked_ok_iff.mp averageOk
  have ht' : (average / ETH_TO_GWEI).toNat = t := by
    rw [UInt64.toNat_div, hAverage, hNat, ht]
  have hT' : (preset.MAX_EFFECTIVE_BALANCE / ETH_TO_GWEI).toNat = T := by
    rw [UInt64.toNat_div, hT]
  have hDelta : Delta.toNat = preset.MAX_DEPOSITS.toNat * preset.SLOTS_PER_EPOCH.toNat :=
    (mulChecked_ok_iff.mp DeltaOk).2
  have hEpochs :
      period.toNat - config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat = epochs.toNat := by
    rw [(addChecked_ok_iff.mp periodOk).2]
    omega
  -- With at least one increment of stake, the total active balance is that stake.
  obtain ⟨-, -, totalEq⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok totalOk)
  rw [Nat.max_eq_right large] at totalEq
  -- A set of validators weighs at most the largest effective balance for each of them.
  have perValidator : ∀ S : Finset ValidatorIndex,
      stake (fun index => balanceAt state index.toNat) S ≤
        S.card * preset.MAX_EFFECTIVE_BALANCE.toNat := fun S =>
    Finset.sum_le_card_nsmul S (fun index => balanceAt state index.toNat)
      preset.MAX_EFFECTIVE_BALANCE.toNat fun index _ => capped index.toNat
  -- The average balance is at most the largest one.
  have averageLe : t ≤ T := by
    have activeLe : total.toNat ≤ N * preset.MAX_EFFECTIVE_BALANCE.toNat := by
      rw [totalEq]
      refine (perValidator _).trans (Nat.mul_le_mul_right _ ?_)
      rw [hN]
      exact List.toFinset_card_le _
    rw [ht, hT]
    exact Nat.div_le_div_right (Nat.div_le_of_le_mul activeLe)
  have fit := churn_le_of_phase0PeriodEpochs_eq_ok epochsOk
  rw [hNat, ht', hT', hDelta] at fit
  have fit := fit largeBalances averageLe topUps
  -- Each justified set changes by at most `3 n δ` largest balances.
  obtain ⟨l, r, lo₁, hi₁, lo₂, hi₂, hl, hr, bound⟩ :=
    accountable_safety_of_change h₁ h₂ hc
      (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset
      (3 * (epochs.toNat * (getValidatorChurnLimit config state).toNat *
        preset.MAX_EFFECTIVE_BALANCE.toNat))
      fun c lo hi hj => by
        obtain ⟨joined, left⟩ := change c lo hi hj
        rw [hEpochs] at joined left
        have := (perValidator _).trans (Nat.mul_le_mul_right _ joined)
        have := (perValidator _).trans (Nat.mul_le_mul_right _ left)
        omega
  refine ⟨l, r, lo₁, hi₁, lo₂, hi₂, hl, hr, ?_⟩
  -- The rule's average gives `N t` ether of stake at most.
  have averageStake : N * t * ETH_TO_GWEI.toNat ≤ total.toNat := by
    rw [ht, Nat.mul_assoc]
    exact (Nat.mul_le_mul_left N (Nat.div_mul_le_self _ _)).trans (Nat.mul_div_le _ _)
  have whole : preset.MAX_EFFECTIVE_BALANCE.toNat = T * ETH_TO_GWEI.toNat := by
    rw [hT, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero wholeEther)]
  have moved : 20 * (epochs.toNat * (getValidatorChurnLimit config state).toNat *
      preset.MAX_EFFECTIVE_BALANCE.toNat) ≤ total.toNat := by
    rw [whole]
    calc 20 * (epochs.toNat * (getValidatorChurnLimit config state).toNat *
          (T * ETH_TO_GWEI.toNat))
        = 20 * (epochs.toNat * (getValidatorChurnLimit config state).toNat * T) *
          ETH_TO_GWEI.toNat := by ac_rfl
      _ ≤ N * t * ETH_TO_GWEI.toNat := Nat.mul_le_mul_right _ fit
      _ ≤ total.toNat := averageStake
  have hD : SAFETY_DECAY.toNat = 10 := rfl
  rw [hD, ← totalEq]
  omega

end EthLib.Consensus
