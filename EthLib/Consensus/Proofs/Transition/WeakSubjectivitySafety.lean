module

public import EthLib.Consensus.Proofs.Models.Ffg.AccountableSafety
public import EthLib.Consensus.Proofs.Transition.FfgStake
public import EthLib.Consensus.Proofs.WeakSubjectivity

/-!
# Proofs: the weak subjectivity period keeps a slashable fraction of the stake

A node that starts from a weak subjectivity checkpoint trusts the active validators of its state.

Their effective balances are the stake of the Casper FFG model.

The trusted set is `V₀`.

Take two conflicting finalized checkpoints, and the justified sets between their epochs.

Measure the change of a set since `V₀` as the stake that joined plus twice the stake that left.

Assume each change is at most three times the churn times the epochs of churn of the period.

The epochs of churn are those of the period, less the delay before a validator can withdraw.

Then validators with at least `1/3 - SAFETY_DECAY/100` of the stake of `V₀` are slashable.

No theorem yet derives that bound on the change from the state transition, so it is an assumption.

The bound follows Gasper Theorem 8.3, [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Models.Ffg

variable {preset : Preset} {fork : Base.Fork} {β : Type*} [Preorder β]

open scoped Classical in
/-- From Electra: a slow change of the validator sets keeps a slashable fraction of the stake.

The trusted set is the active validators of the state at the checkpoint, weighed by its balances.

Take two finalized checkpoints whose blocks conflict.

The set of each justified checkpoint between them must change by at most `3 c` per epoch of churn.

Then two justified checkpoints in that range have slashable validators of both sets.

They hold at least `1/3 - SAFETY_DECAY/100` of the trusted stake. -/
theorem accountable_safety_of_weakSubjectivityPeriod {config : Config}
    {state : BeaconState preset fork} (electra : .pectra ≤ fork) {period churn : UInt64}
    (periodOk : computeWeakSubjectivityPeriod config state = .ok period)
    -- The churn `c` is the one the period uses.
    --
    -- It is the weighted churn from Gloas, and the balance churn before.
    --
    -- From Gloas, [EIP-8061] weighs exits two thirds, activations one third and consolidations one.
    --
    -- There an epoch changes the set by at most three times the weighted churn.
    --
    -- [EIP-8061]: https://eips.ethereum.org/EIPS/eip-8061#churn-computations
    (churnOk : if .glamsterdam ≤ fork then gloasWeightedChurn config state = .ok churn
      else getBalanceChurnLimit config state = .ok churn)
    -- The trusted stake must be at least one increment, so that it is the total active balance.
    (large : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      stake (fun index => balanceAt state index.toNat)
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset)
    {V : Models.Ffg.Checkpoint β → Finset ValidatorIndex} {genesis : β}
    {votes : Set (Vote ValidatorIndex β)} {c₁ c₂ : Models.Ffg.Checkpoint β}
    -- Take a finalized checkpoint.
    (h₁ : Finalized V (fun index => balanceAt state index.toNat) genesis votes c₁)
    -- Take a second finalized checkpoint.
    (h₂ : Finalized V (fun index => balanceAt state index.toNat) genesis votes c₂)
    -- The blocks of the two finalized checkpoints conflict.
    (hc : Conflicting c₁.block c₂.block)
    -- Take each justified checkpoint whose epoch lies between theirs.
    --
    -- Its set changes since the trusted set by at most three times the churn per epoch of churn.
    --
    -- The change counts the stake that joined plus twice the stake that left.
    --
    -- The epochs of churn are those of the period, less the delay before a validator can withdraw.
    --
    -- From Electra, [EIP-7251] sets the balance churn `c`.
    --
    -- Each epoch then changes a set by at most `3 c`.
    --
    -- - Deposits and exits each take at most the churn `a ≤ c` of activations and exits.
    -- - Consolidations take the rest of `c`, and their sources leave the set.
    -- - So an epoch adds at most `a` and removes at most `c`, a change of at most `a + 2 c ≤ 3 c`.
    --
    -- From Gloas, rounding can add 4 Gwei to that when the churn of consolidations is zero.
    --
    -- The queues carry unused churn to later epochs.
    --
    -- So the bound can hold over a window, not each epoch.
    --
    -- No epoch of the model is tied to the epoch of the checkpoint.
    --
    -- The assumed change carries the window.
    --
    -- The rule spends the delay on keeping exits slashable.
    --
    -- It spends the other epochs of the period on churn.
    --
    -- The assumption takes the change over those other epochs as given.
    --
    -- Activations have no such delay.
    --
    -- A validator outside the registry of the checkpoint weighs zero.
    --
    -- The stake of each validator stays its effective balance at the checkpoint.
    --
    -- The model needs that.
    --
    -- [EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251
    (change : ∀ c : Models.Ffg.Checkpoint β, min c₁.epoch c₂.epoch ≤ c.epoch →
      c.epoch ≤ max c₁.epoch c₂.epoch →
      Justified V (fun index => balanceAt state index.toNat) genesis votes c →
      stake (fun index => balanceAt state index.toNat)
          (V c \ (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset) +
        2 * stake (fun index => balanceAt state index.toNat)
          ((getActiveValidatorIndices state (getCurrentEpoch state)).toFinset \ V c) ≤
        (period.toNat - config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) * (3 * churn.toNat)) :
    -- Then two justified checkpoints `l` and `r` lie in that range.
    --
    -- They have slashable validators of both of their sets.
    --
    -- Those validators hold at least `1/3 - SAFETY_DECAY/100` of the trusted stake.
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

It assumes large balances, without which the theorem gives nothing.

The model has no top-up, which raises the balance of a validator that already exists.

Take two finalized checkpoints whose blocks conflict, and each justified checkpoint between them.

Since the trusted set, at most the churn of validators per epoch of churn joins its set.

At most as many leave it.

Then two justified checkpoints in that range have slashable validators of both sets.

They hold at least `1/3 - SAFETY_DECAY/100` of the trusted stake. -/
theorem accountable_safety_of_weakSubjectivityPeriod_of_lt_electra {config : Config}
    {state : BeaconState preset fork} (before : fork < .pectra) {period total : UInt64} (periodOk : computeWeakSubjectivityPeriod config state = .ok period)
    (totalOk : getTotalActiveBalance state = .ok total)
    -- The trusted stake must be at least one increment, so that it is the total active balance.
    (large : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      stake (fun index => balanceAt state index.toNat)
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset)
    -- Assume each balance at most the largest effective balance.
    (capped : ∀ index, balanceAt state index ≤ preset.MAX_EFFECTIVE_BALANCE.toNat)
    -- That largest effective balance is a whole number `T` of ether.
    (wholeEther : preset.MAX_EFFECTIVE_BALANCE.toNat % ETH_TO_GWEI.toNat = 0)
    -- The rule counts `N` active validators of average balance `t` in ether, rounded down.
    {N t T : ℕ} (hN : N = (getActiveValidatorIndices state (getCurrentEpoch state)).length)
    -- The average balance `t` is in ether, rounded down.
    (ht : t = total.toNat / N / ETH_TO_GWEI.toNat)
    -- The largest balance `T` is in ether.
    (hT : T = preset.MAX_EFFECTIVE_BALANCE.toNat / ETH_TO_GWEI.toNat)
    -- Assume large balances, `230 T < 320 t`, where the rule takes its epochs for churn.
    --
    -- With large balances, the epochs that the rule gives for churn always fit the decayed margin.
    (largeBalances : 230 * T < 320 * t)
    {V : Models.Ffg.Checkpoint β → Finset ValidatorIndex} {genesis : β}
    {votes : Set (Vote ValidatorIndex β)} {c₁ c₂ : Models.Ffg.Checkpoint β}
    -- Take a finalized checkpoint.
    (h₁ : Finalized V (fun index => balanceAt state index.toNat) genesis votes c₁)
    -- Take a second finalized checkpoint.
    (h₂ : Finalized V (fun index => balanceAt state index.toNat) genesis votes c₂)
    -- The blocks of the two finalized checkpoints conflict.
    (hc : Conflicting c₁.block c₂.block)
    -- Take each justified checkpoint whose epoch lies between theirs.
    --
    -- At most the churn of validators per epoch of churn joined its set since the trusted set.
    --
    -- At most as many left it.
    --
    -- The epochs of churn leave out the withdrawal delay, as from Electra.
    --
    -- So the theorem assumes the sets gain and lose at most `delta` validators per epoch of churn.
    --
    -- With each stake at most `T`, that is a change of at most `3 delta T` for each epoch of churn.
    --
    -- The churn of later epochs can grow with the validators.
    --
    -- The assumption takes the churn at the checkpoint for every epoch of churn.
    (change : ∀ c : Models.Ffg.Checkpoint β, min c₁.epoch c₂.epoch ≤ c.epoch →
      c.epoch ≤ max c₁.epoch c₂.epoch →
      Justified V (fun index => balanceAt state index.toNat) genesis votes c →
      (V c \ (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset).card ≤
          (period.toNat - config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) *
            (getValidatorChurnLimit config state).toNat ∧
        ((getActiveValidatorIndices state (getCurrentEpoch state)).toFinset \ V c).card ≤
          (period.toNat - config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) *
            (getValidatorChurnLimit config state).toNat) :
    -- Then two justified checkpoints `l` and `r` lie in that range.
    --
    -- They have slashable validators of both of their sets.
    --
    -- Those validators hold at least `1/3 - SAFETY_DECAY/100` of the trusted stake.
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
  obtain ⟨total', totalOk', average, averageOk, _, _, epochs, epochsOk, periodOk⟩ :=
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
  rw [hNat, ht', hT'] at fit
  have fit := fit largeBalances averageLe
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
