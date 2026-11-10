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
  obtain ⟨-, -, totalEq⟩ := getTotalBalance_ok_iff_stake.mp totalOk
  rw [Nat.max_eq_right large] at totalEq
  rw [← totalEq] at bound ⊢
  exact safetyMargin_of_balanceChurnPeriod_eq_ok periodOk bound

end EthLib.Consensus
