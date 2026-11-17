module

public import EthLib.Consensus.Proofs.Transition.ValidatorStep
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The balance reserved for an activation

A validator not yet activated keeps a balance that funds its effective balance.

Before Electra, a scheduled validator keeps the largest effective balance until it activates.

Along a run from genesis before Gloas, every step keeps both facts.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Internal

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- Assignment charges and remaining unassigned resources share one deposit-capacity ledger.

The pending-deposit and block-carry laws are discharged by the funding layer.
-/
theorem Run.unassigned_assignment_resources_of_pending_law {g x u : ForkedBeaconState preset}
    (shared : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g)
    (head : Run config checks x u)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (aligned : MaxEffectiveBalancesAligned preset)
    (electra : .pectra ≤ x.fork) (early : u.fork < .glamsterdam)
    (pendingLaw : ∀ {f : Fork} (a b : BeaconState preset f) (e : .pectra ≤ f),
      f < .glamsterdam → processPendingDeposits config checks a e = .ok b → BalancesMatch a →
      (∑ i ∈ Finset.range b.validators.data.size,
        if (a.validators.data[i]?.map (fun v =>
          decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch a).toNat))).getD false then 0
        else ((b.balances.data[i]?.map UInt64.toNat).getD 0) -
          ((a.balances.data[i]?.map UInt64.toNat).getD 0)) +
        (b.depositBalanceToConsume e).toNat ≤ (a.depositBalanceToConsume e).toNat +
          config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat)
    (blockLaw : ∀ {f : Fork} (a b : BeaconState preset f)
      (engine : ExecutionEngine preset f) (block : BeaconBlock preset f),
      f < .glamsterdam → processBlock config checks engine a block = .ok b →
      b.depositBalanceToConsume = a.depositBalanceToConsume) :
    let candidate := fun i : Nat =>
      (x.state.validators.data[i]?.map (·.activationEpoch)).getD FAR_FUTURE_EPOCH =
        FAR_FUTURE_EPOCH
    let assigned := fun i : Nat =>
      (u.state.validators.data[i]?.map (·.activationEpoch)).getD FAR_FUTURE_EPOCH ≠
        FAR_FUTURE_EPOCH
    let value := fun (s : ForkedBeaconState preset) (i : Nat) =>
      ((s.state.validators.data[i]?).map fun v =>
        max v.effectiveBalance.toNat
          (min ((s.state.balances.data[i]?.map UInt64.toNat).getD 0)
            (withdrawalMaxEffectiveBalance preset s.fork v).toNat)).getD 0
    preset.MAX_EFFECTIVE_BALANCE.toNat *
        ((Finset.range u.state.validators.data.size).filter fun i =>
          candidate i ∧ assigned i).card +
      (∑ i ∈ Finset.range u.state.validators.data.size,
        if candidate i ∧ ¬ assigned i then value u i else 0) +
      ((if h : .pectra ≤ u.fork then
        (u.state.depositBalanceToConsume h).toNat else 0) : Nat) ≤
      (∑ i ∈ Finset.range x.state.validators.data.size,
        if candidate i then value x i else 0) +
      (x.state.depositBalanceToConsume electra).toNat +
      config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat *
        ((getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat + 1) := by
  classical
  dsimp only
  let candidate := fun i : Nat => decide
    ((x.state.validators.data[i]?.map (·.activationEpoch)).getD FAR_FUTURE_EPOCH =
      FAR_FUTURE_EPOCH)
  have bound := preKeyCharge_run shared genesis head activation compounding aligned electra
    early candidate pendingLaw blockLaw
  have initial : (∑ i ∈ Finset.range x.state.validators.data.size,
      preKeyCharge candidate x.state i) =
      ∑ i ∈ Finset.range x.state.validators.data.size,
        if (x.state.validators.data[i]?.map (·.activationEpoch)).getD FAR_FUTURE_EPOCH =
            FAR_FUTURE_EPOCH then
          ((x.state.validators.data[i]?).map fun v => max v.effectiveBalance.toNat
            (min ((x.state.balances.data[i]?.map UInt64.toNat).getD 0)
              (withdrawalMaxEffectiveBalance preset x.fork v).toNat)).getD 0
        else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    cases found : x.state.validators.data[i]? with
    | none => simp [preKeyCharge, candidate, found]
    | some v => simp [preKeyCharge, candidate, found]; split <;> simp_all
  rw [initial] at bound
  have final : (∑ i ∈ Finset.range u.state.validators.data.size,
      preKeyCharge candidate u.state i) =
      preset.MAX_EFFECTIVE_BALANCE.toNat *
        ((Finset.range u.state.validators.data.size).filter fun i =>
          candidate i = true ∧
            (u.state.validators.data[i]?.map (·.activationEpoch)).getD FAR_FUTURE_EPOCH ≠
              FAR_FUTURE_EPOCH).card +
      ∑ i ∈ Finset.range u.state.validators.data.size,
        if candidate i = true ∧
            (u.state.validators.data[i]?.map (·.activationEpoch)).getD FAR_FUTURE_EPOCH =
              FAR_FUTURE_EPOCH then
          ((u.state.validators.data[i]?).map fun v => max v.effectiveBalance.toNat
            (min ((u.state.balances.data[i]?.map UInt64.toNat).getD 0)
              (withdrawalMaxEffectiveBalance preset u.fork v).toNat)).getD 0
        else 0 := by
    rw [Nat.mul_comm preset.MAX_EFFECTIVE_BALANCE.toNat,
      ← Finset.sum_const_nat (f := fun _ : Nat => preset.MAX_EFFECTIVE_BALANCE.toNat)
        (by intros; rfl),
      Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases found : u.state.validators.data[i]? with
    | none => simp [preKeyCharge, found]
    | some v =>
      by_cases chosen : candidate i = true <;>
        by_cases pending : v.activationEpoch = FAR_FUTURE_EPOCH <;>
        simp [preKeyCharge, found, chosen, pending]
  rw [final] at bound
  simp only [candidate, decide_eq_true_eq] at bound
  simpa only [not_not] using bound.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_left _ (Nat.le_succ _)) _)

/-- Before Electra, each scheduled key retains at least one activation reserve. -/
theorem Run.scheduled_activation_reserve {g x : ForkedBeaconState preset}
    (run : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (aligned : MaxEffectiveBalancesAligned preset) (early : x.fork < .pectra)
    (i : Nat) (v : Validator) (found : x.state.validators.data[i]? = some v)
    (future : getCurrentEpoch x.state < v.activationEpoch)
    (assigned : v.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    preset.MAX_EFFECTIVE_BALANCE ≤ v.effectiveBalance := by
  have epochFinite : getCurrentEpoch x.state < FAR_FUTURE_EPOCH := by
    have lower := UInt64.lt_iff_toNat_lt.mp future
    have upper := v.activationEpoch.toNat_lt
    have different := mt UInt64.toNat_inj.mp assigned
    rw [UInt64.lt_iff_toNat_lt]
    change _ < 18446744073709551615
    change v.activationEpoch.toNat ≠ 18446744073709551615 at different
    omega
  have reserve := (run_scheduled_reserve run genesis activation compounding aligned
    (Nat.lt_trans early (by decide)) epochFinite) early i v found
      (UInt64.lt_iff_toNat_lt.mp future) assigned
  exact reserve.1

end EthLib.Consensus
