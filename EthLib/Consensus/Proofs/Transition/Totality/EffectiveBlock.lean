module

public import EthLib.Consensus.Proofs.Transition.Totality.Rewards

import EthLib.Consensus.Proofs.Transition.BalanceDrift
import EthLib.Consensus.Proofs.Transition.ValidatorCaps
import EthLib.Consensus.Proofs.Transition.Invariants

/-!
# Proofs: a block raises the effective balances only through new validators

A block keeps the effective balance of each validator that was there before it.

Each new validator starts with an effective balance within its cap.

So a block raises the sum of the effective balances by at most the largest cap per new validator.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks} {fork : Fork}

private theorem sum_range_le (f : Nat → Nat) (n C : Nat) :
    ∀ k, (∀ j, n ≤ j → j < n + k → f j ≤ C) →
      ((List.range (n + k)).map f).sum ≤ ((List.range n).map f).sum + k * C := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro h
    have := ih fun j a b => h j a (by omega)
    have last := h (n + k) (by omega) (by omega)
    rw [← Nat.add_assoc, List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [Nat.succ_mul]
    omega

/-- A block raises the sum of the effective balances by at most the largest cap per new validator.

The effective balances before it must be within their caps.

The activation balance must be at most the cap of compounding credentials. -/
theorem processBlock_effectiveBalanceSum_le {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (capped : EffectiveBalancesCapped state)
    (computed : processBlock config checks engine state block = .ok after) :
    effectiveBalanceSum after ≤ effectiveBalanceSum state +
      (after.validators.data.size - state.validators.data.size) *
        preset.largestEffectiveBalance := by
  have kept := effectiveKept_processBlock (config := config) (checks := checks) computed
  have cap := processBlock_capped compounding computed capped
  have grows := (frame_processBlock computed).registryGrows
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le grows
  rw [effectiveBalanceSum_eq_sum_range after, effectiveBalanceSum_eq_sum_range state, hk,
    Nat.add_sub_cancel_left]
  have first : ((List.range state.validators.data.size).map fun j =>
      ((after.validators.data[j]?).map (·.effectiveBalance.toNat)).getD 0).sum =
      ((List.range state.validators.data.size).map fun j =>
      ((state.validators.data[j]?).map (·.effectiveBalance.toNat)).getD 0).sum := by
    congr 1
    apply List.map_congr_left
    intro j hj
    exact kept j (List.mem_range.mp hj)
  rw [← first]
  apply sum_range_le
  intro j _ inside
  have size : j < after.validators.data.size := by omega
  rw [Array.getElem?_eq_getElem size]
  have := cap _ (Array.getElem_mem size)
  have h2 := withdrawalMaxEffectiveBalance_le_largestEffectiveBalance preset fork
    after.validators.data[j]
  simp only [Option.map_some, Option.getD_some]
  exact Nat.le_trans (UInt64.le_iff_toNat_le.mp this) h2

end EthLib.Consensus
