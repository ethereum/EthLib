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
  rw [← first, List.range_add, List.map_append, List.sum_append, List.map_map]
  refine Nat.add_le_add_left ((sum_map_le (high := preset.largestEffectiveBalance)
    fun i inside => ?_).trans_eq (by rw [List.length_range])) _
  have size : state.validators.data.size + i < after.validators.data.size := by
    have := List.mem_range.mp inside
    omega
  simp only [Function.comp_apply, Array.getElem?_eq_getElem size, Option.map_some,
    Option.getD_some]
  exact (UInt64.le_iff_toNat_le.mp (cap _ (Array.getElem_mem size))).trans
    (withdrawalMaxEffectiveBalance_le_largestEffectiveBalance preset fork _)

end EthLib.Consensus
