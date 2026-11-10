module

public import EthLib.Base.Proofs.List
public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.Config
public import EthLib.Consensus.Proofs.Accessors

/-!
# Proofs: the bounds under which a run of slots succeeds

The steps of a run of slots divide by constants of the preset and of the configuration.

The specification raises an error on a division by zero and on a remainder by zero.

In Lean a division of 64-bit integers by zero returns zero, and a remainder returns the dividend.

So with a zero divisor a step can succeed in Lean where the specification fails.

A checked division fails on zero in both, but a proof that the step succeeds then needs it positive.

This file names the presets and the configurations whose divisors are all positive.

It shows that mainnet and minimal are such presets and such configurations.

The lengths of the circular buffers are not listed: a read or a write fails on a zero length.

The proofs take them as separate hypotheses.

The file also names two sums of a state that the bounds of the steps use.

They are the sum of the effective balances and the sum of the recent slashed balances.

It shows that a checked sum of a list and the total active balance succeed under such bounds.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

/-- Each constant of a preset that a run of slots divides by is positive.

The run computes epochs from slots, and effective balances in increments.

The update of an effective balance divides the increment by the hysteresis quotient.

The run also starts the periods of deposit votes, of history and of sync committees.

The size of a committee divides the active validators of a slot.

The base rewards divide by the quotient of the proposer reward.

The inactivity penalty divides by the quotient of its fork.

From Altair that division is checked, so the specification and Lean agree there.

A proof that the penalty succeeds still needs the quotient positive. -/
structure Preset.DivisorsPositive (preset : Preset) : Prop where
  slotsPerEpoch : preset.SLOTS_PER_EPOCH ≠ 0
  increment : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0
  hysteresis : preset.HYSTERESIS_QUOTIENT ≠ 0
  votingPeriod : preset.EPOCHS_PER_ETH1_VOTING_PERIOD ≠ 0
  historicalPeriod : preset.SLOTS_PER_HISTORICAL_ROOT / preset.SLOTS_PER_EPOCH ≠ 0
  syncPeriod : preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD ≠ 0
  committeeSize : preset.TARGET_COMMITTEE_SIZE ≠ 0
  proposerReward : preset.PROPOSER_REWARD_QUOTIENT ≠ 0
  inactivityPenalty : preset.INACTIVITY_PENALTY_QUOTIENT ≠ 0
  inactivityPenaltyAltair : preset.INACTIVITY_PENALTY_QUOTIENT_ALTAIR ≠ 0
  inactivityPenaltyBellatrix : preset.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX ≠ 0

/-- Each divisor of the mainnet preset is positive. -/
theorem Preset.divisorsPositive_mainnet : Preset.mainnet.DivisorsPositive := by
  constructor <;> decide

/-- Each divisor of the minimal preset is positive. -/
theorem Preset.divisorsPositive_minimal : Preset.minimal.DivisorsPositive := by
  constructor <;> decide

/-- Each constant of a configuration that a run of slots divides by is positive.

The limits of churn divide the active validators or the active balance by a quotient.

From Gloas the churn has its own quotient, and the consolidations have one from Electra.

The inactivity penalty divides by the score bias times a quotient, with a check. -/
structure Config.DivisorsPositive (config : Config) : Prop where
  churn : config.CHURN_LIMIT_QUOTIENT ≠ 0
  churnGloas : config.CHURN_LIMIT_QUOTIENT_GLOAS ≠ 0
  consolidationChurn : config.CONSOLIDATION_CHURN_LIMIT_QUOTIENT ≠ 0
  scoreBias : config.INACTIVITY_SCORE_BIAS ≠ 0

/-- Each divisor of the mainnet configuration is positive. -/
theorem Config.divisorsPositive_mainnet : Config.mainnet.DivisorsPositive := by
  constructor <;> decide

/-- Each divisor of the minimal configuration is positive. -/
theorem Config.divisorsPositive_minimal : Config.minimal.DivisorsPositive := by
  constructor <;> decide

/-- A fold of checked sums succeeds when the start and the list sum below 2^64.

It returns the sum on natural numbers. -/
theorem foldlM_addChecked_exists_ok (list : List UInt64) (start : UInt64)
    (fits : start.toNat + (list.map (·.toNat)).sum < 2 ^ 64) :
    ∃ sum, list.foldlM addChecked start = .ok sum ∧
      sum.toNat = start.toNat + (list.map (·.toNat)).sum := by
  induction list generalizing start with
  | nil => exact ⟨start, rfl, by simp⟩
  | cons head tail ih =>
    simp only [List.map_cons, List.sum_cons] at fits ⊢
    have step := addChecked_of_lt (a := start) (b := head) (by omega)
    obtain ⟨sum, computed, value⟩ := ih (start + head) (by rw [toNat_add_of_lt (by omega)]; omega)
    exact ⟨sum, by rw [List.foldlM_cons, step]; exact computed,
      by rw [value, toNat_add_of_lt (by omega)]; omega⟩


variable {preset : Preset} {fork : Base.Fork}

/-- The sum of the effective balances of the registry, on natural numbers. -/
def effectiveBalanceSum (state : BeaconState preset fork) : Nat :=
  (state.validators.data.toList.map (·.effectiveBalance.toNat)).sum

/-- The sum of the slashed balances of the recent epochs, on natural numbers. -/
def slashedBalanceSum (state : BeaconState preset fork) : Nat :=
  (state.slashings.elements.toList.map (·.toNat)).sum

/-- The marked sum of the effective balances is at most the sum of all of them. -/
private theorem sumMarked_le_effectiveBalanceSum {state : BeaconState preset fork}
    (marks : Array Bool) :
    sumMarked state.validators.data marks ≤ effectiveBalanceSum state := by
  rw [sumMarked_eq_sum]
  have : effectiveBalanceSum state = ((List.range state.validators.data.size).map fun j =>
      ((state.validators.data[j]?).map (·.effectiveBalance.toNat)).getD 0).sum := by
    unfold effectiveBalanceSum
    congr 1
    apply List.ext_getElem
    · simp
    · intro i first second
      simp [Array.getElem?_eq_getElem (by simpa using first)]
  rw [this]
  refine sum_map_le_sum_map fun j _ => ?_
  split <;> omega

/-- The total active balance succeeds when the sum of the effective balances is below 2^64.

The registry must stay within its limit.

The total is then one increment, or at least one increment and at most that sum. -/
theorem getTotalActiveBalance_exists_ok {state : BeaconState preset fork}
    (within : state.RegistryWithinLimit) (summed : effectiveBalanceSum state < 2 ^ 64) :
    ∃ total, getTotalActiveBalance state = .ok total ∧
      preset.EFFECTIVE_BALANCE_INCREMENT ≤ total ∧
      (total = preset.EFFECTIVE_BALANCE_INCREMENT ∨ total.toNat ≤ effectiveBalanceSum state) := by
  have inside : ∀ i ∈ getActiveValidatorIndices state (getCurrentEpoch state),
      i.toNat < state.validators.data.size := by
    intro i member
    obtain ⟨_, found, -⟩ := (mem_getActiveValidatorIndices within).mp member
    exact (Array.getElem?_eq_some_iff.mp found).1
  have lt := Nat.lt_of_le_of_lt (sumMarked_le_effectiveBalanceSum (state := state)
    (markIndices state.validators.data.size
      (getActiveValidatorIndices state (getCurrentEpoch state)))) summed
  have ok : getTotalActiveBalance state = .ok (max preset.EFFECTIVE_BALANCE_INCREMENT
      (sumMarked state.validators.data (markIndices state.validators.data.size
        (getActiveValidatorIndices state (getCurrentEpoch state)))).toUInt64) :=
    getTotalBalance_ok_iff.mpr ⟨inside, lt, rfl⟩
  refine ⟨_, ok, le_getTotalBalance ok, ?_⟩
  rw [UInt64.max_def]
  split
  · right
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt lt]
    exact sumMarked_le_effectiveBalanceSum _
  · exact .inl rfl

end EthLib.Consensus
