module

public import EthLib.Consensus.Containers.State

/-!
# Proofs: the bounds under which a run of slots succeeds

The steps of a run of slots divide by constants of the preset.

The specification raises an error on a division by zero.

A division of 64-bit integers in Lean returns zero instead.

So with a zero divisor a step can succeed in Lean where the specification fails.

This file names the presets whose divisors are all positive, and shows that mainnet and minimal are.

It also names two sums of a state that the bounds of the steps use.

They are the sum of the effective balances and the sum of the recent slashed balances.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

/-- Each constant of a preset that a run of slots divides by is positive.

The run computes epochs from slots and effective balances in increments.

It also starts the periods of deposit votes, of history and of sync committees.

The base rewards divide by the quotient of the proposer reward.

The inactivity penalty divides by the quotient of its fork. -/
structure Preset.DivisorsPositive (preset : Preset) : Prop where
  slotsPerEpoch : preset.SLOTS_PER_EPOCH ≠ 0
  increment : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0
  hysteresis : preset.HYSTERESIS_QUOTIENT ≠ 0
  votingPeriod : preset.EPOCHS_PER_ETH1_VOTING_PERIOD ≠ 0
  historicalPeriod : preset.SLOTS_PER_HISTORICAL_ROOT / preset.SLOTS_PER_EPOCH ≠ 0
  syncPeriod : preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD ≠ 0
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

variable {preset : Preset} {fork : Base.Fork}

/-- The sum of the effective balances of the registry, on natural numbers. -/
def effectiveBalanceSum (state : BeaconState preset fork) : Nat :=
  (state.validators.data.toList.map (·.effectiveBalance.toNat)).sum

/-- The sum of the slashed balances of the recent epochs, on natural numbers. -/
def slashedBalanceSum (state : BeaconState preset fork) : Nat :=
  (state.slashings.elements.toList.map (·.toNat)).sum

end EthLib.Consensus
