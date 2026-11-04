module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Stake

The consensus models weigh a set of validators by the sum of their stakes.

The stake of each validator is a natural number.
-/

@[expose] public section

namespace EthLib.Consensus.Models

variable {ν : Type*}

/-- The total stake of a set of validators. -/
def stake (w : ν → ℕ) (S : Finset ν) : ℕ :=
  ∑ v ∈ S, w v

variable {w : ν → ℕ}

theorem stake_mono {S T : Finset ν} (h : S ⊆ T) : stake w S ≤ stake w T :=
  Finset.sum_le_sum_of_subset h

/-- Two sets of validators of `V`, each with two thirds of its stake, share one third of it. -/
theorem stake_inter [DecidableEq ν] {V A B : Finset ν} (hA : A ⊆ V) (hB : B ⊆ V)
    (hA' : 2 * stake w V ≤ 3 * stake w A) (hB' : 2 * stake w V ≤ 3 * stake w B) :
    stake w V ≤ 3 * stake w (A ∩ B) := by
  have hsum : stake w (A ∪ B) + stake w (A ∩ B) = stake w A + stake w B :=
    Finset.sum_union_inter
  have hle : stake w (A ∪ B) ≤ stake w V := stake_mono (Finset.union_subset hA hB)
  omega

end EthLib.Consensus.Models
