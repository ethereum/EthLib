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

theorem stake_union_le [DecidableEq ν] (S T : Finset ν) :
    stake w (S ∪ T) ≤ stake w S + stake w T := by
  have hsum : stake w (S ∪ T) + stake w (S ∩ T) = stake w S + stake w T :=
    Finset.sum_union_inter
  omega

/-- Two quorums of two validator sets share stake, up to the change between the two sets.

The quorum `A` holds two thirds of the stake of `L`, and `B` two thirds of the stake of `R`.

The stake of `L \ V₀` and `V₀ \ R` measures that change against any reference set `V₀`.

This is the bound in the proof of Gasper Theorem 8.3, times three. -/
theorem two_mul_stake_le_stake_inter_add [DecidableEq ν] {L R A B : Finset ν} (V₀ : Finset ν)
    (hA : A ⊆ L) (hB : B ⊆ R) (hA' : 2 * stake w L ≤ 3 * stake w A)
    (hB' : 2 * stake w R ≤ 3 * stake w B) :
    2 * stake w L ≤
      3 * stake w (A ∩ B) + stake w R + 3 * (stake w (L \ V₀) + stake w (V₀ \ R)) := by
  have hsum : stake w (A ∪ B) + stake w (A ∩ B) = stake w A + stake w B :=
    Finset.sum_union_inter
  -- A validator of `L` outside `R` either joined after `V₀` or left `V₀` before `R`.
  have hsub : A ∪ B ⊆ (R ∪ L \ V₀) ∪ V₀ \ R := by
    intro v hv
    simp only [Finset.mem_union, Finset.mem_sdiff] at hv ⊢
    rcases hv with hv | hv
    · have := hA hv
      by_cases hR : v ∈ R <;> by_cases h₀ : v ∈ V₀ <;> tauto
    · exact .inl (.inl (hB hv))
  have hle := (stake_mono (w := w) hsub).trans
    ((stake_union_le _ _).trans (Nat.add_le_add_right (stake_union_le _ _) _))
  omega

/-- Two sets of validators of `V`, each with two thirds of its stake, share one third of it. -/
theorem stake_inter [DecidableEq ν] {V A B : Finset ν} (hA : A ⊆ V) (hB : B ⊆ V)
    (hA' : 2 * stake w V ≤ 3 * stake w A) (hB' : 2 * stake w V ≤ 3 * stake w B) :
    stake w V ≤ 3 * stake w (A ∩ B) := by
  have h := two_mul_stake_le_stake_inter_add V hA hB hA' hB'
  simp only [Finset.sdiff_self, stake, Finset.sum_empty] at h
  simp only [stake]
  omega

end EthLib.Consensus.Models
