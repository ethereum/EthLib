module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Stake

The consensus models weigh a set of validators by the sum of their stakes.

The stake of each validator is a natural number.

Along a sequence of sets, the stake that joins or leaves is at most the sum over the steps.
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

/-- A set and what it lacks of another weigh as much as the other and what it lacks of the set. -/
theorem stake_add_stake_sdiff [DecidableEq ν] (s t : Finset ν) :
    stake w s + stake w (t \ s) = stake w t + stake w (s \ t) := by
  -- Both sides weigh the union of the two sets.
  have hs : stake w (s ∪ t) = stake w s + stake w (t \ s) := by
    rw [← Finset.union_sdiff_self_eq_union]
    exact Finset.sum_union Finset.disjoint_sdiff
  have ht : stake w (s ∪ t) = stake w t + stake w (s \ t) := by
    rw [Finset.union_comm, ← Finset.union_sdiff_self_eq_union]
    exact Finset.sum_union Finset.disjoint_sdiff
  rw [← hs, ht]

/-- Along a sequence of sets, the change since the first set is at most the change of each step.

The change counts the stake that joins once and the stake that leaves twice.

A member of the last set outside the first joined at some step.

A member of the first set outside the last left at some step. -/
theorem stake_sdiff_add_two_mul_le [DecidableEq ν] (S : ℕ → Finset ν) {d : ℕ} :
    ∀ {n : ℕ}, (∀ i < n, stake w (S (i + 1) \ S i) + 2 * stake w (S i \ S (i + 1)) ≤ d) →
      stake w (S n \ S 0) + 2 * stake w (S 0 \ S n) ≤ n * d
  | 0, _ => by simp [stake]
  | n + 1, h => by
    have before := stake_sdiff_add_two_mul_le (n := n) S fun i hi => h i (by omega)
    have last := h n (by omega)
    have joined := (stake_mono (w := w) (sdiff_triangle (S (n + 1)) (S n) (S 0))).trans
      (stake_union_le _ _)
    have left := (stake_mono (w := w) (sdiff_triangle (S 0) (S n) (S (n + 1)))).trans
      (stake_union_le _ _)
    have : (n + 1) * d = n * d + d := Nat.succ_mul n d
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
