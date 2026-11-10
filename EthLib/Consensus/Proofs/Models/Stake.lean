module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Stake

The consensus models weigh a set of validators by the sum of their stakes.

The stake of each validator is a natural number.

Along a sequence of sets, the stake that joins or leaves is at most the sum over the steps.

A bound on the Byzantine validators caps the fraction of the stake that they hold.
-/

@[expose] public section

namespace EthLib.Consensus.Models

variable {ν : Type*}

/-- The total stake of a set of validators. -/
def stake (w : ν → ℕ) (S : Finset ν) : ℕ :=
  ∑ v ∈ S, w v

variable {w : ν → ℕ}

@[simp]
theorem stake_empty : stake w ∅ = 0 :=
  Finset.sum_empty

/-- Two stake functions that agree on a set give it the same stake. -/
theorem stake_congr {w' : ν → ℕ} {S : Finset ν} (agree : ∀ v ∈ S, w v = w' v) :
    stake w S = stake w' S :=
  Finset.sum_congr rfl agree

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

/-- Two quorums up to slacks of two validator sets share stake, up to the change between the sets.

The quorum `A` holds two thirds of what is left of the stake of `L` once `a` is removed.

The quorum `B` holds the same share of the stake of `R` once `b` is removed.

The stake of `L \ V₀` and `V₀ \ R` measures that change against any reference set `V₀`.

The bound loses twice each slack.

With no slack, this is the bound in the proof of Gasper Theorem 8.3, times three. -/
theorem two_mul_stake_le_stake_inter_add_slack [DecidableEq ν] {L R A B : Finset ν}
    (V₀ : Finset ν) {a b : ℕ} (hA : A ⊆ L) (hB : B ⊆ R)
    (hA' : 2 * stake w L ≤ 3 * stake w A + 2 * a) (hB' : 2 * stake w R ≤ 3 * stake w B + 2 * b) :
    2 * stake w L ≤ 3 * stake w (A ∩ B) + stake w R +
      3 * (stake w (L \ V₀) + stake w (V₀ \ R)) + 2 * (a + b) := by
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

/-- Two quorums of two validator sets share stake, up to the change between the two sets.

The quorum `A` holds two thirds of the stake of `L`, and `B` two thirds of the stake of `R`.

The stake of `L \ V₀` and `V₀ \ R` measures that change against any reference set `V₀`.

This is the bound in the proof of Gasper Theorem 8.3, times three. -/
theorem two_mul_stake_le_stake_inter_add [DecidableEq ν] {L R A B : Finset ν} (V₀ : Finset ν)
    (hA : A ⊆ L) (hB : B ⊆ R) (hA' : 2 * stake w L ≤ 3 * stake w A)
    (hB' : 2 * stake w R ≤ 3 * stake w B) :
    2 * stake w L ≤
      3 * stake w (A ∩ B) + stake w R + 3 * (stake w (L \ V₀) + stake w (V₀ \ R)) := by
  simpa using two_mul_stake_le_stake_inter_add_slack (a := 0) (b := 0) V₀ hA hB
    (by simpa using hA') (by simpa using hB')

/-- Two sets of validators of `V`, each with two thirds of its stake, share one third of it. -/
theorem stake_inter [DecidableEq ν] {V A B : Finset ν} (hA : A ⊆ V) (hB : B ⊆ V)
    (hA' : 2 * stake w V ≤ 3 * stake w A) (hB' : 2 * stake w V ≤ 3 * stake w B) :
    stake w V ≤ 3 * stake w (A ∩ B) := by
  have h := two_mul_stake_le_stake_inter_add V hA hB hA' hB'
  simp only [Finset.sdiff_self, stake, Finset.sum_empty] at h
  simp only [stake]
  omega

/-- The Byzantine validators of `V` hold at most the fraction `num / den` of its stake.

The validators outside `J` are the Byzantine ones.

The denominator is positive.

The bound is not strict, as in Assumption 2 of the fast confirmation paper.

That assumption is in §3.2 of [arXiv 2405.00549v4](https://arxiv.org/abs/2405.00549v4).

It says nothing when the fraction is at least one, or when `V` has no stake. -/
def ByzantineStakeAtMost (w : ν → ℕ) (V : Finset ν) (J : Set ν) [DecidablePred (· ∈ J)]
    (num den : ℕ) : Prop :=
  0 < den ∧ den * stake w {v ∈ V | v ∉ J} ≤ num * stake w V

namespace ByzantineStakeAtMost

variable {V : Finset ν} {J : Set ν} [DecidablePred (· ∈ J)] {num den : ℕ}

/-- The honest validators of `V` then hold at least the fraction `1 - num / den` of its stake. -/
theorem honest (bound : ByzantineStakeAtMost w V J num den) :
    (den - num) * stake w V ≤ den * stake w {v ∈ V | v ∈ J} := by
  have split : stake w {v ∈ V | v ∈ J} + stake w {v ∈ V | v ∉ J} = stake w V :=
    Finset.sum_filter_add_sum_filter_not V (· ∈ J) w
  have bound := bound.2
  have scaled :
      den * stake w V = den * stake w {v ∈ V | v ∈ J} + den * stake w {v ∈ V | v ∉ J} := by
    rw [← split, Nat.mul_add]
  rw [Nat.sub_mul]
  omega

/-- The bound holds for every fraction when every validator of `V` is honest. -/
theorem of_subset (num : ℕ) (positive : 0 < den) (all : ↑V ⊆ J) :
    ByzantineStakeAtMost w V J num den := by
  have : ({v ∈ V | v ∉ J} : Finset ν) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun v member => not_not.mpr (all member)
  simp [ByzantineStakeAtMost, this, stake, positive]

/-- The bound fails below one when every validator is Byzantine and `V` has stake. -/
theorem not_of_empty (below : num < den) (positive : 0 < stake w V) :
    ¬ByzantineStakeAtMost w V ∅ num den := by
  intro bound
  simp only [ByzantineStakeAtMost, Set.mem_empty_iff_false, not_false_eq_true,
    Finset.filter_true] at bound
  have := bound.2
  have := Nat.mul_lt_mul_of_pos_right below positive
  omega

end ByzantineStakeAtMost

end EthLib.Consensus.Models
