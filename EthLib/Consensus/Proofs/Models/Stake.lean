module

import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Stake

The consensus models weigh a set of validators by the sum of their stakes.

The stake of each validator is a natural number.

Along a sequence of sets, the stake that joins or leaves is at most the sum over the steps.

A quorum under one stake function stays a quorum under another, up to the change between them.

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

/-- The change from weights `w₀` to weights `w` on a set.

It counts the weight that the validators of the set gain once and the weight they lose twice.

It is zero when the two weights agree on the set. -/
def weightChange (w₀ w : ν → ℕ) (S : Finset ν) : ℕ :=
  stake (fun v => w v - w₀ v) S + 2 * stake (fun v => w₀ v - w v) S

theorem weightChange_eq_zero {w₀ : ν → ℕ} {S : Finset ν} (agree : ∀ v ∈ S, w₀ v = w v) :
    weightChange w₀ w S = 0 := by
  have gain : stake (fun v => w v - w₀ v) S = 0 :=
    Finset.sum_eq_zero fun v member => by rw [agree v member, Nat.sub_self]
  have loss : stake (fun v => w₀ v - w v) S = 0 :=
    Finset.sum_eq_zero fun v member => by rw [agree v member, Nat.sub_self]
  simp [weightChange, gain, loss]

@[simp]
theorem weightChange_self (S : Finset ν) : weightChange w w S = 0 :=
  weightChange_eq_zero fun _ _ => rfl

/-- A quorum under weights `w` is a quorum under weights `w₀`, up to the change of the weights.

The quorum `A` of `L` holds two thirds of the stake of `L` under `w`, up to a slack `a`.

Under `w₀` the slack grows by the change from `w₀` to `w` on `L`.

A gain counts once and a loss twice, as for a validator that joins or leaves the set.

The bound overcounts: it also charges the loss of a member of the quorum. -/
theorem two_mul_stake_le_add_weightChange {w₀ : ν → ℕ} {L A : Finset ν} {a : ℕ} (hA : A ⊆ L)
    (h : 2 * stake w L ≤ 3 * stake w A + a) :
    2 * stake w₀ L ≤ 3 * stake w₀ A + weightChange w₀ w L + a := by
  -- Pointwise, `w + (w₀ - w) = w₀ + (w - w₀)` and `w ≤ w₀ + (w - w₀)`.
  have hL : stake w L + stake (fun v => w₀ v - w v) L =
      stake w₀ L + stake (fun v => w v - w₀ v) L := by
    simp only [stake, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by omega
  have hA' : stake w A ≤ stake w₀ A + stake (fun v => w v - w₀ v) A := by
    simp only [stake, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun v _ => by omega
  have hgain := stake_mono (w := fun v => w v - w₀ v) hA
  unfold weightChange
  omega

/-- Two quorums up to slacks of two validator sets share stake, up to the change between the sets.

The quorum `A` holds two thirds of the stake of `L`, up to a slack `a`.

The quorum `B` holds the same share of the stake of `R`, up to a slack `b`.

The stake of `L \ V₀` and `V₀ \ R` measures that change against any reference set `V₀`.

The bound loses each slack once.

With no slack, this is the bound in the proof of Gasper Theorem 8.3, times three. -/
theorem two_mul_stake_le_stake_inter_add_slack [DecidableEq ν] {L R A B : Finset ν}
    (V₀ : Finset ν) {a b : ℕ} (hA : A ⊆ L) (hB : B ⊆ R)
    (hA' : 2 * stake w L ≤ 3 * stake w A + a) (hB' : 2 * stake w R ≤ 3 * stake w B + b) :
    2 * stake w L ≤ 3 * stake w (A ∩ B) + stake w R +
      3 * (stake w (L \ V₀) + stake w (V₀ \ R)) + (a + b) := by
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
  simpa using two_mul_stake_le_stake_inter_add_slack (a := 0) (b := 0) V₀ hA hB hA' hB'

/-- Two sets of validators of `V`, each with two thirds of its stake, share one third of it. -/
theorem stake_inter [DecidableEq ν] {V A B : Finset ν} (hA : A ⊆ V) (hB : B ⊆ V)
    (hA' : 2 * stake w V ≤ 3 * stake w A) (hB' : 2 * stake w V ≤ 3 * stake w B) :
    stake w V ≤ 3 * stake w (A ∩ B) := by
  have h := two_mul_stake_le_stake_inter_add V hA hB hA' hB'
  simp only [Finset.sdiff_self, stake, Finset.sum_empty] at h
  simp only [stake]
  omega

/-- The weight `w v` inside `S`, and zero outside it. -/
def supported [DecidableEq ν] (S : Finset ν) (w : ν → ℕ) (v : ν) : ℕ :=
  if v ∈ S then w v else 0

private theorem sum_supported [DecidableEq ν] (S U : Finset ν) (w : ν → ℕ)
    (inside : S ⊆ U) : (∑ v ∈ U, supported S w v) = stake w S := by
  unfold stake
  rw [← Finset.sum_subset inside]
  · exact Finset.sum_congr rfl (fun v hv => by simp [supported, hv])
  · intro v _ hv
    simp [supported, hv]

/-- Transfer two quorums together, excluding accountable validators from the weight loss.

Gains cost once, losses twice, and support outside each active denominator costs twice.

Bounding each quorum on its own would also charge the losses of accountable keys. -/
theorem stake_le_accountable_add_change [DecidableEq ν]
    (reference active₁ active₂ s₁ s₂ q₁ q₂ accountable : Finset ν)
    (old w₁ w₂ : ν → ℕ) (loss₁ loss₂ gain₁ gain₂ outside₁ outside₂ : ℕ)
    (activeInside₁ : active₁ ⊆ s₁) (activeInside₂ : active₂ ⊆ s₂)
    (votersInside₁ : q₁ ⊆ s₁) (votersInside₂ : q₂ ⊆ s₂)
    (quorum₁ : 2 * stake w₁ active₁ ≤ 3 * stake w₁ q₁)
    (quorum₂ : 2 * stake w₂ active₂ ≤ 3 * stake w₂ q₂)
    (overlap : q₁ ∩ q₂ ⊆ accountable)
    (lossOne : (∑ k ∈ reference \ accountable, (old k - supported s₁ w₁ k)) ≤ loss₁)
    (lossTwo : (∑ k ∈ reference \ accountable, (old k - supported s₂ w₂ k)) ≤ loss₂)
    (gainOne : (∑ k ∈ s₁, (w₁ k - supported reference old k)) ≤ gain₁)
    (gainTwo : (∑ k ∈ s₂, (w₂ k - supported reference old k)) ≤ gain₂)
    (outsideOne : stake w₁ (s₁ \ active₁) ≤ outside₁)
    (outsideTwo : stake w₂ (s₂ \ active₂) ≤ outside₂) :
    stake old reference ≤ 3 * stake old (reference ∩ accountable) +
      2 * (loss₁ + loss₂) + (gain₁ + gain₂) + 2 * (outside₁ + outside₂) := by
  let u := reference ∪ s₁ ∪ s₂
  have refU : reference ⊆ u := by intro k hk; simp [u, hk]
  have oneU : s₁ ⊆ u := by intro k hk; simp [u, hk]
  have twoU : s₂ ⊆ u := by intro k hk; simp [u, hk]
  -- Factor the voter and denominator memberships out of the reference-weight arithmetic.
  have voter_le (q s : Finset ν) (w : ν → ℕ) (inside : q ⊆ s) (k : ν) :
      supported q w k ≤ supported s w k := by
    by_cases h : k ∈ q
    · simp [supported, h, inside h]
    · simp [supported, h]
  have sub_supported (s t : Finset ν) (w v : ν → ℕ) (k : ν) :
      supported s (fun k => w k - supported t v k) k =
        supported s w k - supported t v k := by
    by_cases h : k ∈ s <;> simp [supported, h]
  have localBound : ∀ k, supported reference old k +
      3 * supported q₁ w₁ k + 3 * supported q₂ w₂ k ≤
      3 * supported (reference ∩ accountable) old k +
        2 * supported (reference \ accountable) (fun k => old k - supported s₁ w₁ k) k +
        2 * supported (reference \ accountable) (fun k => old k - supported s₂ w₂ k) k +
        supported s₁ (fun k => w₁ k - supported reference old k) k +
        supported s₂ (fun k => w₂ k - supported reference old k) k +
        2 * supported s₁ w₁ k + 2 * supported s₂ w₂ k := by
    intro k
    have le₁ := voter_le q₁ s₁ w₁ votersInside₁ k
    have le₂ := voter_le q₂ s₂ w₂ votersInside₂ k
    have exclusive : k ∉ accountable →
        supported q₁ w₁ k + supported q₂ w₂ k ≤
          max (supported s₁ w₁ k) (supported s₂ w₂ k) := by
      intro notBad
      have disjoint : ¬(k ∈ q₁ ∧ k ∈ q₂) := fun h =>
        notBad (overlap (Finset.mem_inter.mpr h))
      by_cases h₁ : k ∈ q₁
      · have h₂ : k ∉ q₂ := fun h => disjoint ⟨h₁, h⟩
        simpa only [supported, h₂, ↓reduceIte, Nat.add_zero] using
          le₁.trans (le_max_left _ _)
      · simpa only [supported, h₁, ↓reduceIte, Nat.zero_add] using
          le₂.trans (le_max_right _ _)
    rw [sub_supported s₁ reference, sub_supported s₂ reference]
    by_cases hb : k ∈ accountable
    · by_cases hr : k ∈ reference <;>
        simp only [supported, Finset.mem_inter, Finset.mem_sdiff, hb, hr,
          and_true, not_true_eq_false, and_false, ↓reduceIte]
          at le₁ le₂ ⊢ <;> omega
    · have bound := exclusive hb
      by_cases hr : k ∈ reference <;>
        simp only [supported, Finset.mem_inter, Finset.mem_sdiff, hb, hr,
          and_false, not_false_eq_true, and_true, ↓reduceIte]
          at bound ⊢ <;> omega
  have total := Finset.sum_le_sum (s := u) (fun k _ => localBound k)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at total
  rw [sum_supported reference u old refU,
    sum_supported q₁ u w₁ (votersInside₁.trans oneU),
    sum_supported q₂ u w₂ (votersInside₂.trans twoU),
    sum_supported (reference ∩ accountable) u old (Finset.inter_subset_left.trans refU),
    sum_supported (reference \ accountable) u _ (Finset.sdiff_subset.trans refU),
    sum_supported (reference \ accountable) u _ (Finset.sdiff_subset.trans refU),
    sum_supported s₁ u _ oneU, sum_supported s₂ u _ twoU,
    sum_supported s₁ u w₁ oneU, sum_supported s₂ u w₂ twoU] at total
  have split₁ : stake w₁ active₁ + stake w₁ (s₁ \ active₁) = stake w₁ s₁ :=
    (stake_add_stake_sdiff (w := w₁) active₁ s₁).trans (by
      simp [Finset.sdiff_eq_empty_iff_subset.mpr activeInside₁])
  have split₂ : stake w₂ active₂ + stake w₂ (s₂ \ active₂) = stake w₂ s₂ :=
    (stake_add_stake_sdiff (w := w₂) active₂ s₂).trans (by
      simp [Finset.sdiff_eq_empty_iff_subset.mpr activeInside₂])
  unfold stake at *
  dsimp only at *
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
