module

public import EthLib.Consensus.Proofs.Models.Stake
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Honest support of a block, after the fast confirmation rule

The bounds are Lemmas 1, 3 and 4 of Appendix A of the fast confirmation paper.

The paper is [arXiv 2405.00549v4](https://arxiv.org/abs/2405.00549v4).

Its indicators of support are Definitions 2 and 3, in §3.2.

Sets of validators are weighed by their stake.

The committees of a range of slots form a set `W`, and the honest validators form a set `J`.

The validators of `W` that support a block form a set `S`.

The validators of `W` known to have equivocated form a set `I`.

The Byzantine validators hold at most the fraction `β = num / den` of the stake of `W`.

That bound is Assumption 2 of the paper, taken as a hypothesis.

One more bound serves the discount for empty slots of the specification.

The support of a block, less an adversary that covers `β W - I`, is at most its honest support.

Every bound is stated with its fractions multiplied out, in natural numbers.

Views, checkpoints and Assumption 1 are left out: the statements bound stakes only.
-/

@[expose] public section

namespace EthLib.Consensus.Models.ForkChoice

variable {ν : Type*} {w : ν → ℕ} {J : Set ν} [DecidablePred (· ∈ J)]

/-- Lemma 3: an honest ratio above `Φ / (2 (1 - β) W)` gives honest support `H` above `Φ / 2`.

The honest ratio is `H / K`, where the honest validators of the committees hold the stake `K`.

The hypothesis that they hold at least the fraction `1 - β` of the stake `W` is Assumption 2. -/
theorem lt_two_mul_of_honest_ratio {Φ H K W num den : ℕ} (honest : (den - num) * W ≤ den * K)
    (ratio : den * Φ * K < 2 * (den - num) * W * H) : Φ < 2 * H := by
  by_contra! le
  have share := Nat.mul_le_mul_left (2 * H) honest
  have scaled := Nat.mul_le_mul_right (den * K) le
  have : 2 * (den - num) * W * H ≤ den * Φ * K := by
    calc 2 * (den - num) * W * H = 2 * H * ((den - num) * W) := by ring
      _ ≤ 2 * H * (den * K) := share
      _ ≤ Φ * (den * K) := scaled
      _ = den * Φ * K := by ring
  omega

/-- The counting step of Lemma 1: new honest votes for a block do not lower its honest ratio.

The honest supporters `H` lie in the honest committee set `K`.

The honest validators `N` of the later committees all support the block.

So the later honest supporters `H'` hold both `H` and `N`.

The ratio of `H` to `K` is then at most that of `H'` to the union of `K` and `N`. -/
theorem honest_ratio_le_of_new_votes [DecidableEq ν] {H K N H' : Finset ν} (supportIn : H ⊆ K)
    (later : H ∪ N ⊆ H') :
    stake w H * stake w (K ∪ N) ≤ stake w H' * stake w K := by
  -- The votes that join the honest set also join the honest support.
  have joined : stake w (K ∪ N) = stake w K + stake w (N \ K) := by
    rw [← Finset.union_sdiff_self_eq_union]
    exact Finset.sum_union Finset.disjoint_sdiff
  have gained : stake w H + stake w (N \ K) ≤ stake w H' := by
    have apart : Disjoint H (N \ K) :=
      Finset.disjoint_left.mpr fun _ inH inNew => (Finset.mem_sdiff.mp inNew).2 (supportIn inH)
    unfold stake
    rw [← Finset.sum_union apart]
    exact stake_mono (Finset.union_subset (Finset.subset_union_left.trans later)
      ((Finset.sdiff_subset).trans (Finset.subset_union_right.trans later)))
  have below : stake w H ≤ stake w K := stake_mono supportIn
  rw [joined]
  calc stake w H * (stake w K + stake w (N \ K))
      = stake w H * stake w K + stake w H * stake w (N \ K) := by ring
    _ ≤ stake w H * stake w K + stake w K * stake w (N \ K) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ below) _
    _ = (stake w H + stake w (N \ K)) * stake w K := by ring
    _ ≤ stake w H' * stake w K := Nat.mul_le_mul_right _ gained

/-- Lemma 1 for a threshold: an honest ratio above `a / c` stays above it after new honest votes.

The sets are those of the counting step. -/
theorem honest_ratio_of_new_votes [DecidableEq ν] {H K N H' : Finset ν} {a c : ℕ}
    (supportIn : H ⊆ K) (later : H ∪ N ⊆ H') (ratio : a * stake w K < c * stake w H) :
    a * stake w (K ∪ N) < c * stake w H' := by
  have counted := honest_ratio_le_of_new_votes (w := w) supportIn later
  -- The honest committees have stake, or the honest supporters would have none either.
  have positive : 0 < stake w K := by
    by_contra! zero
    have : stake w H = 0 := Nat.eq_zero_of_le_zero ((stake_mono supportIn).trans zero)
    simp_all
  refine Nat.lt_of_mul_lt_mul_right (a := stake w K) ?_
  calc a * stake w (K ∪ N) * stake w K = a * stake w K * stake w (K ∪ N) := by ring
    _ < c * stake w H * stake w (K ∪ N) :=
        Nat.mul_lt_mul_of_pos_right ratio
          (lt_of_lt_of_le positive (stake_mono Finset.subset_union_left))
    _ = c * (stake w H * stake w (K ∪ N)) := by ring
    _ ≤ c * (stake w H' * stake w K) := Nat.mul_le_mul_left c counted
    _ = c * stake w H' * stake w K := by ring

/-- The Byzantine supporters and the equivocators weigh at most the Byzantine validators of `W`.

The supporters `S` and the equivocators `I` are disjoint parts of `W`.

No equivocator is honest.

This is the disjoint accounting used in arXiv 2405.00549v4, Appendix A.1, Lemma 4. -/
theorem byzantine_support_add_le {W S I : Finset ν} (supportIn : S ⊆ W) (equivocatorsIn : I ⊆ W)
    (apart : Disjoint S I) (dishonest : ∀ v ∈ I, v ∉ J) :
    stake w {v ∈ S | v ∉ J} + stake w I ≤ stake w {v ∈ W | v ∉ J} := by
  classical
  have disjoint : Disjoint ({v ∈ S | v ∉ J} : Finset ν) I :=
    Finset.disjoint_of_subset_left (Finset.filter_subset _ _) apart
  unfold stake
  rw [← Finset.sum_union disjoint]
  refine stake_mono (Finset.union_subset ?_ ?_)
  · exact Finset.filter_subset_filter _ supportIn
  · intro v member
    exact Finset.mem_filter.mpr ⟨equivocatorsIn member, dishonest v member⟩

/-- The support of a block, less an adversary, is at most its honest support.

The supporters `S` and the equivocators `I` are disjoint parts of `W`.

No equivocator is honest.

The adversary and the equivocators must cover the Byzantine share `β W`.

Each set stands for its stake, and the difference is zero when the adversary is larger.

This is the honest lower bound of arXiv 2405.00549v4, Definition 5, under Assumption 2. -/
theorem sub_le_honest_support {W S I : Finset ν} {adversary num den : ℕ}
    (bound : ByzantineStakeAtMost w W J num den) (supportIn : S ⊆ W) (equivocatorsIn : I ⊆ W)
    (apart : Disjoint S I) (dishonest : ∀ v ∈ I, v ∉ J)
    (covered : num * stake w W ≤ den * (adversary + stake w I)) :
    stake w S - adversary ≤ stake w {v ∈ S | v ∈ J} := by
  obtain ⟨positiveDen, byzantineBound⟩ := bound
  -- The support splits into honest and Byzantine validators.
  have split : stake w {v ∈ S | v ∈ J} + stake w {v ∈ S | v ∉ J} = stake w S :=
    Finset.sum_filter_add_sum_filter_not S (· ∈ J) w
  have byzantine := byzantine_support_add_le (w := w) supportIn equivocatorsIn apart dishonest
  -- The Byzantine validators of `W` weigh at most the adversary and the equivocators.
  have room : stake w {v ∈ W | v ∉ J} ≤ adversary + stake w I :=
    Nat.le_of_mul_le_mul_left (byzantineBound.trans covered) positiveDen
  omega

/-- Lemma 4: the observed support of a block bounds its honest ratio from below.

The supporters `S` and the equivocators `I` are disjoint parts of `W`.

No equivocator is honest.

The observed condition is `S > Φ / 2 + β W - I`.

The conclusion is `H / (W ∩ J) > Φ / (2 (1 - β) W)`, with `H` the honest part of `S`.

Each set stands for its stake. -/
theorem honest_ratio_of_support {W S I : Finset ν} {Φ num den : ℕ}
    (bound : ByzantineStakeAtMost w W J num den) (supportIn : S ⊆ W) (equivocatorsIn : I ⊆ W)
    (apart : Disjoint S I) (dishonest : ∀ v ∈ I, v ∉ J)
    (observed : den * Φ + 2 * num * stake w W < 2 * den * (stake w S + stake w I)) :
    den * Φ * stake w {v ∈ W | v ∈ J} <
      2 * (den - num) * stake w W * stake w {v ∈ S | v ∈ J} := by
  classical
  obtain ⟨positiveDen, byzantineBound⟩ := bound
  set A := stake w {v ∈ W | v ∉ J}
  set X := stake w S + stake w I
  -- The committees split into honest and Byzantine validators, and so does the support.
  have splitW : stake w {v ∈ W | v ∈ J} + A = stake w W :=
    Finset.sum_filter_add_sum_filter_not W (· ∈ J) w
  have splitS : stake w {v ∈ S | v ∈ J} + stake w {v ∈ S | v ∉ J} = stake w S :=
    Finset.sum_filter_add_sum_filter_not S (· ∈ J) w
  -- The Byzantine supporters and the equivocators are disjoint Byzantine validators.
  have byzantine : stake w {v ∈ S | v ∉ J} + stake w I ≤ A :=
    byzantine_support_add_le supportIn equivocatorsIn apart dishonest
  -- The supporters and the equivocators fit in the committees.
  have fits : X ≤ stake w W := by
    unfold X stake
    rw [← Finset.sum_union apart]
    exact stake_mono (Finset.union_subset supportIn equivocatorsIn)
  set H := stake w {v ∈ S | v ∈ J}
  set Jw := stake w {v ∈ W | v ∈ J}
  set Wt := stake w W
  have honestLower : X ≤ H + A := by omega
  -- The fraction is below one, or the observed support would exceed the committees.
  have below : num < den := by
    by_contra! le
    have := Nat.mul_le_mul_right Wt le
    nlinarith
  -- Without honest stake there would be no stake at all, against the observed condition.
  have positive : 0 < Jw := by
    by_contra! zero
    have same : A = Wt := by omega
    rw [same] at byzantineBound
    have empty : Wt = 0 := by
      by_contra! pos
      have := Nat.mul_lt_mul_of_pos_right below (Nat.pos_of_ne_zero pos)
      omega
    have none : X = 0 := by omega
    simp [none, empty] at observed
  zify [below.le] at *
  have key : (2 * (den - num) * Wt * (X - A) : ℤ) - (2 * den * X - 2 * num * Wt) * (Wt - A) =
      2 * (Wt - X) * (num * Wt - den * A) := by ring
  have nonneg : (0 : ℤ) ≤ 2 * (Wt - X) * (num * Wt - den * A) := by
    apply mul_nonneg <;> nlinarith
  have strict : (den * Φ : ℤ) * Jw < (2 * den * X - 2 * num * Wt) * Jw :=
    mul_lt_mul_of_pos_right (by linarith) (by exact_mod_cast positive)
  have jw : (Jw : ℤ) = Wt - A := by linarith
  have hx : (X : ℤ) - A ≤ H := by linarith
  have coeff : (0 : ℤ) ≤ 2 * (den - num) * Wt := by
    apply mul_nonneg <;> [nlinarith; positivity]
  rw [jw] at strict ⊢
  linarith [mul_le_mul_of_nonneg_left hx coeff]

/-- Lemmas 4 and 3 together: the observed support of a block gives honest support above `Φ / 2`.

The observed condition is `S > Φ / 2 + β W - I`, as in Lemma 4. -/
theorem lt_two_mul_honest_support {W S I : Finset ν} {Φ num den : ℕ}
    (bound : ByzantineStakeAtMost w W J num den) (supportIn : S ⊆ W) (equivocatorsIn : I ⊆ W)
    (apart : Disjoint S I) (dishonest : ∀ v ∈ I, v ∉ J)
    (observed : den * Φ + 2 * num * stake w W < 2 * den * (stake w S + stake w I)) :
    Φ < 2 * stake w {v ∈ S | v ∈ J} :=
  lt_two_mul_of_honest_ratio bound.honest
    (honest_ratio_of_support bound supportIn equivocatorsIn apart dishonest observed)

/-- The hypotheses of Lemma 4 hold together, so it and the combined bound are not vacuous.

Five validators have stake one, and only the last one is Byzantine.

The fraction is `1 / 5`, and the threshold `Φ` is `5`.

The first three validators support the block, and the Byzantine one has equivocated. -/
theorem honest_support_hypotheses :
    ByzantineStakeAtMost (fun _ : Fin 5 => 1) Finset.univ {v | v ≠ 4} 1 5 ∧
      ({0, 1, 2} : Finset (Fin 5)) ⊆ Finset.univ ∧ ({4} : Finset (Fin 5)) ⊆ Finset.univ ∧
      Disjoint ({0, 1, 2} : Finset (Fin 5)) {4} ∧ (∀ v ∈ ({4} : Finset (Fin 5)), v ∉ {v | v ≠ 4}) ∧
      5 * 5 + 2 * 1 * stake (fun _ : Fin 5 => 1) Finset.univ <
        2 * 5 * (stake (fun _ : Fin 5 => 1) {0, 1, 2} + stake (fun _ : Fin 5 => 1) {4}) := by
  simp only [ByzantineStakeAtMost, stake]
  decide

end EthLib.Consensus.Models.ForkChoice
