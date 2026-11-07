module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Tactic.LinearCombination

/-!
# Proofs: the multiproof batching lemma

This is Lemma 2 of Wagner and Zapico, ePrint 2025/1683, §2.3, over any field.

<https://eprint.iacr.org/2025/1683>

Let a set `S` of distinct nodes be the disjoint union of nonempty parts `S_j`.

Let the vanishing polynomial of `S - S_j` take one value `δ_j` on all of `S_j`.

Claim 1: the interpolation on `S` is the sum of `V_{S - S_j} I_j / δ_j`.

Here `I_j` is the interpolation on `S_j`, and `V_T` vanishes on `T`.

Claim 2: the sum of `V_{S - S_j} / δ_j` is 1.

The paper states it as `1 / V_S = sum_j 1 / (δ_j V_{S_j})`; here both sides are multiplied by `V_S`.

Then from `c - I_j(τ) = φ_j V_{S_j}(τ)` for every part, it follows that `c - I(τ) = φ V_S(τ)`.

Here `I` is the interpolation on `S`, and `φ = sum_j φ_j / δ_j`.

The proof of Claim 1 checks the values on the nodes, and Claim 2 is Claim 1 for the values 1.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open Polynomial Lagrange Finset

variable {F : Type} [Field F] {ι κ : Type} [DecidableEq ι]

/-- The vanishing polynomial of the rest of a union is not zero at a node of a part. -/
theorem nodal_sdiff_ne_zero {T : Finset κ} {part : κ → Finset ι} {v : ι → F}
    (hv : Set.InjOn v (T.biUnion part)) {j : κ} (hj : j ∈ T) {i : ι} (hi : i ∈ part j) :
    (nodal (T.biUnion part \ part j) v).eval (v i) ≠ 0 := by
  refine eval_nodal_not_at_node fun i' hi' heq => ?_
  have hi'S := (Finset.mem_sdiff.mp hi').1
  have := hv (Finset.mem_biUnion.mpr ⟨j, hj, hi⟩) hi'S heq
  exact (Finset.mem_sdiff.mp hi').2 (this ▸ hi)

/-- Claim 1 of Lemma 2.

The interpolation on a union is a weighted sum of the interpolations on its parts. -/
theorem interpolate_biUnion {T : Finset κ} {part : κ → Finset ι}
    (hdisj : (T : Set κ).PairwiseDisjoint part) {v : ι → F}
    (hv : Set.InjOn v (T.biUnion part)) {δ : κ → F}
    (hδ : ∀ j ∈ T, ∀ i ∈ part j, (nodal (T.biUnion part \ part j) v).eval (v i) = δ j)
    (r : ι → F) :
    interpolate (T.biUnion part) v r =
      ∑ j ∈ T, C (δ j)⁻¹ * nodal (T.biUnion part \ part j) v * interpolate (part j) v r := by
  symm
  refine eq_interpolate_of_eval_eq _ hv ?_ fun i hi => ?_
  · refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
      fun j hj => ?_)
    have hsub : part j ⊆ T.biUnion part := Finset.subset_biUnion_of_mem part hj
    have hcard : #(T.biUnion part \ part j) + #(part j) = #(T.biUnion part) := by
      rw [card_sdiff_of_subset hsub]
      exact Nat.sub_add_cancel (card_le_card hsub)
    rcases eq_or_ne (interpolate (part j) v r) 0 with h0 | h0
    · rw [h0, mul_zero, degree_zero]
      exact WithBot.bot_lt_coe _
    have hI := degree_interpolate_lt (r := r) (hv.mono hsub)
    rw [degree_eq_natDegree h0, Nat.cast_lt] at hI
    obtain ⟨i, hi⟩ : (part j).Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty.mp hne, interpolate_empty] at h0
      exact h0 rfl
    have hδj : δ j ≠ 0 := hδ j hj i hi ▸ nodal_sdiff_ne_zero hv hj hi
    rw [degree_eq_natDegree (mul_ne_zero (mul_ne_zero (C_ne_zero.mpr (inv_ne_zero hδj))
        nodal_ne_zero) h0), Nat.cast_lt,
      natDegree_mul (mul_ne_zero (C_ne_zero.mpr (inv_ne_zero hδj)) nodal_ne_zero) h0,
      natDegree_C_mul (inv_ne_zero hδj), natDegree_nodal]
    omega
  · obtain ⟨j₀, hj₀, hi₀⟩ := Finset.mem_biUnion.mp hi
    rw [eval_finsetSum, Finset.sum_eq_single j₀]
    · have hδj : δ j₀ ≠ 0 := hδ j₀ hj₀ i hi₀ ▸ nodal_sdiff_ne_zero hv hj₀ hi₀
      rw [eval_mul, eval_mul, eval_C, hδ j₀ hj₀ i hi₀, inv_mul_cancel₀ hδj, one_mul,
        eval_interpolate_at_node _ (hv.mono (Finset.subset_biUnion_of_mem part hj₀)) hi₀]
    · intro j hj hne
      have hij : i ∈ T.biUnion part \ part j :=
        Finset.mem_sdiff.mpr ⟨hi, Finset.disjoint_left.mp (hdisj hj₀ hj (Ne.symm hne)) hi₀⟩
      rw [eval_mul, eval_mul, eval_nodal_at_node hij, mul_zero, zero_mul]
    · exact fun h => absurd hj₀ h

/-- Claim 2 of Lemma 2, cleared of denominators: the weighted vanishing polynomials sum to 1. -/
theorem sum_nodal_sdiff {T : Finset κ} {part : κ → Finset ι}
    (hdisj : (T : Set κ).PairwiseDisjoint part) {v : ι → F}
    (hv : Set.InjOn v (T.biUnion part)) {δ : κ → F}
    (hδ : ∀ j ∈ T, ∀ i ∈ part j, (nodal (T.biUnion part \ part j) v).eval (v i) = δ j)
    (hne : ∀ j ∈ T, (part j).Nonempty) (hT : T.Nonempty) :
    ∑ j ∈ T, C (δ j)⁻¹ * nodal (T.biUnion part \ part j) v = 1 := by
  have h := interpolate_biUnion hdisj hv hδ 1
  obtain ⟨j, hj⟩ := hT
  rw [interpolate_one hv ⟨_, Finset.mem_biUnion.mpr ⟨j, hj, (hne j hj).choose_spec⟩⟩] at h
  rw [h]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [interpolate_one (hv.mono (Finset.subset_biUnion_of_mem part hj)) (hne j hj), mul_one]

/-- The vanishing polynomial of a union is the product of those of a part and of the rest. -/
theorem eval_nodal_sdiff_mul {T : Finset κ} {part : κ → Finset ι} {v : ι → F} {j : κ}
    (hj : j ∈ T) (τ : F) :
    (nodal (T.biUnion part \ part j) v).eval τ * (nodal (part j) v).eval τ =
      (nodal (T.biUnion part) v).eval τ := by
  rw [eval_nodal, eval_nodal, eval_nodal]
  exact Finset.prod_sdiff (Finset.subset_biUnion_of_mem part hj)

/-- **Lemma 2, the multiproof batching lemma.**

Let `S` be the disjoint union of nonempty parts `S_j`, with distinct nodes `v_i`.

Let the vanishing polynomial of `S \ S_j` take one value `δ_j` at every node of `S_j`.

Let `I_j` interpolate the values `r` on `S_j`, and let `V_j` be the vanishing polynomial of `S_j`.

Let each part satisfy `c - I_j(τ) = φ_j V_j(τ)`.

Let `I` be the interpolation and `V` the vanishing polynomial of `S`.

Then `c - I(τ) = φ V(τ)`, with `φ = sum_j φ_j / δ_j`. -/
theorem multiproof_batching {T : Finset κ} {part : κ → Finset ι}
    (hdisj : (T : Set κ).PairwiseDisjoint part) {v : ι → F}
    (hv : Set.InjOn v (T.biUnion part)) {δ : κ → F}
    (hδ : ∀ j ∈ T, ∀ i ∈ part j, (nodal (T.biUnion part \ part j) v).eval (v i) = δ j)
    (hne : ∀ j ∈ T, (part j).Nonempty) (hT : T.Nonempty) (r : ι → F) {c τ : F} {φ : κ → F}
    (h : ∀ j ∈ T, c - (interpolate (part j) v r).eval τ = φ j * (nodal (part j) v).eval τ) :
    c - (interpolate (T.biUnion part) v r).eval τ =
      (∑ j ∈ T, (δ j)⁻¹ * φ j) * (nodal (T.biUnion part) v).eval τ := by
  have h1 := congrArg (eval τ) (sum_nodal_sdiff hdisj hv hδ hne hT)
  rw [eval_finsetSum, eval_one] at h1
  rw [interpolate_biUnion hdisj hv hδ r, eval_finsetSum, ← mul_one c, ← h1, Finset.mul_sum,
    ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [eval_mul, eval_C]
  linear_combination ((δ j)⁻¹ * (nodal (T.biUnion part \ part j) v).eval τ) * h j hj +
    ((δ j)⁻¹ * φ j) * eval_nodal_sdiff_mul (part := part) (v := v) hj τ

end EthLib.Cryptography.Kzg
