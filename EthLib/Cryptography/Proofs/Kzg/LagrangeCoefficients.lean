module

public import EthLib.Cryptography.Proofs.Kzg.Commitment
public import EthLib.Cryptography.Proofs.Kzg.FftInverse

/-!
# Proofs: the Lagrange points as combinations of the monomial points

Let `d` be a point of the blob domain, and let `n = 4096`.

The Lagrange basis polynomial of `d` is `n⁻¹ * sum_{j < n} (X / d)^j`.

At another domain point `e`, the sum is a geometric sum of the root of unity `e / d`, so it is `0`.

At `d` the sum is `n`, so the polynomial is `1` there.

Its degree is below `n`, so it is the basis polynomial, and its coefficient `j` is `n⁻¹ * d⁻¹ ^ j`.

A setup holds the Lagrange points of its monomial points when each Lagrange point is the sum of the
monomial points times the coefficients of its basis polynomial.

Then any `τ` whose powers the monomial points represent makes the setup well formed.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg

open EthLib.Cryptography.Bls (G1 G2 Fr)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr
open Polynomial

/-- The polynomial `n⁻¹ * sum_{j < n} (X / d)^j`, for the domain point `d`. -/
noncomputable def basisSum (i : Fin FIELD_ELEMENTS_PER_BLOB) : _root_.Polynomial Fr :=
  ∑ j ∈ Finset.range FIELD_ELEMENTS_PER_BLOB,
    C ((FIELD_ELEMENTS_PER_BLOB : Fr)⁻¹ * (evalDomain i)⁻¹ ^ j) * X ^ j

private theorem degree_basisSum_lt (i : Fin FIELD_ELEMENTS_PER_BLOB) :
    (basisSum i).degree < (Finset.univ : Finset (Fin FIELD_ELEMENTS_PER_BLOB)).card := by
  rw [Finset.card_univ, Fintype.card_fin, basisSum]
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun j hj => ?_
  refine lt_of_le_of_lt (degree_C_mul_X_pow_le j _) ?_
  exact_mod_cast Finset.mem_range.mp hj

private theorem eval_basisSum (i m : Fin FIELD_ELEMENTS_PER_BLOB) :
    (basisSum i).eval (evalDomain m) = if i = m then 1 else 0 := by
  have hn := natCast_field_elements_per_blob_ne_zero
  have hd : evalDomain i ≠ 0 := by
    intro h
    have hw := evalDomain_pow_width i
    rw [h, zero_pow (by decide)] at hw
    exact zero_ne_one hw
  rw [basisSum, eval_finsetSum]
  simp only [eval_mul, eval_C, eval_X_pow, mul_assoc]
  rw [← Finset.mul_sum]
  simp only [← mul_pow, mul_comm _ (evalDomain m)]
  by_cases him : i = m
  · subst him
    rw [mul_inv_cancel₀ hd, ite_eq_left rfl, EthLib.Cryptography.Kzg.geom_sum_one,
      inv_mul_cancel₀ hn]
  · rw [ite_eq_right him]
    have hc : evalDomain m * (evalDomain i)⁻¹ ≠ 1 := by
      intro h
      exact him (evalDomain_injective ((mul_inv_eq_one₀ hd).mp h).symm)
    have hcn : (evalDomain m * (evalDomain i)⁻¹) ^ FIELD_ELEMENTS_PER_BLOB = 1 := by
      rw [mul_pow, inv_pow, evalDomain_pow_width, evalDomain_pow_width, inv_one, mul_one]
    rw [EthLib.Cryptography.Kzg.geom_sum_root_ne_one hcn hc, mul_zero]

/-- The Lagrange basis polynomial of a domain point `d` is `n⁻¹ * sum_{j < n} (X / d)^j`. -/
theorem basis_eq_basisSum (i : Fin FIELD_ELEMENTS_PER_BLOB) :
    Lagrange.basis Finset.univ evalDomain i = basisSum i := by
  refine eq_of_degrees_lt_of_eval_index_eq _ evalDomain_injective.injOn ?_
    (degree_basisSum_lt i) fun m _ => ?_
  · rw [Lagrange.degree_basis evalDomain_injective.injOn (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    exact_mod_cast Nat.sub_lt (by decide) Nat.one_pos
  · rw [eval_basisSum]
    by_cases him : i = m
    · subst him
      rw [ite_eq_left rfl, Lagrange.eval_basis_self evalDomain_injective.injOn (Finset.mem_univ i)]
    · rw [ite_eq_right him, Lagrange.eval_basis_of_ne him (Finset.mem_univ m)]

/-- Coefficient `j < n` of the basis polynomial of the domain point `d` is `n⁻¹ * d⁻¹ ^ j`. -/
theorem coeff_basis (i : Fin FIELD_ELEMENTS_PER_BLOB) {j : Nat} (hj : j < FIELD_ELEMENTS_PER_BLOB) :
    (Lagrange.basis Finset.univ evalDomain i).coeff j =
      (FIELD_ELEMENTS_PER_BLOB : Fr)⁻¹ * (evalDomain i)⁻¹ ^ j := by
  rw [basis_eq_basisSum, basisSum, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single j (fun b _ hb => by rw [ite_eq_right (Ne.symm hb), mul_zero])
    (fun h => absurd (Finset.mem_range.mpr hj) h), ite_eq_left rfl, mul_one]

/-- The value of a basis polynomial at `τ` is the sum of its coefficients times powers of `τ`. -/
theorem eval_basis_eq_sum (i : Fin FIELD_ELEMENTS_PER_BLOB) (τ : Fr) :
    (Lagrange.basis Finset.univ evalDomain i).eval τ =
      ∑ j ∈ Finset.range FIELD_ELEMENTS_PER_BLOB,
        (Lagrange.basis Finset.univ evalDomain i).coeff j * τ ^ j := by
  refine eval_eq_sum_range' ?_ τ
  rw [Lagrange.natDegree_basis evalDomain_injective.injOn (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]
  exact Nat.sub_lt (by decide) Nat.one_pos

/-- Each Lagrange point is the sum of the monomial points of `G1` times the coefficients of its
basis polynomial.

Lagrange point `i` belongs to domain point `i`, as in the decoded setup. -/
def TrustedSetup.LagrangeOfMonomial (s : TrustedSetup) : Prop :=
  ∀ i : Fin FIELD_ELEMENTS_PER_BLOB, G1.toPoint s.g1LagrangeBrp[i] =
    ∑ j : Fin FIELD_ELEMENTS_PER_BLOB,
      ((Lagrange.basis Finset.univ evalDomain i).coeff j).val • G1.toPoint s.g1Monomial[j]

/-- A valid setup whose Lagrange points come from its monomial points is well formed at every `τ`
whose powers its monomial points represent. -/
theorem TrustedSetup.WellFormed.of_lagrangeOfMonomial {s : TrustedSetup} {τ : Fr}
    (hv : s.Valid) (hl : s.LagrangeOfMonomial)
    (hg1 : ∀ i : Fin FIELD_ELEMENTS_PER_BLOB, G1.Represents s.g1Monomial[i] (τ ^ i.val))
    (hg2 : ∀ i : Fin KZG_SETUP_G2_LENGTH, G2.Represents s.g2Monomial[i] (τ ^ i.val)) :
    s.WellFormed τ := by
  refine ⟨fun i => ⟨hv.g1LagrangeBrp i, ?_⟩, hg1, hg2⟩
  rw [hl i, G1.toPoint_mul_generator, eval_basis_eq_sum,
    ← G1.sum_nsmul_ofFr _ (fun j => (Lagrange.basis Finset.univ evalDomain i).coeff j)
      (fun j => τ ^ j),
    ← Fin.sum_univ_eq_sum_range (fun j =>
      ((Lagrange.basis Finset.univ evalDomain i).coeff j).val • G1.ofFr (τ ^ j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(hg1 j).2, G1.toPoint_mul_generator]

end EthLib.Cryptography.Kzg
