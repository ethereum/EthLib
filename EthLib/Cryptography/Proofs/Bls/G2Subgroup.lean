module

public import EthLib.Cryptography.Proofs.Bls.G2Endomorphism
public import EthLib.Cryptography.Proofs.Bls.G2SubgroupSpan

/-!
# Proofs: what the `G2` subgroup check decides

On valid triples, the subgroup check decides `[r] P = 0`, as draft-04 §1.3 and §2.2 require.
<https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04>

The check tests `psi(P) = [t] P`.

- A point that passes has `[r] P = 0`, by the relation `psi^4 - psi^2 + 1 = 0`.
- A point with `[r] P = 0` is a multiple of the generator, on which `psi` acts as `[t]`.

It accepts the generator, and it is closed under scalar multiplication, addition and negation.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.G2

open WeierstrassCurve.Jacobian

/-- The subgroup check accepts a valid point exactly when `[r] P = 0`.

For a finite point the check is `psi(P) = [t] P`, which is Scott's criterion. -/
theorem inSubgroup_iff_modulus_smul_eq_zero {p : G2} (hp : Valid p) :
    inSubgroup p = true ↔ Fr.modulus • toPoint p = 0 := by
  rw [inSubgroup]
  by_cases hi : p.isInfinity = true
  · rw [ite_eq_left hi, (isInfinity_eq_true_iff_toPoint_eq_zero hp).mp hi]
    simp
  · have hv := valid_mulNat hp blsX
    rw [ite_eq_right hi,
      projectiveEq_eq_true_iff_toPoint_eq (HashToCurve.psi_valid hp) (valid_neg hv),
      TwistFrobenius.toPoint_psi hp, toPoint_neg hv, toPoint_mulNat hp]
    refine ⟨modulus_smul_eq_zero_of_hom, fun h => ?_⟩
    obtain ⟨n, -, hn⟩ := exists_nsmul_generator_of_modulus_smul_eq_zero h
    rw [hn]
    exact TwistFrobenius.hom_generator_nsmul n

theorem inSubgroup_generator : inSubgroup generator = true :=
  (inSubgroup_iff_modulus_smul_eq_zero valid_generator).mpr modulus_smul_generator

theorem inSubgroup_mulNat {p : G2} (hp : Valid p) (hs : inSubgroup p = true)
    (k : Nat) : inSubgroup (mulNat p k) = true := by
  apply (inSubgroup_iff_modulus_smul_eq_zero (valid_mulNat hp k)).mpr
  -- Commute `Fr.modulus` past `k` so `[r] * toPoint p = 0` annihilates the multiple.
  rw [toPoint_mulNat hp, smul_comm,
    (inSubgroup_iff_modulus_smul_eq_zero hp).mp hs, nsmul_zero]

theorem inSubgroup_mul_generator (s : Fr) : inSubgroup (mul generator s) = true :=
  inSubgroup_mulNat valid_generator inSubgroup_generator s.val

/-- Because `g_2` has order `r` and `s.val < r`, `[s] * g_2` vanishes only at `s = 0`. -/
theorem mul_generator_isInfinity_iff (s : Fr) :
    (mul (generator : G2) s).isInfinity = true ↔ s = 0 := by
  rw [isInfinity_eq_true_iff_toPoint_eq_zero (valid_mul valid_generator s),
    toPoint_mul valid_generator, ← addOrderOf_dvd_iff_nsmul_eq_zero,
    addOrderOf_toPoint_generator]
  constructor
  · intro h
    exact Fr.ext (by rw [Fr.val_zero]; exact Nat.eq_zero_of_dvd_of_lt h (Fr.val_lt s))
  · rintro rfl
    rw [Fr.val_zero]
    exact Nat.dvd_zero _

theorem inSubgroup_add {p q : G2} (hp : Valid p) (hq : Valid q)
    (hs : inSubgroup p = true) (ht : inSubgroup q = true) :
    inSubgroup (add p q) = true := by
  apply (inSubgroup_iff_modulus_smul_eq_zero (valid_add hp hq)).mpr
  rw [toPoint_add hp hq, nsmul_add,
    (inSubgroup_iff_modulus_smul_eq_zero hp).mp hs,
    (inSubgroup_iff_modulus_smul_eq_zero hq).mp ht]
  simp

theorem inSubgroup_neg {p : G2} (hp : Valid p) (hs : inSubgroup p = true) :
    inSubgroup (neg p) = true := by
  apply (inSubgroup_iff_modulus_smul_eq_zero (valid_neg hp)).mpr
  rw [toPoint_neg hp, neg_nsmul,
    (inSubgroup_iff_modulus_smul_eq_zero hp).mp hs]
  simp

/-- A valid point in the subgroup equals `[n] * g_2` for some `n < r`. -/
theorem exists_mulNat_generator_of_inSubgroup {P : G2} (hP : Valid P)
    (hsub : inSubgroup P = true) :
    ∃ n : Nat, n < Fr.modulus ∧ toPoint P = toPoint (mulNat generator n) := by
  obtain ⟨n, hn, he⟩ := exists_nsmul_generator_of_modulus_smul_eq_zero
    ((inSubgroup_iff_modulus_smul_eq_zero hP).mp hsub)
  exact ⟨n, hn, he.trans (toPoint_mulNat valid_generator n).symm⟩

/-- A valid point in the subgroup equals `[a] * g_2` for some `a` in `Fr`. -/
theorem exists_mul_generator_of_inSubgroup {P : G2} (hP : Valid P)
    (hsub : inSubgroup P = true) :
    ∃ a : Fr, toPoint P = toPoint (mul generator a) := by
  obtain ⟨n, hn, he⟩ := exists_mulNat_generator_of_inSubgroup hP hsub
  exact ⟨Fr.ofNat n, by rw [he, mul, Fr.val_ofNat_of_lt hn]⟩

end EthLib.Cryptography.Bls.G2
