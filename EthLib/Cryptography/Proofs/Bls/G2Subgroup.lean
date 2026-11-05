module

public import EthLib.Cryptography.Proofs.Bls.G2Order
public import EthLib.Cryptography.Proofs.Bls.G2Equiv

/-!
# Proofs: what the `G2` subgroup check decides

On valid triples, the subgroup check decides `[r] P = 0`.

The check is the one of draft-04, §1.3 and §2.2.
<https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04>

It accepts the generator, and it is closed under scalar multiplication, addition and negation.

This file does not claim that the points of order `r` of `E'(Fp2)` form a cyclic group.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.G2

open WeierstrassCurve.Jacobian

/-- `Valid` is required because singular `z != 0` triples also map to `0` under `toPoint`. -/
theorem isInfinity_eq_true_iff_toPoint_eq_zero {p : G2} (hp : Valid p) :
    p.isInfinity = true ↔ toPoint p = 0 := by
  constructor
  · intro h
    exact Point.toAffine_of_Z_eq_zero (Fp2.isZero_iff.mp h)
  · intro h
    -- A finite nonsingular representative maps to `Point.some`, never `0`.
    by_contra hne
    have hz : p.z ≠ 0 := fun hz0 => hne (Fp2.isZero_iff.mpr hz0)
    rw [toPoint, Point.toAffine_of_Z_ne_zero hp hz] at h
    cases h

theorem inSubgroup_iff_modulus_smul_eq_zero {p : G2} (hp : Valid p) :
    inSubgroup p = true ↔ Fr.modulus • toPoint p = 0 := by
  rw [inSubgroup]
  by_cases hi : p.isInfinity = true
  · rw [ite_eq_left hi, (isInfinity_eq_true_iff_toPoint_eq_zero hp).mp hi]
    simp
  · rw [ite_eq_right hi, isInfinity_eq_true_iff_toPoint_eq_zero (valid_mulNat hp _),
      toPoint_mulNat hp]

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

end EthLib.Cryptography.Bls.G2
