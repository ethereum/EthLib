module

public import EthLib.Cryptography.Proofs.AltBn128.FinalExponentiation

/-!
# Proofs: the pairing of alt_bn128 is not degenerate

The pairing of the generators `P1` and `P2` is neither 0 nor 1, and its order is the prime `q`.

`G_1` and `G_2` are cyclic, so a bilinear map that is not 1 on the generators is not degenerate.

The kernel evaluates the pairing of the generators once.
-/

@[expose] public section

namespace EthLib.Cryptography.AltBn128

/-- The pairing of `P1` and `P2` is neither 0 nor 1, which the kernel computes.

The kernel compares coefficients, so the statement writes 0 and 1 by their coefficients. -/
private theorem pairing_generators_ne_ofFp_zero_and_ne_one :
    pairing Point.generator Point2.generator ≠ Fp12.ofFp 0 ∧
      pairing Point.generator Point2.generator ≠ Fp12.one := by
  decide +kernel

/-- The pairing of `P1` and `P2` is not 0. -/
theorem pairing_generators_ne_zero : pairing Point.generator Point2.generator ≠ 0 := by
  rw [← map_zero Fp12.ofFpHom]
  exact pairing_generators_ne_ofFp_zero_and_ne_one.1

/-- The pairing of `P1` and `P2` is not 1. -/
theorem pairing_generators_ne_one : pairing Point.generator Point2.generator ≠ 1 :=
  pairing_generators_ne_ofFp_zero_and_ne_one.2

/-- The final exponent times `q` is `p^12 - 1`. -/
theorem finalExponent_mul_modulus : FINAL_EXPONENT * Fr.modulus = Fp.modulus ^ 12 - 1 :=
  Nat.div_mul_cancel (by decide +kernel)

/-- Every nonzero output of the final exponentiation is a `q`-th root of unity. -/
theorem finalExponentiation_pow_modulus {f : Fp12} (h : finalExponentiation f ≠ 0) :
    finalExponentiation f ^ Fr.modulus = 1 := by
  have hf : f ≠ 0 := by
    rintro rfl
    exact h (by rw [finalExponentiation_eq_pow, zero_pow (by decide)])
  rw [finalExponentiation_eq_pow, ← pow_mul, finalExponent_mul_modulus, ← Fp12.card_eq]
  exact FiniteField.pow_card_sub_one_eq_one f hf

/-- The pairing of `P1` and `P2` has order `q`. -/
theorem orderOf_pairing_generators :
    orderOf (pairing Point.generator Point2.generator) = Fr.modulus := by
  have h : pairing Point.generator Point2.generator =
      finalExponentiation (millerLoop Point2.generator 1 2) := rfl
  apply orderOf_eq_prime
  · rw [h]
    exact finalExponentiation_pow_modulus (h ▸ pairing_generators_ne_zero)
  · exact pairing_generators_ne_one

end EthLib.Cryptography.AltBn128
