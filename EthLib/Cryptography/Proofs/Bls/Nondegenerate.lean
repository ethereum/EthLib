module

public import EthLib.Cryptography.Proofs.Bls.FinalExponentiation
public import EthLib.Cryptography.Proofs.Bls.FrZMod
public import EthLib.Cryptography.Proofs.Bls.PairingCongr

/-!
# Proofs: the pairing is not degenerate

The pairing of the two generators is neither 0 nor 1, and its order is the prime `r`.

`G1` and `G2` are cyclic, so a bilinear map that is not 1 on the generators is not degenerate.

The kernel evaluates the pairing of the generators; each check takes a few seconds.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

/-- The pairing of the generators is not 1. -/
theorem pairing_generators_ne_one : pairing G1.generator G2.generator ≠ 1 := by
  decide +kernel

/-- The pairing of the generators is not 0. -/
theorem pairing_generators_ne_zero : pairing G1.generator G2.generator ≠ 0 := by
  decide +kernel

/-- Every nonzero output of the final exponentiation is an `r`-th root of unity. -/
theorem finalExponentiation_pow_modulus {f : Fp12} (h : finalExponentiation f ≠ 0) :
    finalExponentiation f ^ Fr.modulus = 1 := by
  have hf : f ≠ 0 := by
    rintro rfl
    exact h (by rw [finalExponentiation_eq_pow, zero_pow (by decide)])
  rw [finalExponentiation_eq_pow, ← pow_mul,
    show finalExpExponent * Fr.modulus = Fintype.card Fp12 - 1 by
      rw [TwistFrobenius.card_fp12]; decide]
  exact FiniteField.pow_card_sub_one_eq_one f hf

/-- The pairing of the generators has order `r`. -/
theorem orderOf_pairing_generators : orderOf (pairing G1.generator G2.generator) = Fr.modulus := by
  apply orderOf_eq_prime
  · have h := pairing_generators_ne_zero
    unfold pairing at h ⊢
    simp only [show (G1.generator.isInfinity || G2.generator.isInfinity) = false by decide,
      Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact finalExponentiation_pow_modulus h
  · exact pairing_generators_ne_one

/-- The pairing check of the generators fails. -/
theorem pairingCheck_generators : pairingCheck #[(G1.generator, G2.generator)] = false := by
  have h := pairing_generators_ne_one
  rw [pairingCheck_eq_finalExp_prod, Bool.eq_false_iff]
  intro h1
  apply h
  rw [Fp12.isOne_iff] at h1
  unfold pairing
  simpa [pairFactor, show (G1.generator.isInfinity || G2.generator.isInfinity) = false by decide]
    using h1

end EthLib.Cryptography.Bls
