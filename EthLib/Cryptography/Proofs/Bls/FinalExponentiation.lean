module

public import EthLib.Cryptography.Bls.Pairing
public import EthLib.Cryptography.Proofs.Bls.TwistFrobenius

/-!
# Proofs: the final exponentiation

The final exponentiation raises its argument to `(p^12 - 1) / r`.

It reaches that power with conjugates, Frobenius maps, one inverse and powers by small exponents.

Each of these steps is a power of its argument, so the result is a power `f^n` of the argument.

The exponent `n` agrees with `(p^12 - 1) / r` modulo `p^12 - 1`.

`Fp12` has `p^12` elements, so both powers are equal.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

open TwistFrobenius

namespace Fp12

/-- An element is the sum of its six `Fp2` coefficients times the powers of `w`. -/
theorem eq_sum (a : Fp12) :
    a = fp2ToFp12 a.c0.c0 + fp2ToFp12 a.c1.c0 * w + fp2ToFp12 a.c0.c1 * w ^ 2 +
      fp2ToFp12 a.c1.c1 * w ^ 3 + fp2ToFp12 a.c0.c2 * w ^ 4 + fp2ToFp12 a.c1.c2 * w ^ 5 := by
  have hw2 : w ^ 2 = ⟨Fp6.v, 0⟩ := w_squared
  have hw3 : w ^ 3 = ⟨0, Fp6.v⟩ := by rw [pow_succ, hw2]; apply Fp12.ext <;> simp [w]
  have hw4 : w ^ 4 = ⟨Fp6.v * Fp6.v, 0⟩ := by
    rw [show 4 = 2 * 2 by rfl, pow_mul, hw2, pow_two]; apply Fp12.ext <;> simp
  have hw5 : w ^ 5 = ⟨0, Fp6.v * Fp6.v⟩ := by
    rw [pow_succ, hw4]; apply Fp12.ext <;> simp [w, Fp6.mulByV_eq]
  rw [hw2, hw3, hw4, hw5]
  apply Fp12.ext <;> apply Fp6.ext <;>
    simp [w, Fp6.mulByV_eq, Fp2.mulByOnePlusI_eq]

private theorem frobeniusCoeff_eq : frobeniusCoeff = Fp2.xi ^ ((Fp.modulus - 1) / 6) := by
  unfold frobeniusCoeff
  rw [Fp2.powNat_eq_pow]
  rfl

/-- `w^p = γ w`, since `w^6 = ξ`. -/
private theorem primeFrobenius_w : primeFrobenius w = fp2ToFp12 frobeniusCoeff * w := by
  rw [primeFrobenius_apply, show Fp.modulus = 6 * ((Fp.modulus - 1) / 6) + 1 by decide,
    pow_succ, pow_mul, w_sixth, ← map_pow, frobeniusCoeff_eq]

/-- The Frobenius map is the `p`-th power. -/
theorem frobenius_eq_pow (a : Fp12) : a.frobenius = a ^ Fp.modulus := by
  rw [← primeFrobenius_apply]
  conv_rhs => rw [eq_sum a]
  rw [eq_sum a.frobenius]
  simp only [map_add, map_mul, map_pow, primeFrobenius_fp2, primeFrobenius_w, frobenius]
  ring

/-- `ξ` is not a square in `Fp2`, so by Euler's criterion this power is `-1`.

The kernel computes it. -/
theorem xi_pow_half : Fp2.xi ^ ((Fp.modulus ^ 2 - 1) / 2) = -1 := by
  rw [← Fp2.powNat_eq_pow]
  decide +kernel

/-- `w^(p^6) = -w`. -/
private theorem w_pow_p6 : w ^ (Fp.modulus ^ 6) = -w := by
  rw [show Fp.modulus ^ 6 = 6 * ((Fp.modulus ^ 2 - 1) / 2 *
      (2 * ((Fp.modulus ^ 4 + Fp.modulus ^ 2 - 2) / 6) + 1)) + 1 by decide,
    pow_succ, pow_mul, w_sixth, ← map_pow, pow_mul, xi_pow_half, pow_succ, pow_mul, neg_one_sq,
    one_pow, one_mul, map_neg, map_one, neg_one_mul]

/-- The `p^6`-th power, a ring map. -/
private noncomputable def frobenius6 : Fp12 →+* Fp12 := primeFrobenius ^ 6

private theorem frobenius6_apply (a : Fp12) : frobenius6 a = a ^ (Fp.modulus ^ 6) := by
  have h (n : Nat) (b : Fp12) : (⇑primeFrobenius)^[n] b = b ^ (Fp.modulus ^ n) := by
    induction n generalizing b with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ih, primeFrobenius_apply, ← pow_mul, pow_succ]
  rw [frobenius6, RingHom.coe_pow, h]

/-- The conjugate is the `p^6`-th power. -/
theorem conjugate_eq_pow (a : Fp12) : a.conjugate = a ^ (Fp.modulus ^ 6) := by
  have hfix (x : Fp2) : frobenius6 (fp2ToFp12 x) = fp2ToFp12 x := by
    rw [frobenius6_apply, ← map_pow, show Fp.modulus ^ 6 = (Fp.modulus ^ 2) ^ 3 by ring,
      ← card_fp2, FiniteField.pow_card_pow]
  have hw : frobenius6 w = -w := by rw [frobenius6_apply, w_pow_p6]
  rw [← frobenius6_apply]
  conv_rhs => rw [eq_sum a]
  rw [eq_sum a.conjugate]
  simp only [map_add, map_mul, map_pow, hfix, hw, conjugate_c0, conjugate_c1, Fp6.neg_c0,
    Fp6.neg_c1, Fp6.neg_c2, map_neg]
  ring

/-- In a finite field the inverse is the power by the order minus two. -/
private theorem inverse_eq_pow (f : Fp12) : f.inverse = f ^ (Fp.modulus ^ 12 - 2) := by
  by_cases hf : f = 0
  · rw [hf, inverse_zero, zero_pow (by decide)]
  · have h1 : f ^ (Fp.modulus ^ 12 - 2) * f = 1 := by
      rw [← pow_succ, show Fp.modulus ^ 12 - 2 + 1 = Fintype.card Fp12 - 1 by
        rw [card_fp12]; decide]
      exact FiniteField.pow_card_sub_one_eq_one f hf
    exact (eq_inv_of_mul_eq_one_left h1).symm

/-- Two positive exponents that agree modulo `p^12 - 1` give the same power. -/
private theorem pow_eq_pow_of_mod {f : Fp12} {m n : Nat} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : m % (Fp.modulus ^ 12 - 1) = n % (Fp.modulus ^ 12 - 1)) : f ^ m = f ^ n := by
  by_cases hf : f = 0
  · rw [hf, zero_pow hm, zero_pow hn]
  · have h1 : f ^ (Fp.modulus ^ 12 - 1) = 1 := by
      rw [← card_fp12]
      exact FiniteField.pow_card_sub_one_eq_one f hf
    rw [← Nat.div_add_mod m (Fp.modulus ^ 12 - 1), ← Nat.div_add_mod n (Fp.modulus ^ 12 - 1),
      pow_add, pow_add, pow_mul, pow_mul, h1, one_pow, one_pow, h]

end Fp12

/-- The final exponentiation raises its argument to `(p^12 - 1) / r`. -/
theorem finalExponentiation_eq_pow (f : Fp12) : finalExponentiation f = f ^ finalExpExponent := by
  unfold finalExponentiation
  simp only [Fp12.inverse_eq_pow, Fp12.conjugate_eq_pow, Fp12.frobenius_eq_pow,
    Fp12.powNat_eq_pow, ← pow_mul, ← pow_add]
  -- Both exponents are numbers; the kernel compares them modulo `p^12 - 1`.
  exact Fp12.pow_eq_pow_of_mod (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The final exponentiation is multiplicative. -/
theorem finalExponentiation_mul (a b : Fp12) :
    finalExponentiation (a * b) = finalExponentiation a * finalExponentiation b := by
  rw [finalExponentiation_eq_pow, finalExponentiation_eq_pow, finalExponentiation_eq_pow,
    mul_pow]

/-- The final exponentiation sends `c w^3` to 1, for every nonzero `c` in `Fp2`.

Both factors are units of the subfield `Fp2[w^3]` of `p^4` elements.

And `p^4 - 1` divides the final exponent. -/
theorem finalExponentiation_fp2_mul_w_cube {c : Fp2} (hc : c ≠ 0) :
    finalExponentiation (fp2ToFp12 c * w ^ 3) = 1 := by
  have hc2 : c ^ (Fp.modulus ^ 2 - 1) = 1 := by
    rw [← card_fp2]
    exact FiniteField.pow_card_sub_one_eq_one c hc
  have hc4 : c ^ (Fp.modulus ^ 4 - 1) = 1 := by
    rw [show Fp.modulus ^ 4 - 1 = (Fp.modulus ^ 2 - 1) * (Fp.modulus ^ 2 + 1) by decide,
      pow_mul, hc2, one_pow]
  have hw4 : (w ^ 3) ^ (Fp.modulus ^ 4 - 1) = 1 := by
    have h4 : Fp.modulus ^ 4 - 1 =
        4 * ((Fp.modulus ^ 2 - 1) / 2 * ((Fp.modulus ^ 2 + 1) / 2)) := by decide
    have h12 : 3 * (4 * ((Fp.modulus ^ 2 - 1) / 2 * ((Fp.modulus ^ 2 + 1) / 2))) =
        6 * ((Fp.modulus ^ 2 - 1) / 2 * (2 * ((Fp.modulus ^ 2 + 1) / 2))) := by ring
    rw [h4, ← pow_mul, h12, pow_mul, w_sixth, ← map_pow, pow_mul, Fp12.xi_pow_half, pow_mul,
      neg_one_sq, one_pow, map_one]
  rw [finalExponentiation_eq_pow, show finalExpExponent = (Fp.modulus ^ 4 - 1) *
      (finalExpExponent / (Fp.modulus ^ 4 - 1)) by decide +kernel, pow_mul, mul_pow, ← map_pow,
    hc4, hw4, map_one, one_mul, one_pow]

end EthLib.Cryptography.Bls
