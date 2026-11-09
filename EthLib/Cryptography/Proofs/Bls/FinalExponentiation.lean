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
  simp only [_root_.map_add, _root_.map_mul, map_pow, primeFrobenius_fp2, primeFrobenius_w,
    frobenius]
  ring

/-- `ξ` is not a square in `Fp2`, so by Euler's criterion this power is `-1`.

The kernel computes it. -/
theorem xi_pow_half : Fp2.xi ^ ((Fp.modulus ^ 2 - 1) / 2) = -1 := by
  decide_eq_at_model [Fp2.xi]

/-- `w^(p^6) = -w`. -/
private theorem w_pow_p6 : w ^ (Fp.modulus ^ 6) = -w := by
  rw [show Fp.modulus ^ 6 = 6 * ((Fp.modulus ^ 2 - 1) / 2 *
      (2 * ((Fp.modulus ^ 4 + Fp.modulus ^ 2 - 2) / 6) + 1)) + 1 by decide,
    pow_succ, pow_mul, w_sixth, ← map_pow, pow_mul, xi_pow_half, pow_succ, pow_mul, neg_one_sq,
    one_pow, one_mul, _root_.map_neg, _root_.map_one, neg_one_mul]

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
  simp only [_root_.map_add, _root_.map_mul, map_pow, hfix, hw, conjugate_c0, conjugate_c1,
    Fp6.neg_c0, Fp6.neg_c1, Fp6.neg_c2, _root_.map_neg]
  ring

/-! ## Cyclotomic squaring

The proof uses the relation `a^(p^4) * a = a^(p^2)`, from [Granger and Scott][source], §3.2.

It is equation (5) there, and it holds on the cyclotomic subgroup and at zero.

[source]: https://eprint.iacr.org/2009/565
-/

attribute [local irreducible] frobeniusCoeff

private def cyclotomicCoeff : Fp2 := (frobeniusCoeff : Fp2).conjugate * frobeniusCoeff

private theorem frobenius2_certificate {R : Type*} [Field R] (c : R → R)
    (hmul : ∀ x y, c (x * y) = c x * c y) (hinv : ∀ x, c (c x) = x)
    (g z0 z2 z4 z1 z3 z5 : R) :
    let g2 := g * g
    let g3 := g2 * g
    c (c z0) = z0 ∧
      c (c z2 * g2) * g2 = z2 * (c g * g) ^ 2 ∧
      c (c z4 * (g2 * g2)) * (g2 * g2) = z4 * (c g * g) ^ 4 ∧
      c (c z1 * g) * g = z1 * (c g * g) ∧
      c (c z3 * g3) * g3 = z3 * (c g * g) ^ 3 ∧
      c (c z5 * (g3 * g2)) * (g3 * g2) = z5 * (c g * g) ^ 5 := by
  dsimp only
  repeat' constructor
  all_goals simp only [hmul, hinv, pow_succ, pow_zero]
  all_goals ac_rfl

private theorem frobenius2_coordinates (a : Fp12) :
    a.frobenius.frobenius =
      ⟨⟨a.c0.c0, a.c0.c1 * cyclotomicCoeff ^ 2, a.c0.c2 * cyclotomicCoeff ^ 4⟩,
        ⟨a.c1.c0 * cyclotomicCoeff, a.c1.c1 * cyclotomicCoeff ^ 3, a.c1.c2 * cyclotomicCoeff ^ 5⟩⟩
          := by
  have h := frobenius2_certificate Fp2.conjugate Fp2.conjugate_mul
    Fp2.conjugate_conjugate (frobeniusCoeff : Fp2)
    a.c0.c0 a.c0.c1 a.c0.c2 a.c1.c0 a.c1.c1 a.c1.c2
  exact congrArg₂ Fp12.mk
    (congr (congr (congrArg Fp6.mk h.1) h.2.1) h.2.2.1)
    (congr (congr (congrArg Fp6.mk h.2.2.2.1) h.2.2.2.2.1) h.2.2.2.2.2)

private theorem cyclotomicCoeff_quadratic :
    cyclotomicCoeff ^ 2 - cyclotomicCoeff + 1 = 0 := by
  decide_eq_at_model [cyclotomicCoeff, frobeniusCoeff]

private theorem frobenius2_power_coordinates (a : Fp12) :
    a ^ (Fp.modulus ^ 2) =
      ⟨⟨a.c0.c0, a.c0.c1 * cyclotomicCoeff ^ 2, a.c0.c2 * cyclotomicCoeff ^ 4⟩,
        ⟨a.c1.c0 * cyclotomicCoeff, a.c1.c1 * cyclotomicCoeff ^ 3,
          a.c1.c2 * cyclotomicCoeff ^ 5⟩⟩ := by
  rw [← frobenius2_coordinates, frobenius_eq_pow, frobenius_eq_pow, ← pow_mul, pow_two]

private theorem quadratic_nonzero {K : Type} [Field K]
    (d : K) (hd : d ^ 2 - d + 1 = 0) : d ≠ 0 ∧ d - 1 ≠ 0 := by
  constructor
  · intro hz
    rw [hz] at hd
    norm_num at hd
  · intro hz
    rw [sub_eq_zero.mp hz] at hd
    norm_num at hd

private theorem quadratic_comp {K : Type} [Field K]
    (d a2 a4 a1 a5 : K) (hd : d ^ 2 - d + 1 = 0) :
    ((a2 * (d - 1)) * (d - 1) = -a2 * d) ∧
      (-(-a4 * d) * d = a4 * (d - 1)) ∧
      ((a1 * d) * d = a1 * (d - 1)) ∧
      ((a5 * (1 - d)) * (1 - d) = -a5 * d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination a2 * hd
  · linear_combination a4 * hd
  · linear_combination a1 * hd
  · linear_combination a5 * hd

private theorem square_coordinates {K : Type} [Field K]
    (d u a0 a1 a2 a3 a4 a5 : K) (hd : d ^ 2 - d + 1 = 0)
    (h0 : ((-a2 * d + a4 * (d - 1)) * (a2 + a4) - -a2 * d * a2 - a4 * (d - 1) * a4) * u + a0 * a0 +
      ((a1 * (d - 1) + -a5 * d) * (a1 + a5) - a1 * (d - 1) * a1 - -a5 * d * a5 + a3 * a3) * u =
    a0)
    (h1 : ((-a2 * d + a3 + (a4 * (d - 1) + -a5 * d)) * (a2 + a3 + (a4 + a5)) - (-a2 * d + a3) * (a2
      + a3) -
              (a4 * (d - 1) + -a5 * d) * (a4 + a5)) *
            u +
          (a0 + a1 * (d - 1)) * (a0 + a1) -
        (((-a2 * d + a4 * (d - 1)) * (a2 + a4) - -a2 * d * a2 - a4 * (d - 1) * a4) * u + a0 * a0) -
      (((a3 + -a5 * d) * (a3 + a5) - a3 * a3 - -a5 * d * a5) * u + a1 * (d - 1) * a1) =
    a1 * d)
    (h2 : (a0 + -a2 * d) * (a0 + a2) - a0 * a0 - -a2 * d * a2 + a4 * (d - 1) * a4 * u +
      (((a3 + -a5 * d) * (a3 + a5) - a3 * a3 - -a5 * d * a5) * u + a1 * (d - 1) * a1) =
    a2 * (d - 1))
    (h3 : (a0 + a1 * (d - 1) + (-a2 * d + a3)) * (a0 + a1 + (a2 + a3)) - (a0 + a1 * (d - 1)) * (a0 +
      a1) -
            (-a2 * d + a3) * (a2 + a3) +
          (a4 * (d - 1) + -a5 * d) * (a4 + a5) * u -
        ((a0 + -a2 * d) * (a0 + a2) - a0 * a0 - -a2 * d * a2 + a4 * (d - 1) * a4 * u) -
      ((a1 * (d - 1) + a3) * (a1 + a3) - a1 * (d - 1) * a1 - a3 * a3 + -a5 * d * a5 * u) =
    -a3)
    (h4 : (a0 + a4 * (d - 1)) * (a0 + a4) - a0 * a0 - a4 * (d - 1) * a4 + -a2 * d * a2 +
      ((a1 * (d - 1) + a3) * (a1 + a3) - a1 * (d - 1) * a1 - a3 * a3 + -a5 * d * a5 * u) =
    -a4 * d)
    (h5 : (a0 + a1 * (d - 1) + (a4 * (d - 1) + -a5 * d)) * (a0 + a1 + (a4 + a5)) - (a0 + a1 * (d -
      1)) * (a0 + a1) -
            (a4 * (d - 1) + -a5 * d) * (a4 + a5) +
          (-a2 * d + a3) * (a2 + a3) -
        ((a0 + a4 * (d - 1)) * (a0 + a4) - a0 * a0 - a4 * (d - 1) * a4 + -a2 * d * a2) -
      ((a1 * (d - 1) + -a5 * d) * (a1 + a5) - a1 * (d - 1) * a1 - -a5 * d * a5 + a3 * a3) =
    a5 * (1 - d))
    : ((a0 + a3 * u) * (a0 + a3) - a0 * a3 - a0 * a3 * u - a0 +
        ((a0 + a3 * u) * (a0 + a3) - a0 * a3 - a0 * a3 * u - a0) +
      ((a0 + a3 * u) * (a0 + a3) - a0 * a3 - a0 * a3 * u) =
    ((a2 + a4) * (a2 + a4) - a2 * a2 - a4 * a4) * u + a0 * a0 +
      ((a1 + a5) * (a1 + a5) - a1 * a1 - a5 * a5 + a3 * a3) * u) ∧
    ((a1 + a4 * u) * (a1 + a4) - a1 * a4 - a1 * a4 * u - a2 +
        ((a1 + a4 * u) * (a1 + a4) - a1 * a4 - a1 * a4 * u - a2) +
      ((a1 + a4 * u) * (a1 + a4) - a1 * a4 - a1 * a4 * u) =
    (a0 + a2) * (a0 + a2) - a0 * a0 - a2 * a2 + a4 * a4 * u +
      (((a3 + a5) * (a3 + a5) - a3 * a3 - a5 * a5) * u + a1 * a1)) ∧
    ((a2 + a5 * u) * (a2 + a5) - a2 * a5 - a2 * a5 * u - a4 +
        ((a2 + a5 * u) * (a2 + a5) - a2 * a5 - a2 * a5 * u - a4) +
      ((a2 + a5 * u) * (a2 + a5) - a2 * a5 - a2 * a5 * u) =
    (a0 + a4) * (a0 + a4) - a0 * a0 - a4 * a4 + a2 * a2 + ((a1 + a3) * (a1 + a3) - a1 * a1 - a3 * a3
      + a5 * a5 * u)) ∧
    ((a2 * a5 + a2 * a5) * u + a1 + ((a2 * a5 + a2 * a5) * u + a1) + (a2 * a5 + a2 * a5) * u =
    ((a2 + a3 + (a4 + a5)) * (a2 + a3 + (a4 + a5)) - (a2 + a3) * (a2 + a3) - (a4 + a5) * (a4 + a5))
      * u +
          (a0 + a1) * (a0 + a1) -
        (((a2 + a4) * (a2 + a4) - a2 * a2 - a4 * a4) * u + a0 * a0) -
      (((a3 + a5) * (a3 + a5) - a3 * a3 - a5 * a5) * u + a1 * a1)) ∧
    (a0 * a3 + a0 * a3 + a3 + (a0 * a3 + a0 * a3 + a3) + (a0 * a3 + a0 * a3) =
    (a0 + a1 + (a2 + a3)) * (a0 + a1 + (a2 + a3)) - (a0 + a1) * (a0 + a1) - (a2 + a3) * (a2 + a3) +
          (a4 + a5) * (a4 + a5) * u -
        ((a0 + a2) * (a0 + a2) - a0 * a0 - a2 * a2 + a4 * a4 * u) -
      ((a1 + a3) * (a1 + a3) - a1 * a1 - a3 * a3 + a5 * a5 * u)) ∧
    (a1 * a4 + a1 * a4 + a5 + (a1 * a4 + a1 * a4 + a5) + (a1 * a4 + a1 * a4) =
    (a0 + a1 + (a4 + a5)) * (a0 + a1 + (a4 + a5)) - (a0 + a1) * (a0 + a1) - (a4 + a5) * (a4 + a5) +
          (a2 + a3) * (a2 + a3) -
        ((a0 + a4) * (a0 + a4) - a0 * a0 - a4 * a4 + a2 * a2) -
      ((a1 + a5) * (a1 + a5) - a1 * a1 - a5 * a5 + a3 * a3)) := by
  have r0 : a0 * a0 + u * a3 * a3 - a0 - u * a1 * a5 -
      u * a2 * a4 = 0 := by linear_combination h0
  have r3 : 2 * a0 * a3 - a1 * a2 - u * a4 * a5 + a3 = 0 := by
    linear_combination h3
  have r1 : d * (a0 * a1 - 2 * u * a2 * a5 + u * a3 * a4 - a1) = 0 := by
    linear_combination h1
  have r4 : d * (a0 * a4 + a1 * a3 - a2 * a2 - u * a5 * a5 + a4) = 0 := by
    linear_combination h4
  have r2 : (d - 1) * (-a0 * a2 + a1 * a1 - u * a3 * a5 +
      u * a4 * a4 - a2) = 0 := by linear_combination h2
  have r5 : (d - 1) * (-a0 * a5 + 2 * a1 * a4 - a2 * a3 + a5) = 0 := by
    linear_combination h5
  obtain ⟨hd0, hd1⟩ := quadratic_nonzero d hd
  replace r1 := (mul_eq_zero.mp r1).resolve_left hd0
  replace r4 := (mul_eq_zero.mp r4).resolve_left hd0
  replace r2 := (mul_eq_zero.mp r2).resolve_left hd1
  replace r5 := (mul_eq_zero.mp r5).resolve_left hd1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination 2 * r0
  · linear_combination 2 * r2
  · linear_combination -2 * r4
  · linear_combination -2 * r1
  · linear_combination 2 * r3
  · linear_combination 2 * r5

private def frobenius2Form (d : Fp2) (a : Fp12) : Fp12 :=
  ⟨⟨a.c0.c0, a.c0.c1 * (d - 1), -a.c0.c2 * d⟩,
    ⟨a.c1.c0 * d, -a.c1.c1, a.c1.c2 * (1 - d)⟩⟩

private def frobenius4Form (d : Fp2) (a : Fp12) : Fp12 :=
  ⟨⟨a.c0.c0, -a.c0.c1 * d, a.c0.c2 * (d - 1)⟩,
    ⟨a.c1.c0 * (d - 1), a.c1.c1, -a.c1.c2 * d⟩⟩

private theorem frobenius2Form_comp (d : Fp2) (hd : d ^ 2 - d + 1 = 0) (a : Fp12) :
    frobenius2Form d (frobenius2Form d a) = frobenius4Form d a := by
  obtain ⟨⟨a0, a2, a4⟩, ⟨a1, a3, a5⟩⟩ := a
  have hc := quadratic_comp d a2 a4 a1 a5 hd
  apply Fp12.ext <;> apply Fp6.ext <;> dsimp only [frobenius2Form, frobenius4Form]
  · exact hc.1
  · exact hc.2.1
  · exact hc.2.2.1
  · exact neg_neg a3
  · exact hc.2.2.2

private theorem cyclotomicSquare_of_coordinate_relation (d : Fp2)
    (hd : d ^ 2 - d + 1 = 0) (a : Fp12)
    (h : frobenius4Form d a * a = frobenius2Form d a) :
    a.cyclotomicSquare = a * a := by
  obtain ⟨⟨a0, a2, a4⟩, ⟨a1, a3, a5⟩⟩ := a
  have h0 := congrArg (fun z : Fp12 => z.c0.c0) h
  have h1 := congrArg (fun z : Fp12 => z.c1.c0) h
  have h2 := congrArg (fun z : Fp12 => z.c0.c1) h
  have h3 := congrArg (fun z : Fp12 => z.c1.c1) h
  have h4 := congrArg (fun z : Fp12 => z.c0.c2) h
  have h5 := congrArg (fun z : Fp12 => z.c1.c2) h
  simp only [frobenius2Form, frobenius4Form, mul_c0, mul_c1,
    Fp6.mul_c0, Fp6.mul_c1, Fp6.mul_c2, Fp6.mulByV,
    Fp6.add_c0, Fp6.add_c1, Fp6.add_c2, Fp6.sub_c0, Fp6.sub_c1, Fp6.sub_c2,
    Fp2.mulByOnePlusI_eq] at h0 h1 h2 h3 h4 h5
  have hc := square_coordinates d Fp2.xi a0 a1 a2 a3 a4 a5 hd h0 h1 h2 h3 h4 h5
  apply Fp12.ext <;> apply Fp6.ext <;>
    simp only [cyclotomicSquare, mul_c0, mul_c1, Fp6.mul_c0, Fp6.mul_c1, Fp6.mul_c2,
      Fp6.mulByV, Fp6.add_c0, Fp6.add_c1, Fp6.add_c2, Fp6.sub_c0, Fp6.sub_c1,
      Fp6.sub_c2, Fp2.mulByOnePlusI_eq]
  · exact hc.1
  · exact hc.2.1
  · exact hc.2.2.1
  · exact hc.2.2.2.1
  · exact hc.2.2.2.2.1
  · exact hc.2.2.2.2.2

private theorem quadratic_scaled_powers {K : Type} [Field K]
    (d a2 a4 a3 a5 : K) (hd : d ^ 2 - d + 1 = 0) :
    a2 * d ^ 2 = a2 * (d - 1) ∧ a4 * d ^ 4 = -a4 * d ∧
      a3 * d ^ 3 = -a3 ∧ a5 * d ^ 5 = a5 * (1 - d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination a2 * hd
  · linear_combination a4 * (d * d + d) * hd
  · linear_combination a3 * (d + 1) * hd
  · linear_combination a5 * (d ^ 2 * d + d * d - 1) * hd

private theorem frobenius2Form_of_powers (d : Fp2) (hd : d ^ 2 - d + 1 = 0) (a : Fp12) :
    (⟨⟨a.c0.c0, a.c0.c1 * d ^ 2, a.c0.c2 * d ^ 4⟩,
      ⟨a.c1.c0 * d, a.c1.c1 * d ^ 3, a.c1.c2 * d ^ 5⟩⟩ : Fp12) =
      frobenius2Form d a := by
  have hc := quadratic_scaled_powers d a.c0.c1 a.c0.c2 a.c1.c1 a.c1.c2 hd
  exact congrArg₂ Fp12.mk
    (congrArg₂ (fun x y => Fp6.mk a.c0.c0 x y) hc.1 hc.2.1)
    (congrArg₂ (fun x y => Fp6.mk (a.c1.c0 * d) x y) hc.2.2.1 hc.2.2.2)

private theorem square_correct_of_coefficients (d : Fp2) (hd : d ^ 2 - d + 1 = 0)
    (coordinates : ∀ a : Fp12,
      a ^ (Fp.modulus ^ 2) =
        ⟨⟨a.c0.c0, a.c0.c1 * d ^ 2, a.c0.c2 * d ^ 4⟩,
          ⟨a.c1.c0 * d, a.c1.c1 * d ^ 3, a.c1.c2 * d ^ 5⟩⟩)
    (a : Fp12) (ha : a ^ (Fp.modulus ^ 4) * a = a ^ (Fp.modulus ^ 2)) :
    a.cyclotomicSquare = a * a := by
  have h2 (x : Fp12) : x ^ (Fp.modulus ^ 2) = frobenius2Form d x :=
    (coordinates x).trans (frobenius2Form_of_powers d hd x)
  have h4 : a ^ (Fp.modulus ^ 4) = frobenius4Form d a := by
    calc
      a ^ (Fp.modulus ^ 4) = (a ^ (Fp.modulus ^ 2)) ^ (Fp.modulus ^ 2) := by
        rw [← pow_mul, show Fp.modulus ^ 2 * Fp.modulus ^ 2 = Fp.modulus ^ 4 by ring]
      _ = frobenius2Form d (frobenius2Form d a) := by rw [h2, h2]
      _ = frobenius4Form d a := frobenius2Form_comp d hd a
  apply cyclotomicSquare_of_coordinate_relation d hd a
  rw [← h4, ← h2]
  exact ha

/-- The cyclotomic square is a square under the `p^2`-power relation, including zero. -/
theorem cyclotomicSquare_eq_mul_self {a : Fp12}
    (ha : a ^ (Fp.modulus ^ 4) * a = a ^ (Fp.modulus ^ 2)) :
    a.cyclotomicSquare = a * a :=
  square_correct_of_coefficients cyclotomicCoeff cyclotomicCoeff_quadratic
    frobenius2_power_coordinates a ha

/-- Elements of order dividing `p^4 - p^2 + 1` satisfy the cyclotomic square formula. -/
theorem cyclotomicSquare_eq_mul_self_of_order {a : Fp12}
    (ha : a ^ (Fp.modulus ^ 4 - Fp.modulus ^ 2 + 1) = 1) :
    a.cyclotomicSquare = a * a := by
  apply cyclotomicSquare_eq_mul_self
  rw [← pow_succ, show Fp.modulus ^ 4 + 1 =
    Fp.modulus ^ 2 + (Fp.modulus ^ 4 - Fp.modulus ^ 2 + 1) by decide +kernel,
    pow_add, ha, mul_one]

/-- The cyclotomic square sends zero to zero. -/
@[simp] theorem cyclotomicSquare_zero : cyclotomicSquare (0 : Fp12) = 0 := by
  rw [cyclotomicSquare_eq_mul_self (by
    rw [zero_pow (by decide), zero_pow (by decide), zero_mul]), zero_mul]

private theorem cyclotomic_relation_pow {a : Fp12}
    (h : a ^ (Fp.modulus ^ 4) * a = a ^ (Fp.modulus ^ 2)) (n : Nat) :
    (a ^ n) ^ (Fp.modulus ^ 4) * a ^ n = (a ^ n) ^ (Fp.modulus ^ 2) := by
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm] using congrArg (fun x => x ^ n) h

private theorem cyclotomic_relation_mul {a b : Fp12}
    (ha : a ^ (Fp.modulus ^ 4) * a = a ^ (Fp.modulus ^ 2))
    (hb : b ^ (Fp.modulus ^ 4) * b = b ^ (Fp.modulus ^ 2)) :
    (a * b) ^ (Fp.modulus ^ 4) * (a * b) = (a * b) ^ (Fp.modulus ^ 2) := by
  rw [mul_pow, mul_pow]
  calc
    a ^ (Fp.modulus ^ 4) * b ^ (Fp.modulus ^ 4) * (a * b) =
        (a ^ (Fp.modulus ^ 4) * a) * (b ^ (Fp.modulus ^ 4) * b) := by ac_rfl
    _ = a ^ (Fp.modulus ^ 2) * b ^ (Fp.modulus ^ 2) := by rw [ha, hb]

/-- Cyclotomic exponentiation is exponentiation under the `p^2`-power relation. -/
theorem cyclotomicPow_eq_pow
    {a : Fp12} (ha : a ^ (Fp.modulus ^ 4) * a = a ^ (Fp.modulus ^ 2)) (e : Nat) :
    cyclotomicPow a e = a ^ e := by
  induction e using Nat.strongRecOn generalizing a with
  | _ e ih =>
    rw [cyclotomicPow]
    split
    · rename_i he
      subst he
      rw [pow_zero, one_eq_one]
    · rename_i he
      rw [cyclotomicSquare_eq_mul_self ha]
      rw [ih (e / 2) (by omega) (cyclotomic_relation_mul ha ha)]
      by_cases h2 : e % 2 = 1
      · rw [ite_eq_left h2, ← pow_two, ← pow_mul, ← pow_succ']
        congr 1
        omega
      · rw [ite_eq_right h2, ← pow_two, ← pow_mul]
        congr 1
        omega

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


private theorem cyclotomic_relation_frobenius {a : Fp12}
    (h : a ^ (Fp.modulus ^ 4) * a = a ^ (Fp.modulus ^ 2)) :
    a.frobenius ^ (Fp.modulus ^ 4) * a.frobenius =
      a.frobenius ^ (Fp.modulus ^ 2) := by
  rw [frobenius_eq_pow]
  exact cyclotomic_relation_pow h _

private theorem cyclotomic_relation_conjugate {a : Fp12}
    (h : a ^ (Fp.modulus ^ 4) * a = a ^ (Fp.modulus ^ 2)) :
    a.conjugate ^ (Fp.modulus ^ 4) * a.conjugate =
      a.conjugate ^ (Fp.modulus ^ 2) := by
  rw [conjugate_eq_pow]
  exact cyclotomic_relation_pow h _

/-- The easy part satisfies the cyclotomic relation, including when its input is zero. -/
private theorem easy_part_cyclotomic_relation (f : Fp12) :
    let t := f.conjugate * f.inverse
    let m := t.frobenius.frobenius * t
    m ^ (Fp.modulus ^ 4) * m = m ^ (Fp.modulus ^ 2) := by
  dsimp only
  simp only [inverse_eq_pow, conjugate_eq_pow, frobenius_eq_pow, ← pow_mul, ← pow_add]
  exact pow_eq_pow_of_mod (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Fp12

/-- The final exponentiation raises its argument to `(p^12 - 1) / r`. -/
theorem finalExponentiation_eq_pow (f : Fp12) : finalExponentiation f = f ^ finalExpExponent := by
  unfold finalExponentiation
  extract_lets t m a b c
  have hm : m ^ (Fp.modulus ^ 4) * m = m ^ (Fp.modulus ^ 2) :=
    Fp12.easy_part_cyclotomic_relation f
  have haEq : a = (m ^ ((blsX + 1) / 3)) ^ (blsX + 1) := by
    dsimp only [a]
    rw [Fp12.cyclotomicPow_eq_pow hm,
      Fp12.cyclotomicPow_eq_pow (Fp12.cyclotomic_relation_pow hm _)]
  have ha : a ^ (Fp.modulus ^ 4) * a = a ^ (Fp.modulus ^ 2) := by
    rw [haEq]
    exact Fp12.cyclotomic_relation_pow (Fp12.cyclotomic_relation_pow hm _) _
  have hbEq : b = a.frobenius * (a ^ blsX).conjugate := by
    dsimp only [b]
    rw [Fp12.cyclotomicPow_eq_pow ha]
  have hb : b ^ (Fp.modulus ^ 4) * b = b ^ (Fp.modulus ^ 2) := by
    rw [hbEq]
    exact Fp12.cyclotomic_relation_mul (Fp12.cyclotomic_relation_frobenius ha)
      (Fp12.cyclotomic_relation_conjugate (Fp12.cyclotomic_relation_pow ha _))
  dsimp only [c]
  rw [Fp12.cyclotomicPow_eq_pow hb,
    Fp12.cyclotomicPow_eq_pow (Fp12.cyclotomic_relation_pow hb _), hbEq, haEq]
  dsimp only [m, t]
  simp only [Fp12.inverse_eq_pow, Fp12.conjugate_eq_pow, Fp12.frobenius_eq_pow,
    ← pow_mul, ← pow_add]
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
