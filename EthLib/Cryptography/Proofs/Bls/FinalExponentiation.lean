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

It is equation (5) there, where the paper writes `q` for our `p^2`.

It holds on the cyclotomic subgroup, and also at zero, since `0 * 0 = 0`.

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

private theorem coordinate_relations {K : Type} [Field K]
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
    a5 * (1 - d)) :
    a0 * a0 + u * a3 * a3 - a0 - u * a1 * a5 - u * a2 * a4 = 0 ∧
      a0 * a1 - 2 * u * a2 * a5 + u * a3 * a4 - a1 = 0 ∧
      -a0 * a2 + a1 * a1 - u * a3 * a5 + u * a4 * a4 - a2 = 0 ∧
      2 * a0 * a3 - a1 * a2 - u * a4 * a5 + a3 = 0 ∧
      a0 * a4 + a1 * a3 - a2 * a2 - u * a5 * a5 + a4 = 0 ∧
      -a0 * a5 + 2 * a1 * a4 - a2 * a3 + a5 = 0 := by
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
  exact ⟨r0, r1, r2, r3, r4, r5⟩

private theorem square_coordinates {K : Type} [Field K] (u a0 a1 a2 a3 a4 a5 : K)
    (r0 : a0 * a0 + u * a3 * a3 - a0 - u * a1 * a5 - u * a2 * a4 = 0)
    (r1 : a0 * a1 - 2 * u * a2 * a5 + u * a3 * a4 - a1 = 0)
    (r2 : -a0 * a2 + a1 * a1 - u * a3 * a5 + u * a4 * a4 - a2 = 0)
    (r3 : 2 * a0 * a3 - a1 * a2 - u * a4 * a5 + a3 = 0)
    (r4 : a0 * a4 + a1 * a3 - a2 * a2 - u * a5 * a5 + a4 = 0)
    (r5 : -a0 * a5 + 2 * a1 * a4 - a2 * a3 + a5 = 0)
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

/-- The six relations between the coordinates, from the coordinate form of the relation. -/
private theorem relations_of_coordinate_relation (d : Fp2) (hd : d ^ 2 - d + 1 = 0)
    {a0 a1 a2 a3 a4 a5 : Fp2}
    (h : frobenius4Form d ⟨⟨a0, a2, a4⟩, ⟨a1, a3, a5⟩⟩ * ⟨⟨a0, a2, a4⟩, ⟨a1, a3, a5⟩⟩ =
      frobenius2Form d ⟨⟨a0, a2, a4⟩, ⟨a1, a3, a5⟩⟩) :
    a0 * a0 + Fp2.xi * a3 * a3 - a0 - Fp2.xi * a1 * a5 - Fp2.xi * a2 * a4 = 0 ∧
      a0 * a1 - 2 * Fp2.xi * a2 * a5 + Fp2.xi * a3 * a4 - a1 = 0 ∧
      -a0 * a2 + a1 * a1 - Fp2.xi * a3 * a5 + Fp2.xi * a4 * a4 - a2 = 0 ∧
      2 * a0 * a3 - a1 * a2 - Fp2.xi * a4 * a5 + a3 = 0 ∧
      a0 * a4 + a1 * a3 - a2 * a2 - Fp2.xi * a5 * a5 + a4 = 0 ∧
      -a0 * a5 + 2 * a1 * a4 - a2 * a3 + a5 = 0 := by
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
  exact coordinate_relations d Fp2.xi a0 a1 a2 a3 a4 a5 hd h0 h1 h2 h3 h4 h5

private theorem cyclotomicSquare_of_coordinate_relation (d : Fp2)
    (hd : d ^ 2 - d + 1 = 0) (a : Fp12)
    (h : frobenius4Form d a * a = frobenius2Form d a) :
    a.cyclotomicSquare = a * a := by
  obtain ⟨⟨a0, a2, a4⟩, ⟨a1, a3, a5⟩⟩ := a
  obtain ⟨r0, r1, r2, r3, r4, r5⟩ := relations_of_coordinate_relation d hd h
  have hc := square_coordinates Fp2.xi a0 a1 a2 a3 a4 a5 r0 r1 r2 r3 r4 r5
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

private theorem coordinate_relation_of_coefficients (d : Fp2) (hd : d ^ 2 - d + 1 = 0)
    (coordinates : ∀ a : Fp12,
      a ^ (Fp.modulus ^ 2) =
        ⟨⟨a.c0.c0, a.c0.c1 * d ^ 2, a.c0.c2 * d ^ 4⟩,
          ⟨a.c1.c0 * d, a.c1.c1 * d ^ 3, a.c1.c2 * d ^ 5⟩⟩)
    (a : Fp12) (ha : a ^ (Fp.modulus ^ 4) * a = a ^ (Fp.modulus ^ 2)) :
    frobenius4Form d a * a = frobenius2Form d a := by
  have h2 (x : Fp12) : x ^ (Fp.modulus ^ 2) = frobenius2Form d x :=
    (coordinates x).trans (frobenius2Form_of_powers d hd x)
  have h4 : a ^ (Fp.modulus ^ 4) = frobenius4Form d a := by
    calc
      a ^ (Fp.modulus ^ 4) = (a ^ (Fp.modulus ^ 2)) ^ (Fp.modulus ^ 2) := by
        rw [← pow_mul, show Fp.modulus ^ 2 * Fp.modulus ^ 2 = Fp.modulus ^ 4 by ring]
      _ = frobenius2Form d (frobenius2Form d a) := by rw [h2, h2]
      _ = frobenius4Form d a := frobenius2Form_comp d hd a
  rw [← h4, ← h2]
  exact ha

/-- The cyclotomic square is a square under the `p^2`-power relation, including zero. -/
theorem cyclotomicSquare_eq_mul_self {a : Fp12}
    (ha : a ^ (Fp.modulus ^ 4) * a = a ^ (Fp.modulus ^ 2)) :
    a.cyclotomicSquare = a * a :=
  cyclotomicSquare_of_coordinate_relation cyclotomicCoeff cyclotomicCoeff_quadratic a
    (coordinate_relation_of_coefficients cyclotomicCoeff cyclotomicCoeff_quadratic
      frobenius2_power_coordinates a ha)

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

/-! ## Exponentiation with compressed squares -/

/-- The kept coefficients of the cyclotomic square are the square of the kept coefficients. -/
private theorem compress_cyclotomicSquare (a : Fp12) :
    compress a.cyclotomicSquare = (compress a).square := by
  obtain ⟨⟨a0, a2, a4⟩, ⟨a1, a3, a5⟩⟩ := a
  simp only [compress, cyclotomicSquare, Compressed.square,
    Cryptography.Fp2.square_eq Fp.embedding, Fp2.mulByOnePlusI_eq, Compressed.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- Under the relation, the numerators and the inverse of `D` give the element back. -/
private theorem decompress_compress {a : Fp12}
    (ha : a ^ (Fp.modulus ^ 4) * a = a ^ (Fp.modulus ^ 2))
    (hD : (compress a).numerators.2.2 ≠ 0) :
    (compress a).decompress (compress a).numerators (compress a).numerators.2.2⁻¹ = a := by
  obtain ⟨⟨a0, a2, a4⟩, ⟨a1, a3, a5⟩⟩ := a
  obtain ⟨-, -, r2, -, -, r5⟩ := relations_of_coordinate_relation cyclotomicCoeff
    cyclotomicCoeff_quadratic (coordinate_relation_of_coefficients cyclotomicCoeff
      cyclotomicCoeff_quadratic frobenius2_power_coordinates _ ha)
  simp only [compress, Compressed.numerators, Compressed.decompress,
    Cryptography.Fp2.square_eq Fp.embedding, Fp2.mulByOnePlusI_eq] at hD ⊢
  rw [Fp12.mk.injEq, Fp6.mk.injEq, Fp6.mk.injEq, mul_inv_eq_iff_eq_mul₀ hD,
    mul_inv_eq_iff_eq_mul₀ hD]
  refine ⟨⟨?_, rfl, rfl⟩, rfl, ?_, rfl⟩
  · linear_combination a2 * r2 - Fp2.xi * a5 * r5
  · linear_combination a2 * r5 - a5 * r2

/-- The last component of the suffix products is the product of the list. -/
private theorem suffixProducts_snd (xs : List Fp2) : (suffixProducts xs).2 = xs.prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.prod_cons, ← ih]
    rfl

/-- Montgomery's trick inverts each element of a list of nonzero product. -/
private theorem batchInverse_suffixProducts (xs : List Fp2) (h : xs.prod ≠ 0) :
    batchInverse (suffixProducts xs).1 xs.prod⁻¹ = xs.map (·⁻¹) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.prod_cons] at h
    obtain ⟨hx, hxs⟩ := mul_ne_zero_iff.mp h
    have hstep : suffixProducts (x :: xs) =
        ((x, (suffixProducts xs).2) :: (suffixProducts xs).1, x * (suffixProducts xs).2) := rfl
    rw [hstep, List.prod_cons, List.map_cons, batchInverse, suffixProducts_snd, mul_inv,
      inv_mul_cancel_right₀ hxs, mul_comm, mul_inv_cancel_left₀ hx, ih hxs]

/-- The kept coefficients of the squares that the bits of `n` select, as compressed powers.

Their product is `b^n`. -/
private theorem squares_eq {b : Fp12} (hb : b ^ (Fp.modulus ^ 4) * b = b ^ (Fp.modulus ^ 2))
    (n : Nat) :
    ∃ L : List Fp12, (∀ x ∈ L, x ^ (Fp.modulus ^ 4) * x = x ^ (Fp.modulus ^ 2)) ∧
      (compress b).squares n = L.map compress ∧ L.prod = b ^ n := by
  induction n using Nat.strongRecOn generalizing b with
  | _ n ih =>
    rw [Compressed.squares]
    by_cases h0 : n = 0
    · subst h0
      exact ⟨[], fun _ hx => absurd hx List.not_mem_nil, rfl, by rw [List.prod_nil, pow_zero]⟩
    rw [ite_eq_right h0]
    by_cases h1 : n = 1
    · subst h1
      refine ⟨[b], fun x hx => ?_, rfl, by rw [List.prod_singleton, pow_one]⟩
      rw [List.mem_singleton.mp hx]
      exact hb
    rw [ite_eq_right h1]
    obtain ⟨L, hL, hsq, hprod⟩ := ih (n / 2) (by omega) (cyclotomic_relation_mul hb hb)
    rw [← cyclotomicSquare_eq_mul_self hb, compress_cyclotomicSquare] at hsq
    rw [← pow_two, ← pow_mul] at hprod
    by_cases h2 : n % 2 = 1
    · refine ⟨b :: L, fun x hx => ?_, ?_, ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact hb
        · exact hL x hx
      · rw [ite_eq_left h2, hsq, List.map_cons]
      · rw [List.prod_cons, hprod, ← pow_succ']
        congr 1
        omega
    · refine ⟨L, hL, ?_, ?_⟩
      · rw [ite_eq_right h2, hsq]
      · rw [hprod]
        congr 1
        omega

/-- Each element of the list decompresses from its kept coefficients and its inverse of `D`. -/
private theorem zipWith_decompress {L : List Fp12}
    (hL : ∀ x ∈ L, x ^ (Fp.modulus ^ 4) * x = x ^ (Fp.modulus ^ 2))
    (hD : ∀ x ∈ L, (compress x).numerators.2.2 ≠ 0) :
    List.zipWith (fun x d => x.1.decompress x.2 d)
      ((L.map compress).zip ((L.map compress).map Compressed.numerators))
      ((((L.map compress).map Compressed.numerators).map fun n => n.2.2).map (·⁻¹)) = L := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.zipWith_cons_cons]
    rw [decompress_compress (hL x List.mem_cons_self) (hD x List.mem_cons_self),
      ih (fun y hy => hL y (List.mem_cons_of_mem x hy))
        (fun y hy => hD y (List.mem_cons_of_mem x hy))]

/-- A left fold by the product is the product of the start and of the list. -/
private theorem foldl_mul (x : Fp12) (l : List Fp12) : l.foldl (· * ·) x = x * l.prod := by
  induction l generalizing x with
  | nil => rw [List.foldl_nil, List.prod_nil, mul_one]
  | cons y l ih => rw [List.foldl_cons, ih, List.prod_cons, mul_assoc]

/-- The power with compressed squares is exponentiation under the `p^2`-power relation. -/
theorem compressedPow_eq_pow
    {a : Fp12} (ha : a ^ (Fp.modulus ^ 4) * a = a ^ (Fp.modulus ^ 2)) (e : Nat) :
    compressedPow a e = a ^ e := by
  obtain ⟨L, hL, hsq, hprod⟩ := squares_eq (cyclotomic_relation_mul ha ha) (e / 2)
  rw [← cyclotomicSquare_eq_mul_self ha, compress_cyclotomicSquare] at hsq
  unfold compressedPow
  dsimp only
  rw [hsq, suffixProducts_snd]
  by_cases hz : Fp2.isZero (((L.map compress).map Compressed.numerators).map fun n => n.2.2).prod
  · rw [ite_eq_left hz]
    exact cyclotomicPow_eq_pow ha e
  rw [ite_eq_right hz]
  have hne : (((L.map compress).map Compressed.numerators).map fun n => n.2.2).prod ≠ 0 :=
    fun h => hz (Fp2.isZero_iff.mpr h)
  have hD : ∀ x ∈ L, (compress x).numerators.2.2 ≠ 0 := fun x hx h0 =>
    hne (List.prod_eq_zero (List.mem_map.mpr
      ⟨_, List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨x, hx, rfl⟩, rfl⟩, h0⟩))
  rw [show ∀ x : Fp2, x.inverse = x⁻¹ from fun _ => rfl, batchInverse_suffixProducts _ hne,
    zipWith_decompress hL hD]
  have hpow : (a * a) ^ (e / 2) = a ^ (2 * (e / 2)) := by rw [← pow_two, ← pow_mul]
  by_cases h2 : e % 2 = 1
  · rw [ite_eq_left h2, foldl_mul, hprod, hpow, ← pow_succ']
    congr 1
    omega
  rw [ite_eq_right h2]
  cases L with
  | nil =>
    dsimp only
    rw [List.prod_nil, hpow] at hprod
    rw [one_eq_one, hprod]
    congr 1
    omega
  | cons p rest =>
    dsimp only
    rw [foldl_mul, ← List.prod_cons, hprod, hpow]
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
      Fp12.compressedPow_eq_pow (Fp12.cyclotomic_relation_pow hm _)]
  have ha : a ^ (Fp.modulus ^ 4) * a = a ^ (Fp.modulus ^ 2) := by
    rw [haEq]
    exact Fp12.cyclotomic_relation_pow (Fp12.cyclotomic_relation_pow hm _) _
  have hbEq : b = a.frobenius * (a ^ blsX).conjugate := by
    dsimp only [b]
    rw [Fp12.compressedPow_eq_pow ha]
  have hb : b ^ (Fp.modulus ^ 4) * b = b ^ (Fp.modulus ^ 2) := by
    rw [hbEq]
    exact Fp12.cyclotomic_relation_mul (Fp12.cyclotomic_relation_frobenius ha)
      (Fp12.cyclotomic_relation_conjugate (Fp12.cyclotomic_relation_pow ha _))
  dsimp only [c]
  rw [Fp12.compressedPow_eq_pow hb,
    Fp12.compressedPow_eq_pow (Fp12.cyclotomic_relation_pow hb _), hbEq, haEq]
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
