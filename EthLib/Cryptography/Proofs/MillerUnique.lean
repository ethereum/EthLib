module

public import EthLib.Cryptography.Proofs.MillerLines

/-!
# Proofs: a product of lines is fixed by its divisor

Two quotients of products of lines with the same divisor are equal.

Miller calls a function normalized when the leading coefficient of its Laurent series at `O` is 1.

He notes that each principal divisor has exactly one normalized function.

Here the same holds for quotients of the lines of Miller's algorithm, in two steps.

First, the same divisor gives the same fractional ideal, so the two functions differ by a unit.

The units of the coordinate ring are the nonzero constants.

Second, every line has the leading coefficient 1 at `O`, so the constant is 1.

The leading coefficient is read in the basis `1, Y` of the coordinate ring over `F[X]`.

Near `O`, `x` has a pole of order 2 and `y` a pole of order 3.

So `p(X) + q(X) Y` has the leading term of `p(T^2) - T^3 q(T^2)`, in powers of `1 / T`.

The even powers of this polynomial come from `p` and the odd ones from `q`, so no term cancels.

The sign comes from the uniformizer `-x / y` at `O`, under which `y` has the leading coefficient -1.

See Miller, "The Weil Pairing, and Its Efficient Calculation", J. Cryptology 17 (2004).

Section 4.1 defines normalized functions (Definition 4).

The proof of Proposition 8, in Section 4.2, expands `x` and `y` in the uniformizer `-x / y`.

Section 4.1 prints the uniformizer as `-y / x`, which has a pole at `O`.
-/

@[expose] public section

namespace EthLib.Cryptography.Miller

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped nonZeroDivisors

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F}

/-! ## The units of the coordinate ring -/

/-- A unit of the coordinate ring is a constant.

Its norm to `F[X]` is a unit, so it has degree 0.

The norm of `p + q Y` has the degree of `p^2` or of `q^2 X^3`, so `q = 0` and `p` is constant. -/
theorem exists_eq_algebraMap_of_isUnit {a : W.CoordinateRing} (ha : IsUnit a) :
    ∃ c : F, a = algebraMap F W.CoordinateRing c := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq a
  have hn := ha.map (Algebra.norm F[X] (S := W.CoordinateRing))
  rw [Polynomial.isUnit_iff_degree_eq_zero, degree_norm_smul_basis] at hn
  have hq : q = 0 := by
    by_contra hq
    have h3 : (3 : WithBot ℕ) ≤ 2 • q.degree + 3 := by
      rw [← degree_eq_bot.not] at hq
      obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hq
      rw [← hd]
      change ((3 : ℕ) : WithBot ℕ) ≤ ((2 • d : ℕ) : WithBot ℕ) + ((3 : ℕ) : WithBot ℕ)
      exact le_add_of_nonneg_left (WithBot.coe_nonneg.mpr (Nat.zero_le _))
    have := le_max_right (2 • p.degree) (2 • q.degree + 3)
    rw [hn] at this
    exact absurd (h3.trans this) (by decide)
  subst hq
  have hp : p.degree ≤ 0 := by
    have := le_max_left (2 • p.degree) (2 • (0 : F[X]).degree + 3)
    rw [hn] at this
    rcases hd : p.degree with _ | d
    · exact bot_le
    · rw [hd] at this
      have h2 : ((2 • d : ℕ) : WithBot ℕ) ≤ ((0 : ℕ) : WithBot ℕ) := this
      have h2' : 2 • d ≤ 0 := by exact_mod_cast h2
      rw [smul_eq_mul] at h2'
      exact WithBot.coe_le_coe.mpr (by omega)
  refine ⟨p.coeff 0, ?_⟩
  rw [eq_C_of_degree_le_zero hp, zero_smul, add_zero, coeff_C_zero, Algebra.smul_def, mul_one]
  rfl

/-! ## The leading coefficient at `O` -/

/-- The polynomial `p(T^2) - T^3 q(T^2)`, whose leading term is that of `p + q Y` at `O`. -/
noncomputable def leadForm (p q : F[X]) : F[X] := expand F 2 p - X ^ 3 * expand F 2 q

/-- The odd coefficients of the polynomial come from `q`. -/
theorem coeff_leadForm_odd (p q : F[X]) (n : ℕ) :
    (leadForm p q).coeff (2 * n + 3) = -q.coeff n := by
  have h1 : ¬ 2 ∣ 2 * n + 3 := by omega
  rw [leadForm, coeff_sub, coeff_expand two_pos, mul_comm (X ^ 3), coeff_mul_X_pow,
    coeff_expand two_pos]
  simp [h1]

/-- With `q ≠ 0`, the polynomial has degree at least `2 deg q + 3`. -/
theorem le_natDegree_leadForm (p : F[X]) {q : F[X]} (hq : q ≠ 0) :
    2 * q.natDegree + 3 ≤ (leadForm p q).natDegree :=
  le_natDegree_of_ne_zero <| by
    rw [coeff_leadForm_odd, neg_ne_zero]
    exact leadingCoeff_ne_zero.mpr hq

/-- With `q ≠ 0`, the polynomial is not zero. -/
theorem leadForm_ne_zero (p : F[X]) {q : F[X]} (hq : q ≠ 0) : leadForm p q ≠ 0 := by
  intro h
  have := coeff_leadForm_odd p q q.natDegree
  rw [h, coeff_zero, eq_comm, neg_eq_zero] at this
  exact leadingCoeff_ne_zero.mpr hq this

variable (W) in
/-- The lower terms of the curve equation, in `T` with `x = T^2` and `y = -T^3`. -/
noncomputable def lowerTerms : F[X] :=
  C W.a₁ * X ^ 5 + C W.a₂ * X ^ 4 + C W.a₃ * X ^ 3 + C W.a₄ * X ^ 2 + C W.a₆

/-- The lower terms have degree at most 5, below the 6 of `x^3 = T^6`. -/
theorem natDegree_lowerTerms : (lowerTerms W).natDegree ≤ 5 := by
  unfold lowerTerms
  compute_degree

/-- The polynomial of a product is the product of the polynomials, up to lower terms. -/
theorem leadForm_mul (p₁ q₁ p₂ q₂ : F[X]) :
    leadForm (p₁ * p₂ + q₁ * q₂ * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆))
        (p₁ * q₂ + q₁ * p₂ - q₁ * q₂ * (C W.a₁ * X + C W.a₃)) =
      leadForm p₁ q₁ * leadForm p₂ q₂ + expand F 2 (q₁ * q₂) * lowerTerms W := by
  simp only [leadForm, lowerTerms, map_add, map_sub, map_mul, expand_X, expand_C, map_pow]
  ring

/-- The leading coefficient of the polynomial of a product is the product of the two. -/
theorem leadingCoeff_leadForm_mul (p₁ q₁ p₂ q₂ : F[X]) :
    (leadForm (p₁ * p₂ + q₁ * q₂ * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆))
        (p₁ * q₂ + q₁ * p₂ - q₁ * q₂ * (C W.a₁ * X + C W.a₃))).leadingCoeff =
      (leadForm p₁ q₁).leadingCoeff * (leadForm p₂ q₂).leadingCoeff := by
  rw [leadForm_mul, ← leadingCoeff_mul]
  by_cases hq : q₁ = 0 ∨ q₂ = 0
  · rcases hq with rfl | rfl <;> simp
  obtain ⟨hq₁, hq₂⟩ := not_or.mp hq
  apply leadingCoeff_add_of_degree_lt'
  apply degree_lt_degree
  have h1 := le_natDegree_leadForm p₁ hq₁
  have h2 := le_natDegree_leadForm p₂ hq₂
  rw [natDegree_mul (leadForm_ne_zero p₁ hq₁) (leadForm_ne_zero p₂ hq₂)]
  calc (expand F 2 (q₁ * q₂) * lowerTerms W).natDegree
      ≤ (expand F 2 (q₁ * q₂)).natDegree + (lowerTerms W).natDegree := natDegree_mul_le
    _ ≤ (q₁.natDegree + q₂.natDegree) * 2 + 5 := by
        rw [natDegree_expand, natDegree_mul hq₁ hq₂]
        exact Nat.add_le_add_left natDegree_lowerTerms _
    _ < _ := by omega

/-- The coordinates of `p + q Y` in the basis `1, Y` are `p` and `q`. -/
theorem repr_smul_basis (p q : F[X]) :
    (CoordinateRing.basis W).repr (p • (1 : W.CoordinateRing) + q • mk W Polynomial.X) 0 = p ∧
      (CoordinateRing.basis W).repr (p • (1 : W.CoordinateRing) + q • mk W Polynomial.X) 1 =
        q := by
  have e : p • (1 : W.CoordinateRing) + q • mk W Polynomial.X =
      ∑ i, ![p, q] i • CoordinateRing.basis W i := by
    rw [Fin.sum_univ_two, basis_zero, basis_one]
    rfl
  rw [e, ← Module.Basis.equivFun_symm_apply, ← Module.Basis.equivFun_apply,
    LinearEquiv.apply_symm_apply]
  exact ⟨rfl, rfl⟩

/-- The product of `p₁ + q₁ Y` and `p₂ + q₂ Y`, with `Y^2` replaced through the curve equation. -/
theorem smul_basis_mul (p₁ q₁ p₂ q₂ : F[X]) :
    (p₁ • (1 : W.CoordinateRing) + q₁ • mk W Polynomial.X) *
        (p₂ • (1 : W.CoordinateRing) + q₂ • mk W Polynomial.X) =
      (p₁ * p₂ + q₁ * q₂ * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) •
          (1 : W.CoordinateRing) +
        (p₁ * q₂ + q₁ * p₂ - q₁ * q₂ * (C W.a₁ * X + C W.a₃)) • mk W Polynomial.X := by
  have e : p₂ • (1 : W.CoordinateRing) + q₂ • mk W Polynomial.X =
      mk W (C p₂) + mk W (C q₂) * mk W Polynomial.X := by
    rw [smul, smul, mul_one]
  rw [e, mul_add, ← mul_assoc, smul_basis_mul_C, smul_basis_mul_C, smul_basis_mul_Y]
  simp only [smul, map_add, map_sub, map_mul, mul_one]
  ring

/-- The leading coefficient at `O`, for `x` of pole order 2 and `y` of pole order 3.

The uniformizer at `O` is `-x / y`, so `x` and `-y` have the leading coefficient 1. -/
noncomputable def leadCoeffO (a : W.CoordinateRing) : F :=
  (leadForm ((CoordinateRing.basis W).repr a 0) ((CoordinateRing.basis W).repr a 1)).leadingCoeff

/-- The leading coefficient of `p + q Y` is that of `p(T^2) - T^3 q(T^2)`. -/
theorem leadCoeffO_smul_basis (p q : F[X]) :
    leadCoeffO (p • (1 : W.CoordinateRing) + q • mk W Polynomial.X) =
      (leadForm p q).leadingCoeff := by
  rw [leadCoeffO, (repr_smul_basis p q).1, (repr_smul_basis p q).2]

/-- The leading coefficient at `O` of a product is the product of the leading coefficients. -/
theorem leadCoeffO_mul (a b : W.CoordinateRing) :
    leadCoeffO (a * b) = leadCoeffO a * leadCoeffO b := by
  obtain ⟨p₁, q₁, rfl⟩ := exists_smul_basis_eq a
  obtain ⟨p₂, q₂, rfl⟩ := exists_smul_basis_eq b
  rw [smul_basis_mul, leadCoeffO_smul_basis, leadCoeffO_smul_basis, leadCoeffO_smul_basis,
    leadingCoeff_leadForm_mul]

/-- A constant is its own leading coefficient. -/
theorem leadCoeffO_algebraMap (c : F) : leadCoeffO (algebraMap F W.CoordinateRing c) = c := by
  have e : algebraMap F W.CoordinateRing c =
      (C c) • (1 : W.CoordinateRing) + (0 : F[X]) • mk W Polynomial.X := by
    rw [zero_smul, add_zero, Algebra.smul_def, mul_one]
    rfl
  rw [e, leadCoeffO_smul_basis, leadForm, expand_C, map_zero, mul_zero, sub_zero,
    leadingCoeff_C]

variable [DecidableEq F]

/-- Every line of Miller's algorithm has the leading coefficient 1 at `O`.

A vertical is `x - x1`, and the line `y = l(x)` is `l(x) - y`. -/
theorem leadCoeffO_lineElem (T S : W.Point) : leadCoeffO (lineElem W T S) = 1 := by
  have hX (x : F) : leadCoeffO (XClass W x) = 1 := by
    have e : XClass W x = (X - C x) • (1 : W.CoordinateRing) + (0 : F[X]) • mk W Polynomial.X := by
      rw [zero_smul, add_zero, smul, mul_one]
      rfl
    rw [e, leadCoeffO_smul_basis, leadForm, map_zero, mul_zero, sub_zero, map_sub, expand_X,
      expand_C]
    exact leadingCoeff_X_pow_sub_C two_pos
  rcases T with _ | ⟨x₁, y₁, h₁⟩ <;> rcases S with _ | ⟨x₂, y₂, h₂⟩
  · rw [show lineElem W .zero .zero = 1 from rfl, ← map_one (algebraMap F W.CoordinateRing),
      leadCoeffO_algebraMap]
  · exact hX x₂
  · exact hX x₁
  · simp only [lineElem]
    split_ifs
    · exact hX x₁
    · set l := linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂)
      have e : -YClass W l = l • (1 : W.CoordinateRing) + (-1 : F[X]) • mk W Polynomial.X := by
        rw [YClass, map_sub, smul, mul_one, neg_smul, one_smul]
        ring
      have hl : (expand F 2 l).natDegree ≤ 2 := by
        rw [natDegree_expand]
        have : l.natDegree ≤ 1 := by
          simp only [l, linePolynomial]
          compute_degree
        omega
      rw [e, leadCoeffO_smul_basis, leadForm, map_neg, map_one, mul_neg, mul_one, sub_neg_eq_add,
        leadingCoeff_add_of_degree_lt (degree_lt_degree ?_), leadingCoeff_X_pow]
      rw [natDegree_X_pow]
      omega

/-- A product of lines has the leading coefficient 1 at `O`. -/
theorem leadCoeffO_linesElem (M : Multiset (W.Point × W.Point)) :
    leadCoeffO (linesElem W M) = 1 := by
  induction M using Multiset.induction with
  | empty =>
    rw [linesElem, Multiset.map_zero, Multiset.prod_zero, ← map_one (algebraMap F _),
      leadCoeffO_algebraMap]
  | cons l M ih =>
    rw [linesElem, Multiset.map_cons, Multiset.prod_cons, leadCoeffO_mul, ← linesElem, ih,
      leadCoeffO_lineElem, mul_one]

/-! ## Uniqueness -/

/-- Two quotients of products of lines with the same divisor are equal.

The quotients are `N₁ / D₁` and `N₂ / D₂`, written without division. -/
theorem linesElem_mul_eq_of_linesDivisor {N₁ D₁ N₂ D₂ : Multiset (W.Point × W.Point)}
    (h : linesDivisor W N₁ - linesDivisor W D₁ = linesDivisor W N₂ - linesDivisor W D₂) :
    linesElem W N₁ * linesElem W D₂ = linesElem W N₂ * linesElem W D₁ := by
  have hD : linesDivisor W (N₁ + D₂) = linesDivisor W (N₂ + D₁) := by
    rw [linesDivisor_add, linesDivisor_add]
    rw [sub_eq_sub_iff_add_eq_add] at h
    exact h
  have hI : Ideal.span {linesElem W (N₁ + D₂)} = Ideal.span {linesElem W (N₂ + D₁)} := by
    apply (FractionalIdeal.coeIdeal_inj (K := W.FunctionField)).mp
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
      spanSingleton_linesElem, spanSingleton_linesElem, hD]
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hI
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_isUnit u.isUnit
  have hc1 : c = 1 := by
    have := congrArg leadCoeffO hu
    rwa [leadCoeffO_mul, hc, leadCoeffO_algebraMap, leadCoeffO_linesElem, leadCoeffO_linesElem,
      one_mul] at this
  rw [hc1, map_one] at hc
  rw [← linesElem_add, ← linesElem_add, ← hu, hc, mul_one]

end EthLib.Cryptography.Miller
