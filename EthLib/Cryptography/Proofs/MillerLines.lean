module

public import EthLib.Cryptography.Proofs.MillerDivisor

/-!
# Proofs: Miller's function as a product of lines

Miller's algorithm for `s` and `Q` multiplies lines and divides by verticals.

Here the algorithm records these factors, without evaluating them.

The numerator is a multiset of lines, and so is the denominator.

From the two multisets come three objects:

- the value of the function at a point, which the loop computes;
- the element of the function field;
- the divisor, a formal sum of points.

Each line through `T` and `S` gets the divisor `(T) + (S) + (-(T + S)) - 3 (O)`.

These divisors add up to `s (Q) - (s Q) - (s - 1) (O)`, an identity of formal sums.

The fractional ideals prove the affine part of each divisor, but not the multiplicity at `O`.

So the fractional ideal of the function is the ideal of `Q` to the power `s`, over that of `s Q`.

See Miller, "The Weil Pairing, and Its Efficient Calculation", J. Cryptology 17 (2004).

These are Proposition 2 and Lemma 2, equation (7), of its Section 4.1.
-/

@[expose] public section

namespace EthLib.Cryptography.Miller

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped nonZeroDivisors

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-! ## Divisors -/

/-- The fractional ideal of a divisor: each point's ideal to its multiplicity, with 1 for `O`. -/
noncomputable def divisorUnit (D : W.Point →₀ ℤ) :
    (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ :=
  D.prod fun P n => pointUnit W P ^ n

variable {W}

/-- The zero divisor has the ideal 1. -/
theorem divisorUnit_zero : divisorUnit W 0 = 1 := Finsupp.prod_zero_index

/-- The ideal of a sum of divisors is the product of their ideals. -/
theorem divisorUnit_add (D E : W.Point →₀ ℤ) :
    divisorUnit W (D + E) = divisorUnit W D * divisorUnit W E :=
  Finsupp.prod_add_index' (fun _ => zpow_zero _) fun _ => zpow_add _

/-- The divisor `n (P)` has the ideal of `P` to the power `n`. -/
theorem divisorUnit_single (P : W.Point) (n : ℤ) :
    divisorUnit W (Finsupp.single P n) = pointUnit W P ^ n :=
  Finsupp.prod_single_index (zpow_zero _)

/-- The ideal of a difference of divisors is the quotient of their ideals. -/
theorem divisorUnit_sub (D E : W.Point →₀ ℤ) :
    divisorUnit W (D - E) = divisorUnit W D * (divisorUnit W E)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, ← divisorUnit_add, sub_add_cancel]

/-- The ideal of `n D` is the ideal of `D` to the power `n`. -/
theorem divisorUnit_nsmul (n : ℕ) (D : W.Point →₀ ℤ) :
    divisorUnit W (n • D) = divisorUnit W D ^ n := by
  induction n with
  | zero => rw [zero_smul, divisorUnit_zero, pow_zero]
  | succ n ih => rw [succ_nsmul, divisorUnit_add, ih, pow_succ]

variable (W) [DecidableEq F]

/-- The divisor of the line through `T` and `S`: `(T) + (S) + (-(T + S)) - 3 (O)`.

This is Proposition 2 of Miller (2004), Section 4.1. -/
noncomputable def lineDivisor (T S : W.Point) : W.Point →₀ ℤ :=
  Finsupp.single T 1 + Finsupp.single S 1 + Finsupp.single (-(T + S)) 1 - Finsupp.single 0 3

variable {W}

/-- The ideal of the divisor of a line is the ideal that the line generates. -/
theorem divisorUnit_lineDivisor (T S : W.Point) :
    divisorUnit W (lineDivisor W T S) =
      pointUnit W T * pointUnit W S * pointUnit W (-(T + S)) := by
  rw [lineDivisor, divisorUnit_sub, divisorUnit_add, divisorUnit_add, divisorUnit_single,
    divisorUnit_single, divisorUnit_single, divisorUnit_single, pointUnit_zero, one_zpow,
    inv_one, mul_one, zpow_one, zpow_one, zpow_one]

/-! ## Products of lines -/

variable (W)

/-- The product of the lines of a multiset, in the coordinate ring. -/
noncomputable def linesElem (M : Multiset (W.Point × W.Point)) : W.CoordinateRing :=
  (M.map fun l => lineElem W l.1 l.2).prod

/-- The product of the lines of a multiset, at `(xp, yp)`. -/
noncomputable def linesValue (M : Multiset (W.Point × W.Point)) (xp yp : F) : F :=
  (M.map fun l => line W l.1 l.2 xp yp).prod

/-- The sum of the divisors of the lines of a multiset. -/
noncomputable def linesDivisor (M : Multiset (W.Point × W.Point)) : W.Point →₀ ℤ :=
  (M.map fun l => lineDivisor W l.1 l.2).sum

variable {W}

/-- The product of the lines of a union is the product of the two products. -/
theorem linesElem_add (M N : Multiset (W.Point × W.Point)) :
    linesElem W (M + N) = linesElem W M * linesElem W N := by
  rw [linesElem, Multiset.map_add, Multiset.prod_add, linesElem, linesElem]

/-- The value of the lines of a union is the product of the two values. -/
theorem linesValue_add (M N : Multiset (W.Point × W.Point)) (xp yp : F) :
    linesValue W (M + N) xp yp = linesValue W M xp yp * linesValue W N xp yp := by
  rw [linesValue, Multiset.map_add, Multiset.prod_add, linesValue, linesValue]

/-- The divisor of the lines of a union is the sum of the two divisors. -/
theorem linesDivisor_add (M N : Multiset (W.Point × W.Point)) :
    linesDivisor W (M + N) = linesDivisor W M + linesDivisor W N := by
  rw [linesDivisor, Multiset.map_add, Multiset.sum_add, linesDivisor, linesDivisor]

/-- Taking each line `n` times multiplies the divisor by `n`. -/
theorem linesDivisor_nsmul (n : ℕ) (M : Multiset (W.Point × W.Point)) :
    linesDivisor W (n • M) = n • linesDivisor W M := by
  rw [linesDivisor, Multiset.map_nsmul, Multiset.sum_nsmul, linesDivisor]

/-- One more line adds its divisor. -/
theorem linesDivisor_insert (l : W.Point × W.Point) (M : Multiset (W.Point × W.Point)) :
    linesDivisor W (insert l M) = lineDivisor W l.1 l.2 + linesDivisor W M := by
  rw [linesDivisor, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons, linesDivisor]

/-- The divisor of one line is the divisor of that line. -/
theorem linesDivisor_singleton (l : W.Point × W.Point) :
    linesDivisor W {l} = lineDivisor W l.1 l.2 := by
  rw [linesDivisor, Multiset.map_singleton, Multiset.sum_singleton]

/-- At a point of the curve, the product of the lines takes the value of the product. -/
theorem evalAt_linesElem (M : Multiset (W.Point × W.Point)) {xp yp : F} (h : W.Equation xp yp) :
    evalAt W h (linesElem W M) = linesValue W M xp yp := by
  rw [linesElem, map_multiset_prod, Multiset.map_map]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun l _ => evalAt_lineElem l.1 l.2 h)

/-- A product of lines is not zero in the coordinate ring. -/
theorem linesElem_ne_zero (M : Multiset (W.Point × W.Point)) : linesElem W M ≠ 0 :=
  Multiset.prod_ne_zero fun h0 => by
    obtain ⟨l, -, hl⟩ := Multiset.mem_map.mp h0
    exact lineElem_ne_zero l.1 l.2 hl

/-- The fractional ideal of a product of lines is the ideal of the sum of their divisors. -/
theorem spanSingleton_linesElem (M : Multiset (W.Point × W.Point)) :
    FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (algebraMap W.CoordinateRing W.FunctionField (linesElem W M)) =
      ↑(divisorUnit W (linesDivisor W M)) := by
  induction M using Multiset.induction with
  | empty =>
    simp only [linesElem, linesDivisor, Multiset.map_zero, Multiset.prod_zero, Multiset.sum_zero,
      map_one, divisorUnit_zero, Units.val_one]
  | cons l M ih =>
    rw [← Multiset.singleton_add, linesElem_add, linesDivisor_add, divisorUnit_add, map_mul,
      map_mul, ih, Units.val_mul]
    congr 1
    simp only [linesElem, linesDivisor, Multiset.map_singleton, Multiset.prod_singleton,
      Multiset.sum_singleton, divisorUnit_lineDivisor, spanSingleton_lineElem]

/-! ## The factors of Miller's algorithm -/

variable (W)

/-- The lines that the loop multiplies and divides by, from bit `n - 1` down to bit `0` of `s`.

The pair holds the numerator and the denominator, and `T` is the current point.

Doubling squares the function and multiplies it by `g_{T,T}`.

Adding `Q` multiplies it by `g_{2T,Q}`.

The lines `L` go to the numerator, and the verticals to the denominator. -/
noncomputable def lineSteps (s : ℕ) (Q : W.Point) :
    ℕ → W.Point → Multiset (W.Point × W.Point) × Multiset (W.Point × W.Point) →
      Multiset (W.Point × W.Point) × Multiset (W.Point × W.Point)
  | 0, _, M => M
  | n + 1, T, M =>
    if s.testBit n then
      lineSteps s Q n (T + T + Q)
        (2 • M.1 + {(T, T), (T + T, Q)}, 2 • M.2 + {(T + T, -(T + T)), (T + T + Q, -(T + T + Q))})
    else lineSteps s Q n (T + T) (2 • M.1 + {(T, T)}, 2 • M.2 + {(T + T, -(T + T))})

/-- The lines of Miller's function `f_{s,Q}`: the numerator, then the denominator. -/
noncomputable def lines (s : ℕ) (Q : W.Point) :
    Multiset (W.Point × W.Point) × Multiset (W.Point × W.Point) :=
  lineSteps W s Q s.log2 Q (0, 0)

/-- Miller's function `f_{s,Q}` in the function field. -/
noncomputable def millerElem (s : ℕ) (Q : W.Point) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (linesElem W (lines W s Q).1) /
    algebraMap W.CoordinateRing W.FunctionField (linesElem W (lines W s Q).2)

/-- The divisor `s (Q) - (s Q) - (s - 1) (O)`.

This is the divisor of `f_{s,Q}` in Lemma 2, equation (7), of Miller (2004), Section 4.1. -/
noncomputable def millerDivisor (s : ℕ) (Q : W.Point) : W.Point →₀ ℤ :=
  (s : ℤ) • Finsupp.single Q 1 - Finsupp.single (s • Q) 1 - ((s : ℤ) - 1) • Finsupp.single 0 1

variable {W}

/-! ## The value at a point -/

/-- Started from the value of some lines, the steps of the loop give the value of the new lines.

Each step multiplies by the values of the lines it adds and divides by those of the verticals. -/
theorem steps_linesValue (s : ℕ) (Q : W.Point) (xp yp : F) :
    ∀ (n : ℕ) (T : W.Point) (M : Multiset (W.Point × W.Point) × Multiset (W.Point × W.Point)),
      steps W s Q xp yp n T (linesValue W M.1 xp yp / linesValue W M.2 xp yp) =
        linesValue W (lineSteps W s Q n T M).1 xp yp /
          linesValue W (lineSteps W s Q n T M).2 xp yp := by
  intro n
  induction n with
  | zero => intro T M; rfl
  | succ n ih =>
    intro T M
    rw [steps_succ, lineSteps]
    split_ifs
    · rw [← ih]
      congr 1
      rw [linesValue_add, linesValue_add]
      simp only [linesValue, Multiset.map_nsmul, Multiset.prod_nsmul, Multiset.insert_eq_cons,
        Multiset.map_cons, Multiset.prod_cons, Multiset.map_singleton, Multiset.prod_singleton,
        lineRatio]
      ring
    · rw [← ih]
      congr 1
      rw [linesValue_add, linesValue_add]
      simp only [linesValue, Multiset.map_nsmul, Multiset.prod_nsmul, Multiset.map_singleton,
        Multiset.prod_singleton, lineRatio]
      ring

/-- Miller's algorithm computes the product of the numerator lines over that of the verticals.

This holds at every pair `(xp, yp)`: a vertical that vanishes there makes both sides zero. -/
theorem loop_eq_linesValue (s : ℕ) (Q : W.Point) (xp yp : F) :
    loop W s Q xp yp = linesValue W (lines W s Q).1 xp yp / linesValue W (lines W s Q).2 xp yp := by
  have h1 : linesValue W (0 : Multiset (W.Point × W.Point)) xp yp /
      linesValue W (0 : Multiset (W.Point × W.Point)) xp yp = 1 := by
    simp [linesValue]
  rw [loop, lines, ← steps_linesValue, h1]

/-- At a point of the curve, Miller's algorithm is the quotient of the values of the products. -/
theorem loop_eq_evalAt (s : ℕ) (Q : W.Point) {xp yp : F} (h : W.Equation xp yp) :
    loop W s Q xp yp = evalAt W h (linesElem W (lines W s Q).1) /
      evalAt W h (linesElem W (lines W s Q).2) := by
  rw [loop_eq_linesValue, evalAt_linesElem, evalAt_linesElem]

/-! ## The divisor -/

/-- The doubling step adds the divisor `2 (T) - (2 T) - (O)` of `g_{T,T}`. -/
private theorem lineDivisor_sub_double (T : W.Point) :
    lineDivisor W T T - lineDivisor W (T + T) (-(T + T)) =
      (2 : ℤ) • Finsupp.single T 1 - Finsupp.single (T + T) 1 - Finsupp.single 0 1 := by
  simp only [lineDivisor, add_neg_cancel, neg_zero, two_smul]
  ext P
  simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
  split_ifs <;> omega

/-- The addition step adds the divisor `(T) + (Q) - (T + Q) - (O)` of `g_{T,Q}`. -/
theorem lineDivisor_sub_add (T Q : W.Point) :
    lineDivisor W T Q - lineDivisor W (T + Q) (-(T + Q)) =
      Finsupp.single T 1 + Finsupp.single Q 1 - Finsupp.single (T + Q) 1 -
        Finsupp.single 0 1 := by
  simp only [lineDivisor, add_neg_cancel, neg_zero]
  ext P
  simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
  split_ifs <;> omega

/-- The divisor of the lines after the steps, when `T = k Q` and `k` is the part of `s` read. -/
theorem linesDivisor_lineSteps (s : ℕ) (Q : W.Point) :
    ∀ (n : ℕ) (T : W.Point) (M : Multiset (W.Point × W.Point) × Multiset (W.Point × W.Point)),
      T = (s >>> n) • Q → linesDivisor W M.1 - linesDivisor W M.2 = millerDivisor W (s >>> n) Q →
      linesDivisor W (lineSteps W s Q n T M).1 - linesDivisor W (lineSteps W s Q n T M).2 =
        millerDivisor W s Q := by
  intro n
  induction n with
  | zero =>
    intro T M _ hM
    rw [Nat.shiftRight_zero] at hM
    exact hM
  | succ n ih =>
    intro T M hT hM
    have hsplit := shiftRight_split s n
    set k := s >>> (n + 1)
    have hd := lineDivisor_sub_double (W := W) T
    rw [lineSteps]
    split_ifs with hb
    · simp only [hb, ite_true] at hsplit
      have ha := lineDivisor_sub_add (W := W) (T + T) Q
      refine ih _ _ (by rw [hT, hsplit, ← two_nsmul, ← mul_nsmul', add_nsmul, one_nsmul]) ?_
      simp only [linesDivisor_add, linesDivisor_nsmul, linesDivisor_insert, linesDivisor_singleton]
      calc _ = 2 • (linesDivisor W M.1 - linesDivisor W M.2) +
              (lineDivisor W T T - lineDivisor W (T + T) (-(T + T))) +
              (lineDivisor W (T + T) Q - lineDivisor W (T + T + Q) (-(T + T + Q))) := by
            rw [nsmul_sub]; abel
        _ = _ := by
          have hP : (2 * k + 1) • Q = T + T + Q := by
            rw [hT, ← two_nsmul, ← mul_nsmul', add_nsmul, one_nsmul]
          rw [hM, hd, ha, hsplit, millerDivisor, millerDivisor, hP, ← hT]
          push_cast
          module
    · simp only [hb, Bool.false_eq_true, ite_false, add_zero] at hsplit
      refine ih _ _ (by rw [hT, hsplit, ← two_nsmul, ← mul_nsmul']) ?_
      simp only [linesDivisor_add, linesDivisor_nsmul, linesDivisor_singleton]
      calc _ = 2 • (linesDivisor W M.1 - linesDivisor W M.2) +
              (lineDivisor W T T - lineDivisor W (T + T) (-(T + T))) := by
            rw [nsmul_sub]; abel
        _ = _ := by
          have hP : (2 * k) • Q = T + T := by rw [hT, ← two_nsmul, ← mul_nsmul']
          rw [hM, hd, hsplit, millerDivisor, millerDivisor, hP, ← hT]
          push_cast
          module

/-- The lines of `f_{s,Q}` have the divisor `s (Q) - (s Q) - (s - 1) (O)`.

This is Lemma 2, equation (7), of Miller (2004), Section 4.1. -/
theorem linesDivisor_lines (s : ℕ) (Q : W.Point) :
    linesDivisor W (lines W s Q).1 - linesDivisor W (lines W s Q).2 = millerDivisor W s Q := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp [lines, lineSteps, linesDivisor, millerDivisor]
  have hlog := shiftRight_log2 hs.ne'
  refine linesDivisor_lineSteps s Q _ _ _ (by rw [hlog, one_nsmul]) ?_
  simp [linesDivisor, millerDivisor, hlog]

/-- The ideal of `s (Q) - (s Q) - (s - 1) (O)` is that of `Q` to the power `s`, over that of `s Q`.

The point `O` has the ideal 1, so its multiplicity does not matter. -/
theorem divisorUnit_millerDivisor (s : ℕ) (Q : W.Point) :
    divisorUnit W (millerDivisor W s Q) = pointUnit W Q ^ s * (pointUnit W (s • Q))⁻¹ := by
  rw [millerDivisor, divisorUnit_sub, divisorUnit_sub, Finsupp.smul_single_one,
    Finsupp.smul_single_one, divisorUnit_single, divisorUnit_single, divisorUnit_single,
    pointUnit_zero, one_zpow, inv_one, mul_one, zpow_one, zpow_natCast]

/-- The fractional ideal of `f_{s,Q}` is the ideal of `Q` to the power `s`, over that of `s Q`. -/
theorem spanSingleton_millerElem (s : ℕ) (Q : W.Point) :
    FractionalIdeal.spanSingleton W.CoordinateRing⁰ (millerElem W s Q) =
      ↑(pointUnit W Q ^ s * (pointUnit W (s • Q))⁻¹) := by
  have hy : algebraMap W.CoordinateRing W.FunctionField (linesElem W (lines W s Q).2) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero (linesElem_ne_zero _))
  set u := divisorUnit W (linesDivisor W (lines W s Q).2)
  rw [← divisorUnit_millerDivisor, ← linesDivisor_lines, divisorUnit_sub,
    ← Units.mul_inv_cancel_right
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰ (millerElem W s Q)) u,
    ← spanSingleton_linesElem, ← map_mul, millerElem, div_mul_cancel₀ _ hy,
    spanSingleton_linesElem, Units.val_mul]

end EthLib.Cryptography.Miller
