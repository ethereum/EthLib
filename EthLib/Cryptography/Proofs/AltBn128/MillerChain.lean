module

public import EthLib.Cryptography.Proofs.AltBn128.FinalExponentiation
public import EthLib.Cryptography.Proofs.AltBn128.Lines
public import EthLib.Cryptography.Proofs.AltBn128.Twist
public import EthLib.Cryptography.Proofs.ScaledCurve

/-!
# Proofs: the pairing of alt_bn128 is the final exponentiation of Miller's algorithm

The untwist sends a point `(x, y)` of the twist to `(x w^2, y w^3)` on `y^2 = x^3 + 3`.

That curve is over `Fp12`, and `pi` is the map `(x, y) -> (x^p, y^p)` on its points.

Write `Q'` for the untwist of `Q`, `s = 6 u + 2` and `R = s Q'`.

The pairing multiplies three values at `P`, then applies the final exponentiation.

- The value of Miller's algorithm for `s` and `Q'`.
- The line through `R` and `pi(Q')`.
- The line through `R + pi(Q')` and `-pi(pi(Q'))`.

[Beuchat et al.](https://eprint.iacr.org/2010/354), §2, call this the optimal ate pairing.

There, the first value is `f_{s, Q'}(P)`, which Miller's Lemma 2 gives; no theorem here proves it.

The loop of the specification multiplies by lines, without the verticals of Miller's algorithm.

The vertical through the untwist of `(x, y)` is `xp - x w^2`, nonzero when `x ≠ 0`.

It is fixed by the `p^6`-th power, so the final exponentiation sends it to 1.

The loop keeps `T = k Q`, with `0 < k ≤ s < q`, and `Q` of prime order `q`.

So no point of the loop is `O`, or has order 2 or 3.

A finite point with `x = 0` has order 3, so each vertical of the loop is nonzero.
-/

@[expose] public section

namespace EthLib.Cryptography.AltBn128

open WeierstrassCurve WeierstrassCurve.Affine Fp12

open scoped Fin.CommRing

/-! ## The untwist and the Frobenius map -/

/-- The curve `y^2 = x^3 + 3` over `Fp12`. -/
noncomputable abbrev ambientCurve : WeierstrassCurve.Affine Fp12 := ShortWeierstrass.curve 0 3

private theorem xi_ne_zero : (⟨9, 1⟩ : Fp2) ≠ 0 := fun h => absurd (congrArg Fp2.c1 h) (by decide)

/-- `w` is not zero, since `w^6 = 9 + i` is not. -/
theorem w_ne_zero : wPow 1 ≠ 0 := by
  intro h
  have h6 := w_pow_six
  rw [h, zero_pow (by decide)] at h6
  exact (map_ne_zero ofFp2Hom).mpr xi_ne_zero h6.symm

/-- `b2 w^6 = 3`, since `b2 = 3 / (9 + i)` and `w^6 = 9 + i`. -/
theorem twist_coefficient : ofFp2Hom b2 * wPow 1 ^ 6 = 3 := by
  rw [w_pow_six, ← map_mul, show b2 = 3 * (⟨9, 1⟩ : Fp2)⁻¹ from rfl, mul_assoc,
    inv_mul_cancel₀ xi_ne_zero, mul_one, map_ofNat]

/-- The untwist `(x, y) -> (x w^2, y w^3)`, a group homomorphism. -/
noncomputable def untwist : twist.Point →+ ambientCurve.Point :=
  ShortWeierstrass.scaledHom ofFp2Hom w_ne_zero twist_coefficient

/-- Distinct points of the twist have distinct untwists. -/
theorem untwist_injective : Function.Injective untwist :=
  ShortWeierstrass.scaledHom_injective _ _ _

/-- The map `(x, y) -> (x^p, y^p)` on points over `Fp12`, a group homomorphism. -/
noncomputable def frobeniusHom : ambientCurve.Point →+ ambientCurve.Point :=
  ShortWeierstrass.scaledHom primeFrobenius one_ne_zero (by rw [map_ofNat, one_pow, mul_one])

/-- The two embeddings agree on `Fp`. -/
theorem ofFp2Hom_ofFp (c : Fp) : ofFp2Hom (Fp2.ofFp c) = ofFpHom c := by
  apply toQuot_injective
  change toQuot (ofFp2 _) = toQuot (ofFp c)
  rw [toQuot_ofFp2, toQuot_ofFp]
  simp

/-- `i^p = -i`, since `(p - 1) / 2` is odd. -/
private theorem i_pow_modulus : Fp2.i ^ Fp.modulus = -Fp2.i := by
  rw [show Fp.modulus = 2 * ((Fp.modulus - 1) / 2) + 1 by decide, pow_succ, pow_mul, sq,
    Fp2.i_mul_i, Odd.neg_one_pow (by decide), neg_one_mul]

/-- The conjugate in `Fp2` is the `p`-th power. -/
theorem ofFp2Hom_conj (x : Fp2) : ofFp2Hom x.conj = primeFrobenius (ofFp2Hom x) := by
  have hx : x = Fp2.ofFp x.c0 + Fp2.ofFp x.c1 * Fp2.i := by
    apply Fp2.ext <;> simp [Fp2.i]
  have hc : x.conj = Fp2.ofFp x.c0 - Fp2.ofFp x.c1 * Fp2.i := by
    apply Fp2.ext <;> simp [Fp2.i, Fp2.conj]
  rw [hc]
  conv_rhs => rw [hx]
  simp only [map_add, map_sub, map_mul, ofFp2Hom_ofFp, primeFrobenius_apply, ← map_pow,
    i_pow_modulus, map_neg]
  have h0 : x.c0 ^ Fp.modulus = x.c0 := ZMod.pow_card (p := Fp.modulus) x.c0
  have h1 : x.c1 ^ Fp.modulus = x.c1 := ZMod.pow_card (p := Fp.modulus) x.c1
  rw [h0, h1]
  ring

/-- `(w^2)^p = w^2 (9 + i)^((p - 1) / 3)`, since `w^6 = 9 + i`. -/
theorem primeFrobenius_w_sq : primeFrobenius (wPow 1 ^ 2) = ofFp2Hom frobeniusX * wPow 1 ^ 2 := by
  rw [primeFrobenius_apply, frobeniusX, Fp2.powBits_eq_pow 256 _ _ (by decide), map_pow,
    ← w_pow_six, ← pow_mul, ← pow_mul, ← pow_add,
    show 2 * Fp.modulus = 6 * ((Fp.modulus - 1) / 3) + 2 by decide]

/-- `(w^3)^p = w^3 (9 + i)^((p - 1) / 2)`, since `w^6 = 9 + i`. -/
theorem primeFrobenius_w_cube :
    primeFrobenius (wPow 1 ^ 3) = ofFp2Hom frobeniusY * wPow 1 ^ 3 := by
  rw [primeFrobenius_apply, frobeniusY, Fp2.powBits_eq_pow 256 _ _ (by decide), map_pow,
    ← w_pow_six, ← pow_mul, ← pow_mul, ← pow_add,
    show 3 * Fp.modulus = 6 * ((Fp.modulus - 1) / 2) + 3 by decide]

/-- The Frobenius map of the specification keeps a point on the twist.

Under the untwist, it is the map `(x, y) -> (x^p, y^p)`. -/

theorem untwist_frobenius {Q : Point2} (hQ : Q.isOnCurve = true) :
    (frobenius Q).isOnCurve = true ∧
      untwist (frobenius Q).toPoint = frobeniusHom (untwist Q.toPoint) := by
  cases Q with
  | infinity => exact ⟨rfl, rfl⟩
  | affine x y =>
    have hX : ofFp2Hom (x.conj * frobeniusX) * wPow 1 ^ 2 =
        primeFrobenius (ofFp2Hom x * wPow 1 ^ 2) * 1 ^ 2 := by
      rw [one_pow, mul_one, map_mul, map_mul, ofFp2Hom_conj, primeFrobenius_w_sq]
      ring
    have hY : ofFp2Hom (y.conj * frobeniusY) * wPow 1 ^ 3 =
        primeFrobenius (ofFp2Hom y * wPow 1 ^ 3) * 1 ^ 3 := by
      rw [one_pow, mul_one, map_mul, map_mul, ofFp2Hom_conj, primeFrobenius_w_cube]
      ring
    have hns := ShortWeierstrass.scaled_nonsingular primeFrobenius 1 one_ne_zero
      (by rw [map_ofNat, one_pow, mul_one] : primeFrobenius 3 * 1 ^ 6 = (3 : Fp12))
      (ShortWeierstrass.scaled_nonsingular ofFp2Hom (wPow 1) w_ne_zero twist_coefficient
        (twist_nonsingular_of ((Point2.isOnCurve_affine x y).mp hQ)))
    rw [← hX, ← hY] at hns
    have heq :=
      ShortWeierstrass.equation_of_scaled ofFp2Hom (wPow 1) w_ne_zero twist_coefficient hns.1
    have hc : (Point2.affine (x.conj * frobeniusX) (y.conj * frobeniusY)).isOnCurve = true :=
      (Point2.isOnCurve_affine _ _).mpr ((twist_equation_iff _ _).mp heq)
    refine ⟨hc, ?_⟩
    change untwist (Point2.affine (x.conj * frobeniusX) (y.conj * frobeniusY)).toPoint = _
    rw [Point2.toPoint_affine hc, Point2.toPoint_affine hQ]
    change Affine.Point.some _ _ _ = Affine.Point.some _ _ _
    rw [Affine.Point.some.injEq]
    exact ⟨hX, hY⟩

/-! ## Lines and verticals -/

/-- The line of the specification through two points of the twist is Miller's line.

The two points are not the same point of order 2. -/
theorem linefunc_eq_line {x₁ y₁ x₂ y₂ : Fp2} (h₁ : (Point2.affine x₁ y₁).isOnCurve = true)
    (h₂ : (Point2.affine x₂ y₂).isOnCurve = true) (hdeg : x₁ = x₂ → y₁ = y₂ → y₁ ≠ 0)
    (xt yt : Fp) :
    linefunc (.affine x₁ y₁) (.affine x₂ y₂) xt yt =
      Miller.line ambientCurve (untwist (Point2.affine x₁ y₁).toPoint)
        (untwist (Point2.affine x₂ y₂).toPoint) (ofFpHom xt) (ofFpHom yt) := by
  have e₁ := (Point2.isOnCurve_affine x₁ y₁).mp h₁
  have e₂ := (Point2.isOnCurve_affine x₂ y₂).mp h₂
  rw [Point2.toPoint_affine h₁, Point2.toPoint_affine h₂]
  change _ = Miller.line ambientCurve (ShortWeierstrass.scaledHom ofFp2Hom w_ne_zero
    twist_coefficient _) (ShortWeierstrass.scaledHom ofFp2Hom w_ne_zero twist_coefficient _) _ _
  rw [ShortWeierstrass.line_scaledHom_some]
  have h2 : (2 : Fp2) ≠ 0 := fun h => absurd (congrArg Fp2.c0 h) (by decide)
  simp only [linefunc]
  by_cases hx : x₁ = x₂
  · subst hx
    by_cases hy : y₁ = y₂
    · subst hy
      have hy0 := hdeg rfl rfl
      have hny : ¬(y₁ = -y₁) := fun h => hy0 (by
        have : 2 * y₁ = 0 := by linear_combination h
        exact (mul_eq_zero.mp this).resolve_left h2)
      simp only [ne_eq, not_true_eq_false, ite_false, ite_true, true_and, hny]
      rw [slopeLine_eq, slope_of_Y_ne rfl (by rwa [ShortWeierstrass.negY_eq]),
        ShortWeierstrass.negY_eq]
      simp only [ShortWeierstrass.curve, Fp2.ofFp_two, Fp2.ofFp_three, Fp2.inv_eq_inv]
      have hl : 3 * x₁ * x₁ * (2 * y₁)⁻¹ =
          (3 * x₁ ^ 2 + 2 * 0 * x₁ + 0 - 0 * y₁) / (y₁ - -y₁) := by
        rw [show y₁ - -y₁ = 2 * y₁ by ring]
        field_simp
        ring
      rw [hl]
      ring
    · have hneg : y₁ = -y₂ := by
        rcases ShortWeierstrass.y_eq_or_eq_neg (a := 0) (b := b2) (x := x₁) (y1 := y₂) (y2 := y₁)
          (by rw [zero_mul, add_zero]; exact e₂) (by rw [zero_mul, add_zero]; exact e₁) with h | h
        · exact absurd h hy
        · exact h
      simp only [ne_eq, not_true_eq_false, ite_false, true_and, hneg, ite_true]
      rw [ite_eq_right_iff.mpr fun h => absurd (hneg ▸ h) hy, verticalLine_eq]
  · simp only [ne_eq, hx, not_false_eq_true, ite_true, false_and, ite_false]
    rw [slopeLine_eq, slope_of_X_ne hx]
    have hd : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    simp only [Fp2.inv_eq_inv, map_mul, map_inv₀, map_div₀, map_sub]
    have hd' : ofFp2Hom x₂ - ofFp2Hom x₁ ≠ 0 := by
      rw [← map_sub]; exact (map_ne_zero ofFp2Hom).mpr hd
    have hd'' : ofFp2Hom x₁ - ofFp2Hom x₂ ≠ 0 := by
      rw [← neg_sub]; exact neg_ne_zero.mpr hd'
    field_simp
    ring

/-- An element of `Fp2` is its two coefficients. -/
def fp2Equiv : Fp2 ≃ Fp × Fp where
  toFun a := (a.c0, a.c1)
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Fp2` is finite. -/
noncomputable instance : Fintype Fp2 := Fintype.ofEquiv _ fp2Equiv.symm

/-- `Fp2` has `p^2` elements. -/
theorem card_fp2 : Fintype.card Fp2 = Fp.modulus ^ 2 := by
  rw [Fintype.card_eq_nat_card, Nat.card_congr fp2Equiv, Nat.card_prod, Nat.card_fin, sq]

/-- The vertical `xt - x w^2` through the untwist of a point with `x ≠ 0` is not zero. -/
theorem vertical_ne_zero {x : Fp2} (hx : x ≠ 0) (xt : Fp) :
    ofFpHom xt - ofFp2Hom x * wPow 1 ^ 2 ≠ 0 := by
  rw [← verticalLine_eq]
  intro h
  have h8 := congrArg (fun v : Fp12 => v[8]) h
  have h2 := congrArg (fun v : Fp12 => v[2]) h
  simp [verticalLine] at h8 h2
  apply hx
  apply Fp2.ext
  · simpa [h8] using (sub_eq_zero.mp h2).symm
  · exact h8

/-- The final exponentiation sends that vertical to 1.

It is fixed by the `p^6`-th power, and `p^6 - 1` divides the final exponent. -/
theorem finalExponentiation_vertical {x : Fp2} (hx : x ≠ 0) (xt : Fp) :
    finalExponentiation (ofFpHom xt - ofFp2Hom x * wPow 1 ^ 2) = 1 := by
  set v := ofFpHom xt - ofFp2Hom x * wPow 1 ^ 2
  have hv := vertical_ne_zero hx xt
  have hxi : (⟨9, 1⟩ : Fp2) ^ (Fp.modulus ^ 2 - 1) = 1 := by
    rw [← card_fp2]
    exact FiniteField.pow_card_sub_one_eq_one _ xi_ne_zero
  have hw : (wPow 1 ^ 2) ^ Fp.modulus ^ 6 = wPow 1 ^ 2 := by
    rw [← pow_mul, show 2 * Fp.modulus ^ 6 = 6 * ((Fp.modulus ^ 2 - 1) *
      ((Fp.modulus ^ 6 - 1) / 3 / (Fp.modulus ^ 2 - 1))) + 2 by decide +kernel, pow_add,
      pow_mul, w_pow_six, ← map_pow, pow_mul, hxi, one_pow, map_one, one_mul]
  have hx6 : (ofFp2Hom x) ^ Fp.modulus ^ 6 = ofFp2Hom x := by
    rw [← map_pow, show Fp.modulus ^ 6 = (Fp.modulus ^ 2) ^ 3 by ring, ← card_fp2,
      FiniteField.pow_card_pow]
  have ht6 : (ofFpHom xt) ^ Fp.modulus ^ 6 = ofFpHom xt := by
    have h : xt ^ Fp.modulus ^ 6 = xt := ZMod.pow_card_pow (p := Fp.modulus) (n := 6) xt
    rw [← map_pow, h]
  have hp6 : v ^ Fp.modulus ^ 6 = v := by
    rw [sub_pow_expChar_pow, mul_pow, hw, hx6, ht6]
  have h1 : v ^ (Fp.modulus ^ 6 - 1) = 1 := by
    apply mul_right_cancel₀ hv
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by decide)), hp6, one_mul]
  rw [finalExponentiation_eq_pow, show FINAL_EXPONENT = (Fp.modulus ^ 6 - 1) *
    (FINAL_EXPONENT / (Fp.modulus ^ 6 - 1)) by decide +kernel, pow_mul, h1, one_pow]

/-! ## Points of the loop -/

/-- A point of the twist of prime order `q` is `(x, y)` with `x ≠ 0` and `y ≠ 0`.

Otherwise it would have order 2 or 3. -/
theorem exists_affine_of_order {T : Point2} (hT : T.isOnCurve = true)
    (hr : Fr.modulus • T.toPoint = 0) (h0 : T.toPoint ≠ 0) :
    ∃ x y, T = .affine x y ∧ x ≠ 0 ∧ y ≠ 0 := by
  have hsmall : ∀ m, m ∣ 6 → m • T.toPoint ≠ 0 := by
    intro m hm hm0
    have h1 : addOrderOf T.toPoint ∣ Nat.gcd m Fr.modulus :=
      Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hm0) (addOrderOf_dvd_of_nsmul_eq_zero hr)
    have hg : Nat.gcd m Fr.modulus = 1 := by
      have : Nat.gcd 6 Fr.modulus = 1 := by decide +kernel
      exact Nat.eq_one_of_dvd_one (this ▸ Nat.gcd_dvd_gcd_of_dvd_left _ hm)
    rw [hg, Nat.dvd_one, AddMonoid.addOrderOf_eq_one_iff] at h1
    exact h0 h1
  cases T with
  | infinity => exact absurd rfl h0
  | affine x y =>
    refine ⟨x, y, rfl, ?_, ?_⟩
    · rintro rfl
      apply hsmall 3 (by decide)
      rw [Point2.toPoint_affine hT]
      exact ShortWeierstrass.three_nsmul_some_zero _
    · rintro rfl
      apply hsmall 2 (by decide)
      rw [Point2.toPoint_affine hT, two_nsmul]
      exact ShortWeierstrass.add_of_y_eq_neg _ _ neg_zero.symm

/-- The final exponentiation sends Miller's vertical through the untwist of such a point to 1. -/
theorem finalExponentiation_line_neg {T : Point2} (hT : T.isOnCurve = true)
    (hr : Fr.modulus • T.toPoint = 0) (h0 : T.toPoint ≠ 0) (xp yp : Fp) :
    finalExponentiation (Miller.line ambientCurve (untwist T.toPoint) (-untwist T.toPoint)
      (ofFpHom xp) (ofFpHom yp)) = 1 := by
  obtain ⟨x, y, rfl, hx, -⟩ := exists_affine_of_order hT hr h0
  rw [Point2.toPoint_affine hT]
  change finalExponentiation (Miller.line ambientCurve (.some _ _ _) (-(.some _ _ _)) _ _) = 1
  rw [Miller.line_neg_self]
  exact finalExponentiation_vertical hx xp

/-- The opposite of a point `(x, y)` of the twist is `(x, -y)`. -/
theorem toPoint_affine_neg {x y : Fp2} (h : (Point2.affine x y).isOnCurve = true) :
    (Point2.affine x (-y)).isOnCurve = true ∧
      (Point2.affine x (-y)).toPoint = -(Point2.affine x y).toPoint := by
  have hc : (Point2.affine x (-y)).isOnCurve = true := by
    rw [Point2.isOnCurve_affine] at h ⊢
    rw [neg_mul_neg]
    exact h
  refine ⟨hc, ?_⟩
  rw [Point2.toPoint_affine h, Point2.toPoint_affine hc, Point.neg_some, Point.some.injEq,
    ShortWeierstrass.negY_eq]
  exact ⟨rfl, rfl⟩

/-- The final exponentiation commutes with division. -/
theorem finalExponentiation_div (a b : Fp12) :
    finalExponentiation (a / b) = finalExponentiation a / finalExponentiation b := by
  simp only [finalExponentiation_eq_pow, div_pow]

/-- Through `T` of order `q` and a finite `S`, the line of the specification is Miller's line.

Miller's line passes through the untwists of `T` and `S`. -/
theorem linefunc_eq_line_of_order {T S : Point2} (hT : T.isOnCurve = true)
    (hS : S.isOnCurve = true) (hTr : Fr.modulus • T.toPoint = 0) (hT0 : T.toPoint ≠ 0)
    (hS0 : S ≠ .infinity) (xp yp : Fp) :
    linefunc T S xp yp =
      Miller.line ambientCurve (untwist T.toPoint) (untwist S.toPoint) (ofFpHom xp)
        (ofFpHom yp) := by
  obtain ⟨x, y, rfl, -, hy⟩ := exists_affine_of_order hT hTr hT0
  cases S with
  | infinity => exact absurd rfl hS0
  | affine x' y' => exact linefunc_eq_line hT hS (fun _ _ => hy) xp yp

/-- Let `T` be a point of the twist of order `q`, and `S` a point with `T + S` of order `q`.

Take the product by the line of the specification through `T` and `S`.

After the final exponentiation, it is the product by Miller's `g_{T, S}` of the untwists. -/

theorem finalExponentiation_mul_linefunc {T S : Point2} (hT : T.isOnCurve = true)
    (hS : S.isOnCurve = true) (hTr : Fr.modulus • T.toPoint = 0) (hT0 : T.toPoint ≠ 0)
    (hS0 : S ≠ .infinity) (hTSr : Fr.modulus • (T + S).toPoint = 0)
    (hTS0 : (T + S).toPoint ≠ 0) (xp yp : Fp) {f f' : Fp12}
    (hf : finalExponentiation f = finalExponentiation f') :
    finalExponentiation (f * linefunc T S xp yp) =
      finalExponentiation (f' * Miller.lineRatio ambientCurve (untwist T.toPoint)
        (untwist S.toPoint) (ofFpHom xp) (ofFpHom yp)) := by
  rw [finalExponentiation_mul, finalExponentiation_mul, hf, Miller.lineRatio,
    finalExponentiation_div, ← map_add untwist, ← Point2.toPoint_add hT hS,
    finalExponentiation_line_neg (Point2.isOnCurve_add hT hS) hTSr hTS0 xp yp, div_one,
    linefunc_eq_line_of_order hT hS hTr hT0 hS0]

/-- One step of the loop of the specification: double, then add `q` if bit `i` is set. -/
private def loopStep (q : Point2) (xp yp : Fp) (i : ℕ) : Fp12 × Point2 → Fp12 × Point2 :=
  fun (f, r) =>
    let f := f * f * linefunc r r xp yp
    let r := r + r
    if ATE_LOOP_COUNT / 2 ^ i % 2 = 1 then (f * linefunc r q xp yp, r + q) else (f, r)


/-- The steps of the loop at bits `n - 1` down to `0`. -/
private def loopSteps (q : Point2) (xp yp : Fp) : ℕ → Fp12 × Point2 → Fp12 × Point2
  | 0, acc => acc
  | n + 1, acc => loopSteps q xp yp n (loopStep q xp yp n acc)

/-- The loop of the specification walks bits `n` down to `0`. -/
private theorem foldl_loopStep (q : Point2) (xp yp : Fp) (n : ℕ) (acc : Fp12 × Point2) :
    (List.range (n + 1)).foldl (fun acc step => loopStep q xp yp (n - step) acc) acc =
      loopSteps q xp yp (n + 1) acc := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    simp only [Nat.succ_sub_succ]
    rw [ih]
    rfl

/-- The Miller loop of the specification: 64 steps, then the two lines. -/
private theorem millerLoop_eq (q : Point2) (xp yp : Fp) :
    millerLoop q xp yp =
      (loopSteps q xp yp 64 (Fp12.one, q)).1 *
        linefunc (loopSteps q xp yp 64 (Fp12.one, q)).2 (frobenius q) xp yp *
        linefunc ((loopSteps q xp yp 64 (Fp12.one, q)).2 + frobenius q)
          (match frobenius (frobenius q) with
            | .affine x y => .affine x (-y)
            | .infinity => .infinity) xp yp := by
  rw [← foldl_loopStep]
  rfl

/-- `6 u + 2 < q`, so no multiple `k Q` of the loop, with `0 < k ≤ 6 u + 2`, is `O`. -/
theorem ateLoopCount_lt : ATE_LOOP_COUNT < Fr.modulus := by decide +kernel

/-- Under the final exponentiation, the steps of the specification are Miller's algorithm.

Miller's algorithm runs on the untwists.


The invariant is that `T` is `k Q`, where `k` is the part of `6 u + 2` above the bits left.

At the end, the point of the steps is `(6 u + 2) Q`. -/
private theorem finalExponentiation_loopSteps {Q : Point2}
 (hQ : Q.isOnCurve = true)
    (hord : addOrderOf Q.toPoint = Fr.modulus) (xp yp : Fp) :
    ∀ (n : ℕ) (T : Point2) (f f' : Fp12), T.isOnCurve = true →
      T.toPoint = (ATE_LOOP_COUNT / 2 ^ n) • Q.toPoint → 0 < ATE_LOOP_COUNT / 2 ^ n →
      finalExponentiation f = finalExponentiation f' →
      finalExponentiation (loopSteps Q xp yp n (f, T)).1 =
          finalExponentiation (Miller.steps ambientCurve ATE_LOOP_COUNT (untwist Q.toPoint)
            (ofFpHom xp) (ofFpHom yp) n (untwist T.toPoint) f') ∧
        (loopSteps Q xp yp n (f, T)).2.isOnCurve = true ∧
        (loopSteps Q xp yp n (f, T)).2.toPoint = ATE_LOOP_COUNT • Q.toPoint := by
  have hr : ∀ j : ℕ, Fr.modulus • (j • Q.toPoint) = 0 := fun j => by
    rw [smul_comm, ← hord, addOrderOf_nsmul_eq_zero, smul_zero]
  have hne : ∀ j, 0 < j → j ≤ ATE_LOOP_COUNT → j • Q.toPoint ≠ 0 := fun j hj0 hjs h =>
    absurd (Nat.le_of_dvd hj0 (hord ▸ addOrderOf_dvd_of_nsmul_eq_zero h))
      (by have := ateLoopCount_lt; omega)
  have hQ0 : Q ≠ .infinity := fun h =>
    hne 1 one_pos (by decide) (by rw [one_nsmul, h, Point2.toPoint_infinity])
  intro n
  induction n with
  | zero =>
    intro T f f' hT hk _ hf
    simp only [pow_zero, Nat.div_one] at hk
    exact ⟨hf, hT, hk⟩
  | succ n ih =>
    intro T f f' hT hk hpos hf
    set k := ATE_LOOP_COUNT / 2 ^ (n + 1)
    have hsplit : ATE_LOOP_COUNT / 2 ^ n = 2 * k + ATE_LOOP_COUNT / 2 ^ n % 2 := by
      have h1 : k = ATE_LOOP_COUNT / 2 ^ n / 2 := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
      omega
    have hle : ATE_LOOP_COUNT / 2 ^ n ≤ ATE_LOOP_COUNT := Nat.div_le_self _ _
    have hT2 := Point2.isOnCurve_add hT hT
    have hk2 : (T + T).toPoint = (2 * k) • Q.toPoint := by
      rw [Point2.toPoint_add hT hT, hk, two_mul, add_nsmul]
    have hD := finalExponentiation_mul_linefunc hT hT (by rw [hk]; exact hr k)
      (by rw [hk]; exact hne k hpos (by omega)) (fun h => hne k hpos (by omega) (by
        rw [← hk, h, Point2.toPoint_infinity]))
      (by rw [hk2]; exact hr _) (by rw [hk2]; exact hne (2 * k) (by omega) (by omega)) xp yp
      (f := f * f) (f' := f' ^ 2) (by rw [finalExponentiation_mul, hf, sq,
        finalExponentiation_mul])
    have hg2 : untwist (T + T).toPoint = untwist T.toPoint + untwist T.toPoint := by
      rw [Point2.toPoint_add hT hT, map_add]
    rw [loopSteps, Miller.steps_succ, Nat.testBit_eq_decide_div_mod_eq]
    by_cases hb : ATE_LOOP_COUNT / 2 ^ n % 2 = 1
    · rw [decide_eq_true hb, ite_eq_left rfl]
      have hT3 := Point2.isOnCurve_add hT2 hQ
      have hk3 : (T + T + Q).toPoint = (2 * k + 1) • Q.toPoint := by
        rw [Point2.toPoint_add hT2 hQ, hk2, add_nsmul, one_nsmul]
      have hA := finalExponentiation_mul_linefunc hT2 hQ (by rw [hk2]; exact hr _)
        (by rw [hk2]; exact hne (2 * k) (by omega) (by omega)) hQ0 (by rw [hk3]; exact hr _)
        (by rw [hk3]; exact hne (2 * k + 1) (by omega) (by omega)) xp yp hD
      have hg3 : untwist (T + T + Q).toPoint =
          untwist T.toPoint + untwist T.toPoint + untwist Q.toPoint := by
        rw [Point2.toPoint_add hT2 hQ, map_add, hg2]
      have hstep : loopStep Q xp yp n (f, T) =
          (f * f * linefunc T T xp yp * linefunc (T + T) Q xp yp, T + T + Q) := by
        simp only [loopStep]
        rw [ite_eq_left hb]
      rw [hstep, ← hg3, ← hg2]
      exact ih _ _ _ hT3 (by rw [hk3]; congr 1; omega) (by omega) hA
    · rw [decide_eq_false hb, ite_eq_right Bool.false_ne_true]
      have hstep : loopStep Q xp yp n (f, T) = (f * f * linefunc T T xp yp, T + T) := by
        simp only [loopStep]
        rw [ite_eq_right hb]
      rw [hstep, ← hg2]
      exact ih _ _ _ hT2 (by rw [hk2]; congr 1; omega) (by omega) hD

/-! ## The pairing -/

/-- The Frobenius image of a point whose `q`-multiple is `O` has the same property. -/
theorem frobenius_order {Q : Point2} (hQ : Q.isOnCurve = true)
    (hr : Fr.modulus • Q.toPoint = 0) : Fr.modulus • (frobenius Q).toPoint = 0 := by
  apply untwist_injective
  rw [map_nsmul, (untwist_frobenius hQ).2, ← map_nsmul, ← map_nsmul, hr, map_zero, map_zero]

/-- The pairing of alt_bn128 is the final exponentiation of Miller's algorithm and two lines.

Write `Q'` for the untwist of `Q`, `pi` for the `p`-th power map, and `s = 6 u + 2`.

The algorithm computes `f_{s, Q'}` at `P = (xp, yp)`.

The lines pass through `s Q'` and `pi(Q')`, then through `s Q' + pi(Q')` and `-pi(pi(Q'))`.

`Q` is on the twist and `q Q = O`; `P` is any pair, since the pairing does not check it. -/
theorem pairing_eq_finalExponentiation_loop {Q : Point2} (hQ : Q.isOnCurve = true)
    (hQr : Fr.modulus • Q.toPoint = 0) (xp yp : Fp) :
    pairing (.affine xp yp) Q = finalExponentiation
      (Miller.loop ambientCurve ATE_LOOP_COUNT (untwist Q.toPoint) (ofFpHom xp) (ofFpHom yp) *
        Miller.line ambientCurve (ATE_LOOP_COUNT • untwist Q.toPoint)
          (frobeniusHom (untwist Q.toPoint)) (ofFpHom xp) (ofFpHom yp) *
        Miller.line ambientCurve
          (ATE_LOOP_COUNT • untwist Q.toPoint + frobeniusHom (untwist Q.toPoint))
          (-frobeniusHom (frobeniusHom (untwist Q.toPoint))) (ofFpHom xp) (ofFpHom yp)) := by
  cases Q with
  | infinity =>
    simp only [Point2.toPoint_infinity, map_zero, Miller.loop_zero, nsmul_zero, add_zero,
      neg_zero, Miller.line_zero_zero, mul_one]
    rw [finalExponentiation_eq_pow, one_pow]
    rfl
  | affine xq yq =>
    have hQ0 : (Point2.affine xq yq).toPoint ≠ 0 := by
      rw [Point2.toPoint_affine hQ]
      exact fun h => by cases h
    have hord := addOrderOf_eq_prime hQr hQ0
    have hne : ∀ j, 0 < j → j ≤ ATE_LOOP_COUNT → j • (Point2.affine xq yq).toPoint ≠ 0 :=
      fun j hj0 hjs h => absurd (Nat.le_of_dvd hj0 (hord ▸ addOrderOf_dvd_of_nsmul_eq_zero h))
        (by have := ateLoopCount_lt; omega)
    obtain ⟨hF, hRc, hR⟩ := finalExponentiation_loopSteps hQ hord xp yp 64 _ Fp12.one 1 hQ
      (by rw [show ATE_LOOP_COUNT / 2 ^ 64 = 1 by decide, one_nsmul]) (by decide) rfl
    have hlog : ATE_LOOP_COUNT.log2 = 64 :=
      (Nat.log2_eq_iff (by decide)).mpr ⟨by decide, by decide⟩
    change finalExponentiation (millerLoop _ xp yp) = _
    rw [millerLoop_eq, Miller.loop, hlog]
    set R := (loopSteps (Point2.affine xq yq) xp yp 64 (Fp12.one, Point2.affine xq yq)).2
    set F := (loopSteps (Point2.affine xq yq) xp yp 64 (Fp12.one, Point2.affine xq yq)).1
    set Q := Point2.affine xq yq
    obtain ⟨hq1, hq1u⟩ := untwist_frobenius hQ
    obtain ⟨hq2, hq2u⟩ := untwist_frobenius hq1
    have hq1r := frobenius_order hQ hQr
    have hq2r := frobenius_order hq1 hq1r
    obtain ⟨X2, Y2, hq2eq⟩ : ∃ X2 Y2, frobenius (frobenius Q) = .affine X2 Y2 := ⟨_, _, rfl⟩
    rw [hq2eq] at hq2 hq2u hq2r ⊢
    obtain ⟨hn2, hn2u⟩ := toPoint_affine_neg hq2
    have hn2r : Fr.modulus • (Point2.affine X2 (-Y2)).toPoint = 0 := by
      simp [hn2u, hq2r]
    have hn20 : (Point2.affine X2 (-Y2)).toPoint ≠ 0 := by
      rw [Point2.toPoint_affine hn2]
      exact fun h => by cases h
    have hRr : Fr.modulus • R.toPoint = 0 := by
      rw [hR, smul_comm, hQr, nsmul_zero]
    have hR0 : R.toPoint ≠ 0 := by
      rw [hR]
      exact hne _ (by decide +kernel) le_rfl
    have hq10 : frobenius Q ≠ .infinity := by
      simp only [Q, frobenius]
      exact fun h => Point2.noConfusion h

    have e1 : ATE_LOOP_COUNT • untwist Q.toPoint = untwist R.toPoint := by rw [hR, map_nsmul]
    have e3 : -frobeniusHom (frobeniusHom (untwist Q.toPoint)) =
        untwist (Point2.affine X2 (-Y2)).toPoint := by
      rw [hn2u, map_neg, hq2u, hq1u]
    have hl2 : finalExponentiation (linefunc (R + frobenius Q) (Point2.affine X2 (-Y2)) xp yp) =
        finalExponentiation (Miller.line ambientCurve (untwist (R + frobenius Q).toPoint)
          (untwist (Point2.affine X2 (-Y2)).toPoint) (ofFpHom xp) (ofFpHom yp)) := by
      by_cases h0 : (R + frobenius Q).toPoint = 0
      · have hinf := (Point2.toPoint_eq_zero (Point2.isOnCurve_add hRc hq1)).mp h0
        obtain ⟨x, y, hxy, hx, -⟩ := exists_affine_of_order hn2 hn2r hn20
        rw [hinf, Point2.toPoint_infinity, map_zero]
        rw [hxy] at hn2 ⊢
        rw [Point2.toPoint_affine hn2]
        change finalExponentiation Fp12.one = finalExponentiation
          (Miller.line ambientCurve 0 (ShortWeierstrass.scaledHom ofFp2Hom w_ne_zero
            twist_coefficient (.some _ _ _)) _ _)
        rw [ShortWeierstrass.line_zero_scaledHom_some, finalExponentiation_vertical hx,
          finalExponentiation_eq_pow]
        exact one_pow _
      · rw [linefunc_eq_line_of_order (Point2.isOnCurve_add hRc hq1) hn2
          (by rw [Point2.toPoint_add hRc hq1, nsmul_add, hRr, hq1r, add_zero]) h0

          (fun h => Point2.noConfusion h)]
    rw [e3, ← hq1u, e1, ← map_add, ← Point2.toPoint_add hRc hq1]
    simp only [finalExponentiation_mul]
    rw [hF, linefunc_eq_line_of_order hRc hq1 hRr hR0 hq10, hl2]


end EthLib.Cryptography.AltBn128
