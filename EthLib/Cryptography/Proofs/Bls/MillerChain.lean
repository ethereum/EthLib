module

public import EthLib.Cryptography.Proofs.Bls.MillerLoop
public import EthLib.Cryptography.Proofs.Bls.G2Subgroup
public import EthLib.Cryptography.Proofs.MillerFunction

/-!
# Proofs: the pairing is the final exponentiation of Miller's algorithm

The pairing runs a loop on the twist and multiplies by scaled lines.

Miller's algorithm runs on the untwisted point in `E(Fp12)` and multiplies by `g_{T,S}`.

That function is the line through `T` and `S`, divided by the vertical through `T + S`.

Each step of the loop and of the algorithm differ by three factors.

- The loop scales each line by `c w^3`, with `c` a nonzero element of `Fp2`.
- The loop's line is the opposite of the normalized line.
- The loop omits the vertical, whose value at `P` is a nonzero element of `Fp6`.

The final exponentiation sends each of these factors to 1.

The steps need `T` finite, `Y ≠ 0` to double and an `x` other than that of `Q` to add.

The loop keeps `T = k Q`, where `k` is the part of `|x|` read so far, so `0 < k ≤ |x|`.

`Q` has the prime order `r`, and `|x| < r`, so no step meets the point at infinity.

The vertical is nonzero because no point of the twist has `x = 0`.

That holds because `4 (1 + i)` is not a square in `Fp2`: its norm is 32, and 2 is not a square.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

open TwistFrobenius WeierstrassCurve.Affine

/-- The final exponentiation sends every nonzero element of `Fp6` to 1. -/
theorem finalExponentiation_fp6 {c : Fp6} (hc : c ≠ 0) :
    finalExponentiation (fp6ToFp12 c) = 1 := by
  have hc6 : c ^ (Fp.modulus ^ 6 - 1) = 1 := by
    rw [← card_fp6]
    exact FiniteField.pow_card_sub_one_eq_one c hc
  rw [finalExponentiation_eq_pow, show finalExpExponent = (Fp.modulus ^ 6 - 1) *
      (finalExpExponent / (Fp.modulus ^ 6 - 1)) by decide +kernel, pow_mul, ← map_pow, hc6,
    map_one, one_pow]

/-- At `x = a`, the vertical through the untwist of a point of the twist with `x = b` lies in `Fp6`.
-/
theorem vertical_eq (a : Fp) (b : Fp2) :
    fpToFp12 a - fp2ToFp12 b * w⁻¹ ^ 2 =
      fp6ToFp12 (fp2ToFp6 (Fp2.ofFp a) - fp2ToFp6 b * Fp6.v⁻¹) := by
  rw [inv_pow, w_squared, ← map_inv₀, map_sub, map_mul]
  rfl

/-- That element of `Fp6` is not zero when the point of the twist has `x ≠ 0`. -/
theorem vertical_ne_zero {b : Fp2} (hb : b ≠ 0) (a : Fp) :
    fp2ToFp6 (Fp2.ofFp a) - fp2ToFp6 b * Fp6.v⁻¹ ≠ 0 := by
  intro h
  have hv : (Fp6.v : Fp6) ≠ 0 := fun h => by simpa using congrArg Fp6.c1 h
  have h' : fp2ToFp6 (Fp2.ofFp a) * Fp6.v = fp2ToFp6 b := by
    rw [sub_eq_zero] at h
    rw [h, mul_assoc, inv_mul_cancel₀ hv, mul_one]
  have h0 := congrArg Fp6.c0 h'
  simp at h0
  exact hb h0.symm

/-- No point of the twist has `x = 0`, because `4 (1 + i)` is not a square in `Fp2`. -/
theorem twist_x_ne_zero {x y : Fp2} (h : G2.curve.toAffine.Nonsingular x y) : x ≠ 0 := by
  rintro rfl
  have he : y * y = 2 * 2 * Fp2.xi := by
    have h1 := h.1
    rw [equation_iff] at h1
    simp only [G2.curve, WeierstrassCurve.Jacobian.toAffine] at h1
    rw [show (2 : Fp2) * 2 * Fp2.xi = G2.bTwist by decide_eq_at_model [Fp2.xi, G2.map_bTwist]]
    linear_combination h1
  have hn := congrArg Fp2.norm he
  simp only [Fp2.norm_mul] at hn
  have h2 : Fp2.norm 2 = 0 := Fp12.sq_eq_two_mul_sq_zmod (nxi := Fp2.norm Fp2.xi) rfl hn
  exact absurd h2 (by decide_eq_at_model [Fp2.norm])

/-- The final exponentiation commutes with division. -/
theorem finalExponentiation_div (a b : Fp12) :
    finalExponentiation (a / b) = finalExponentiation a / finalExponentiation b := by
  simp only [finalExponentiation_eq_pow, div_pow]

/-- The final exponentiation ignores the sign, because its exponent is even. -/
theorem finalExponentiation_neg (a : Fp12) : finalExponentiation (-a) = finalExponentiation a := by
  simp only [finalExponentiation_eq_pow]
  exact Even.neg_pow (by decide +kernel) a

/-- The final exponentiation commutes with powers. -/
theorem finalExponentiation_pow (a : Fp12) (n : ℕ) :
    finalExponentiation (a ^ n) = finalExponentiation a ^ n := by
  simp only [finalExponentiation_eq_pow, ← pow_mul, mul_comm]

/-- A valid finite point of `G2` is the affine point `(X / Z^2, Y / Z^3)`. -/
theorem toPoint_eq_some {T : G2} (hT : G2.Valid T) (hz : T.z ≠ 0) :
    ∃ h, G2.toPoint T = .some (T.x / T.z ^ 2) (T.y / T.z ^ 3) h :=
  ⟨_, WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero (W := G2.curve) hT hz⟩

/-- The untwist of a valid finite point of `G2`. -/
theorem g2Hom_toPoint {T : G2} (hT : G2.Valid T) (hz : T.z ≠ 0) :
    ∃ h, g2Hom (G2.toPoint T) = .some (untwist (T.x / T.z ^ 2) (T.y / T.z ^ 3)).1
      (untwist (T.x / T.z ^ 2) (T.y / T.z ^ 3)).2 h := by
  obtain ⟨h, hT'⟩ := toPoint_eq_some hT hz
  exact ⟨_, by rw [hT']; rfl⟩

/-- The untwist of a valid affine point `(x, y, 1)` of `G2`. -/
theorem g2Hom_toPoint_affine {xq yq : Fp2} (hQ : G2.Valid ⟨xq, yq, Fp2.one⟩) :
    ∃ h, g2Hom (G2.toPoint ⟨xq, yq, Fp2.one⟩) = .some (untwist xq yq).1 (untwist xq yq).2 h := by
  obtain ⟨h, hg⟩ := g2Hom_toPoint hQ (one_ne_zero : (1 : Fp2) ≠ 0)
  have e1 : xq / Fp2.one ^ 2 = xq := by rw [show Fp2.one = 1 from rfl, one_pow, div_one]
  have e2 : yq / Fp2.one ^ 3 = yq := by rw [show Fp2.one = 1 from rfl, one_pow, div_one]
  simp only [e1, e2] at h hg
  exact ⟨h, hg⟩

/-- The final exponentiation of the vertical through the untwist of a finite point is 1. -/
theorem finalExponentiation_vertical {T : G2} (hT : G2.Valid T) (hz : T.z ≠ 0) (xp yp : Fp) :
    finalExponentiation
      (Miller.line ambientCurve (g2Hom (G2.toPoint T)) (-g2Hom (G2.toPoint T))
        (fpToFp12 xp) (fpToFp12 yp)) = 1 := by
  obtain ⟨h, hT'⟩ := toPoint_eq_some hT hz
  obtain ⟨h', hg⟩ := g2Hom_toPoint hT hz
  rw [hg, Miller.line_neg_self, untwist, vertical_eq]
  exact finalExponentiation_fp6 (vertical_ne_zero (twist_x_ne_zero h) xp)

private theorem fp2ToFp12_ne_zero {a : Fp2} (h : a ≠ 0) : fp2ToFp12 a ≠ 0 :=
  (map_ne_zero fp2ToFp12).mpr h

private theorem two_ne_zero_fp12 : (2 : Fp12) ≠ 0 := by
  rw [← map_ofNat fp2ToFp12 2]
  exact fp2ToFp12_ne_zero (by decide_eq_at_model [])

/-- At a point with `Y ≠ 0`, the tangent of Miller's algorithm is the opposite of the loop's line.
-/
theorem line_tangent_eq {X Y : Fp12} (h : ambientCurve.Nonsingular X Y) (hY : Y ≠ 0)
    (xp yp : Fp) :
    Miller.line ambientCurve (.some X Y h) (.some X Y h) (fpToFp12 xp) (fpToFp12 yp) =
      -lineAt X Y (3 * X ^ 2 / (2 * Y)) xp yp := by
  have hneg : ambientCurve.negY X Y = -Y := ShortWeierstrass.negY_eq X Y
  have hxy : ¬(X = X ∧ Y = ambientCurve.negY X Y) := by
    rw [hneg]
    rintro ⟨-, h2⟩
    have h2Y : 2 * Y = 0 := by linear_combination h2
    exact hY ((mul_eq_zero.mp h2Y).resolve_left two_ne_zero_fp12)
  rw [Miller.line_some_some _ h h hxy, slope_of_Y_ne rfl (fun h => hxy ⟨rfl, h⟩), hneg]
  simp only [ambientCurve, ShortWeierstrass.curve, lineAt]
  have h2 := two_ne_zero_fp12
  have h22 : (2 : Fp12)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
  field_simp
  linear_combination (3 * X ^ 2 * fpToFp12 xp - 3 * X ^ 3) * h22

/-- The same holds at the untwist of a finite point of `G2` with `Y ≠ 0`. -/
theorem line_tangent {T : G2} (hT : G2.Valid T) (hz : T.z ≠ 0) (hy : T.y ≠ 0) (xp yp : Fp) :
    Miller.line ambientCurve (g2Hom (G2.toPoint T)) (g2Hom (G2.toPoint T))
        (fpToFp12 xp) (fpToFp12 yp) =
      -lineAt (untwist (T.x / T.z ^ 2) (T.y / T.z ^ 3)).1
        (untwist (T.x / T.z ^ 2) (T.y / T.z ^ 3)).2
        (3 * (untwist (T.x / T.z ^ 2) (T.y / T.z ^ 3)).1 ^ 2 /
          (2 * (untwist (T.x / T.z ^ 2) (T.y / T.z ^ 3)).2)) xp yp := by
  obtain ⟨h, hg⟩ := g2Hom_toPoint hT hz
  rw [hg]
  exact line_tangent_eq h (mul_ne_zero (fp2ToFp12_ne_zero (div_ne_zero hy (pow_ne_zero 3 hz)))
    (pow_ne_zero 3 (inv_ne_zero w_ne_zero))) xp yp

/-- Through two points with different `x`, the chord is the opposite of the loop's line. -/
theorem line_chord_eq {X Y X' Y' : Fp12} (h : ambientCurve.Nonsingular X Y)
    (h' : ambientCurve.Nonsingular X' Y') (hX : X ≠ X') (xp yp : Fp) :
    Miller.line ambientCurve (.some X Y h) (.some X' Y' h') (fpToFp12 xp) (fpToFp12 yp) =
      -lineAt X Y ((Y' - Y) / (X' - X)) xp yp := by
  rw [Miller.line_some_some _ h h' (fun hxy => hX hxy.1), slope_of_X_ne hX]
  simp only [lineAt]
  have h1 : X - X' ≠ 0 := sub_ne_zero.mpr hX
  have h2 : X' - X ≠ 0 := sub_ne_zero.mpr (Ne.symm hX)
  field_simp
  ring

/-- The same holds at the untwists of a finite `T` and of `Q = (xq, yq)` with different `x`. -/
theorem line_chord {T : G2} {xq yq : Fp2} (hT : G2.Valid T) (hz : T.z ≠ 0)
    (hQ : G2.Valid ⟨xq, yq, Fp2.one⟩) (hx : xq * T.z ^ 2 - T.x ≠ 0) (xp yp : Fp) :
    Miller.line ambientCurve (g2Hom (G2.toPoint T)) (g2Hom (G2.toPoint ⟨xq, yq, Fp2.one⟩))
        (fpToFp12 xp) (fpToFp12 yp) =
      -lineAt (untwist (T.x / T.z ^ 2) (T.y / T.z ^ 3)).1
        (untwist (T.x / T.z ^ 2) (T.y / T.z ^ 3)).2
        (((untwist xq yq).2 - (untwist (T.x / T.z ^ 2) (T.y / T.z ^ 3)).2) /
          ((untwist xq yq).1 - (untwist (T.x / T.z ^ 2) (T.y / T.z ^ 3)).1)) xp yp := by
  obtain ⟨h, hg⟩ := g2Hom_toPoint hT hz
  obtain ⟨h', hg'⟩ := g2Hom_toPoint_affine hQ
  rw [hg, hg']
  refine line_chord_eq h h' (fun hX => hx ?_) xp yp
  have hX' := (ShortWeierstrass.scaled_x_eq_iff fp2ToFp12 (inv_ne_zero w_ne_zero) _ _).mp hX
  rw [← hX', div_mul_cancel₀ _ (pow_ne_zero 2 hz), sub_self]

private theorem two_ne_zero_fp2 : (2 : Fp2) ≠ 0 := by decide_eq_at_model []

/-- After the final exponentiation, a doubling step multiplies by the square and by `g_{T,T}`. -/
theorem finalExponentiation_millerDouble {T : G2} (hT : G2.Valid T) (hz : T.z ≠ 0)
    (hy : T.y ≠ 0) (h2 : T.double.z ≠ 0) (xp yp : Fp) {f f' : Fp12}
    (hf : finalExponentiation f = finalExponentiation f') :
    finalExponentiation (millerDouble T xp yp f).2 =
      finalExponentiation (f' ^ 2 * Miller.lineRatio ambientCurve (g2Hom (G2.toPoint T))
        (g2Hom (G2.toPoint T)) (fpToFp12 xp) (fpToFp12 yp)) := by
  have hd := millerDouble_snd hz hy xp yp f
  have hc : 2 * T.y * T.z ^ 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero_fp2 hy) (pow_ne_zero 3 hz)
  simp only at hd
  rw [hd, Miller.lineRatio, ← map_add, ← G2.toPoint_double hT, line_tangent hT hz hy,
    finalExponentiation_mul (f * f), finalExponentiation_mul (fp2ToFp12 _ * w ^ 3),
    finalExponentiation_fp2_mul_w_cube hc]
  simp only [finalExponentiation_mul, finalExponentiation_div, finalExponentiation_neg,
    finalExponentiation_pow, finalExponentiation_vertical (G2.valid_double hT) h2, div_one, hf]
  ring

/-- After the final exponentiation, an addition step multiplies by `g_{T,Q}`. -/
theorem finalExponentiation_millerAdd {T : G2} {xq yq : Fp2} (hT : G2.Valid T)
    (hz : T.z ≠ 0) (hQ : G2.Valid ⟨xq, yq, Fp2.one⟩) (hx : xq * T.z ^ 2 - T.x ≠ 0)
    (h2 : (T.add ⟨xq, yq, Fp2.one⟩).z ≠ 0) (xp yp : Fp) {f f' : Fp12}
    (hf : finalExponentiation f = finalExponentiation f') :
    finalExponentiation (millerAdd T xq yq xp yp f).2 =
      finalExponentiation (f' * Miller.lineRatio ambientCurve (g2Hom (G2.toPoint T))
        (g2Hom (G2.toPoint ⟨xq, yq, Fp2.one⟩)) (fpToFp12 xp) (fpToFp12 yp)) := by
  have hd := millerAdd_snd (yq := yq) hz hx xp yp f
  have hc : (xq * T.z ^ 2 - T.x) * T.z ≠ 0 := mul_ne_zero hx hz
  simp only at hd
  rw [hd, Miller.lineRatio, ← map_add, ← G2.toPoint_add hT hQ, line_chord hT hz hQ hx,
    finalExponentiation_mul f, finalExponentiation_mul (fp2ToFp12 _ * w ^ 3),
    finalExponentiation_fp2_mul_w_cube hc]
  simp only [finalExponentiation_mul, finalExponentiation_div, finalExponentiation_neg,
    finalExponentiation_vertical (G2.valid_add hT hQ) h2, div_one, hf]
  ring

/-- A multiple `k Q` with `0 < k < r` of a point of order `r` is not 0. -/
private theorem nsmul_ne_zero_of_lt {P : G2.curve.toAffine.Point}
    (hP : addOrderOf P = Fr.modulus) {k : ℕ} (hk0 : 0 < k) (hkr : k < Fr.modulus) : k • P ≠ 0 :=
  fun h => absurd (Nat.le_of_dvd hk0 (hP ▸ addOrderOf_dvd_of_nsmul_eq_zero h)) (by omega)

/-- A valid point that is not 0 in the group has `z ≠ 0`. -/
private theorem z_ne_zero_of_toPoint {T : G2} (h : G2.toPoint T ≠ 0) : T.z ≠ 0 :=
  fun hz => h (WeierstrassCurve.Jacobian.Point.toAffine_of_Z_eq_zero hz)

/-- One step of the loop: double, then add `Q` if the bit is set. -/
theorem millerSteps_succ (s : ℕ) (xq yq : Fp2) (xp yp : Fp) (n : ℕ) (T : G2) (f : Fp12) :
    millerSteps s xq yq xp yp (n + 1) T f =
      if (s >>> n) &&& 1 = 1 then
        millerSteps s xq yq xp yp n (millerAdd (millerDouble T xp yp f).1 xq yq xp yp
          (millerDouble T xp yp f).2).1 (millerAdd (millerDouble T xp yp f).1 xq yq xp yp
          (millerDouble T xp yp f).2).2
      else millerSteps s xq yq xp yp n (millerDouble T xp yp f).1 (millerDouble T xp yp f).2 := by
  rw [millerSteps]
  generalize millerDouble T xp yp f = d
  obtain ⟨T2, f2⟩ := d
  dsimp only
  split_ifs
  · generalize millerAdd T2 xq yq xp yp f2 = a
    obtain ⟨T3, f3⟩ := a
    rfl
  · rfl

private theorem bit_iff (s n : ℕ) : (s >>> n) &&& 1 = 1 ↔ s.testBit n = true := by
  rw [Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow,
    decide_eq_true_iff]

/-- Let `T` represent `j Q`, and let `(j - 1) Q` and `(j + 1) Q` be nonzero.

Then `T` and `Q` have different `x`. -/
private theorem x_ne_of_nsmul {T : G2} {xq yq : Fp2} (hT : G2.Valid T) (hz : T.z ≠ 0)
    (hQ : G2.Valid ⟨xq, yq, Fp2.one⟩) {j : ℕ} (hj : 1 ≤ j)
    (hTj : G2.toPoint T = j • G2.toPoint ⟨xq, yq, Fp2.one⟩)
    (hm : (j - 1) • G2.toPoint ⟨xq, yq, Fp2.one⟩ ≠ 0)
    (hp : (j + 1) • G2.toPoint ⟨xq, yq, Fp2.one⟩ ≠ 0) : xq * T.z ^ 2 - T.x ≠ 0 := by
  intro hx0
  obtain ⟨h, e⟩ := toPoint_eq_some hT hz
  obtain ⟨h', e'⟩ := toPoint_eq_some hQ (one_ne_zero : (1 : Fp2) ≠ 0)
  have hX : T.x / T.z ^ 2 = xq / Fp2.one ^ 2 := by
    rw [show Fp2.one = 1 from rfl, one_pow, div_one, div_eq_iff (pow_ne_zero 2 hz)]
    linear_combination -hx0
  rcases (Point.X_eq_iff (h₁ := h) (h₂ := h')).mp hX with heq | heq
  · rw [← e, ← e', hTj] at heq
    apply hm
    have hj' : j = (j - 1) + 1 := by omega
    rw [hj', add_nsmul, one_nsmul] at heq
    simpa [Nat.add_sub_cancel] using heq
  · rw [← e, ← e', hTj] at heq
    apply hp
    rw [add_nsmul, one_nsmul, heq, neg_add_cancel]

/-- Under the final exponentiation, the loop of the specification agrees with Miller's algorithm.

The invariant is that `T` represents `k Q`, where `k` is the part of `s` read so far.

Since `0 < k ≤ s < r` and `Q` has order `r`, no step meets the point at infinity. -/
theorem finalExponentiation_millerSteps {s : ℕ} (hs : s < Fr.modulus) {xq yq : Fp2}
    (hQ : G2.Valid ⟨xq, yq, Fp2.one⟩)
    (hord : addOrderOf (G2.toPoint ⟨xq, yq, Fp2.one⟩) = Fr.modulus) (xp yp : Fp) :
    ∀ (n : ℕ) (T : G2) (f f' : Fp12), G2.Valid T →
      G2.toPoint T = (s >>> n) • G2.toPoint ⟨xq, yq, Fp2.one⟩ → 0 < s >>> n →
      finalExponentiation f = finalExponentiation f' →
      finalExponentiation (millerSteps s xq yq xp yp n T f) =
        finalExponentiation (Miller.steps ambientCurve s (g2Hom (G2.toPoint ⟨xq, yq, Fp2.one⟩))
          (fpToFp12 xp) (fpToFp12 yp) n (g2Hom (G2.toPoint T)) f') := by
  intro n
  induction n with
  | zero => intro T f f' _ _ _ hf; exact hf
  | succ n ih =>
    intro T f f' hT hk hpos hf
    set Q1 : G2 := ⟨xq, yq, Fp2.one⟩
    set k := s >>> (n + 1)
    have hsplit := Miller.shiftRight_split s n
    have hle : s >>> n ≤ s := Nat.shiftRight_le s n
    have hne : ∀ j, 0 < j → j ≤ s → j • G2.toPoint Q1 ≠ 0 :=
      fun j hj0 hjs => nsmul_ne_zero_of_lt hord hj0 (by omega)
    have hz : T.z ≠ 0 := z_ne_zero_of_toPoint (hk ▸ hne k hpos (by omega))
    have hy : T.y ≠ 0 := by
      intro hy0
      have hTneg : G2.neg T = T := by
        cases T
        simp_all [G2.neg]
      have h2 := G2.toPoint_neg hT
      rw [hTneg] at h2
      have : (2 * k) • G2.toPoint Q1 = 0 := by
        rw [two_mul, add_nsmul, ← hk]
        exact add_eq_zero_iff_eq_neg.mpr h2
      exact hne (2 * k) (by omega) (by omega) this
    have hT2 := G2.valid_double hT
    have hk2 : G2.toPoint T.double = (2 * k) • G2.toPoint Q1 := by
      rw [G2.toPoint_double hT, hk, two_mul, add_nsmul]
    have hz2 : T.double.z ≠ 0 := z_ne_zero_of_toPoint (hk2 ▸ hne (2 * k) (by omega) (by omega))
    have hD := finalExponentiation_millerDouble hT hz hy hz2 xp yp hf
    have hg2 : g2Hom (G2.toPoint T.double) = g2Hom (G2.toPoint T) + g2Hom (G2.toPoint T) := by
      rw [G2.toPoint_double hT, map_add]
    have hd1 : (millerDouble T xp yp f).1 = T.double := rfl
    rw [millerSteps_succ, Miller.steps_succ, hd1]
    by_cases hb : s.testBit n = true
    · have hb' := (bit_iff s n).mpr hb
      simp only [hb, hb', ite_true] at hsplit ⊢
      have hx := x_ne_of_nsmul hT2 hz2 hQ (j := 2 * k) (by omega) hk2
        (hne (2 * k - 1) (by omega) (by omega)) (hne (2 * k + 1) (by omega) (by omega))
      have hT3 := G2.valid_add hT2 hQ
      have hk3 : G2.toPoint (T.double.add Q1) = (2 * k + 1) • G2.toPoint Q1 := by
        rw [G2.toPoint_add hT2 hQ, hk2, add_nsmul, one_nsmul]
      have hz3 : (T.double.add Q1).z ≠ 0 :=
        z_ne_zero_of_toPoint (hk3 ▸ hne (2 * k + 1) (by omega) (by omega))
      have hA := finalExponentiation_millerAdd hT2 hz2 hQ hx hz3 xp yp hD
      have hg3 : g2Hom (G2.toPoint (T.double.add Q1)) =
          g2Hom (G2.toPoint T) + g2Hom (G2.toPoint T) + g2Hom (G2.toPoint Q1) := by
        rw [G2.toPoint_add hT2 hQ, map_add, hg2]
      have ha1 : (millerAdd T.double xq yq xp yp (millerDouble T xp yp f).2).1 =
          T.double.add Q1 := rfl
      rw [ha1, ← hg3, ← hg2]
      exact ih _ _ _ hT3 (by rw [hk3, hsplit]) (by omega) hA
    · have hb' : ¬(s >>> n) &&& 1 = 1 := fun h => hb ((bit_iff s n).mp h)
      simp only [hb, hb', ite_false, Bool.false_eq_true] at hsplit ⊢
      rw [← hg2]
      exact ih T.double _ _ hT2 (by rw [hk2, hsplit, add_zero]) (by omega) hD

private theorem finalExponentiation_conjugate_congr {a b : Fp12}
    (h : finalExponentiation a = finalExponentiation b) :
    finalExponentiation a.conjugate = finalExponentiation b.conjugate := by
  rw [Fp12.conjugate_eq_pow, Fp12.conjugate_eq_pow, finalExponentiation_eq_pow,
    finalExponentiation_eq_pow, pow_right_comm, pow_right_comm b, ← finalExponentiation_eq_pow,
    ← finalExponentiation_eq_pow, h]

/-- The pairing is the final exponentiation of Miller's algorithm, conjugated because `x < 0`.

The algorithm runs on `|x|`, on the untwist of `Q` in `E(Fp12)`, at the point `P` of `G1`.

`Q` is a valid point of the subgroup of order `r`, and `P` is not the point at infinity. -/
theorem pairing_eq_finalExponentiation_loop {P : G1} {Q : G2} (hQ : G2.Valid Q)
    (hQr : G2.inSubgroup Q = true) (hP : P.isInfinity = false) :
    pairing P Q = finalExponentiation (Miller.loop ambientCurve blsX (g2Hom (G2.toPoint Q))
      (fpToFp12 P.toAffine.1) (fpToFp12 P.toAffine.2)).conjugate := by
  by_cases hQi : Q.isInfinity = true
  · have h1 : (1 : Fp12).conjugate = 1 := by apply Fp12.ext <;> simp
    rw [(G2.isInfinity_eq_true_iff_toPoint_eq_zero hQ).mp hQi, map_zero, Miller.loop_zero,
      pairing, hQi, Bool.or_true, ite_eq_left rfl, h1,
      finalExponentiation_eq_pow, one_pow, Fp12.one_eq_one]
  rw [pairing, hP, Bool.false_or, ite_eq_right hQi]
  apply finalExponentiation_conjugate_congr
  have hz : Q.z ≠ 0 := fun h => hQi (Fp2.isZero_iff.mpr h)
  obtain ⟨h, e⟩ := toPoint_eq_some hQ hz
  set Q1 : G2 := ⟨Q.x / Q.z ^ 2, Q.y / Q.z ^ 3, Fp2.one⟩
  have hQ1 : G2.Valid Q1 := (WeierstrassCurve.Jacobian.nonsingular_some _ _).mpr h
  have he1 : G2.toPoint Q1 = G2.toPoint Q := by
    rw [e]
    exact WeierstrassCurve.Jacobian.Point.toAffine_some hQ1
  have hord : addOrderOf (G2.toPoint Q1) = Fr.modulus := by
    rw [he1]
    exact addOrderOf_eq_prime ((G2.inSubgroup_iff_modulus_smul_eq_zero hQ).mp hQr)
      (fun h0 => hQi ((G2.isInfinity_eq_true_iff_toPoint_eq_zero hQ).mpr h0))
  have hlog : blsX >>> blsX.log2 = 1 := Miller.shiftRight_log2 (by decide)
  have hmain := finalExponentiation_millerSteps (s := blsX) (by decide) hQ1 hord P.toAffine.1
    P.toAffine.2 blsX.log2 Q1 1 1 hQ1 (by rw [hlog, one_nsmul]) (by rw [hlog]; omega) rfl
  rw [← he1]
  rw [TwistFrobenius.toAffine_eq_div Q (Bool.eq_false_iff.mpr hQi)]
  exact hmain

end EthLib.Cryptography.Bls
