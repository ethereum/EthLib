module

public import EthLib.Cryptography.Proofs.Bls.AteFrobenius
public import EthLib.Cryptography.Proofs.Bls.PairingBilinear
public import EthLib.Cryptography.Proofs.Bls.G1SubgroupSpan

/-!
# Proofs: the pairing of BLS12-381 is bilinear

Let `N = (p^12 - 1) / r` be the exponent of the final exponentiation.

For points `P` and `Q` of `E : y^2 = x^3 + 4` over `Fp12`, take Miller's function of `|x|` and `Q`.

Its value at `P`, raised to `N`, is the ate value of `P` and `Q`.

- Let `pi` be the map `(x, y) -> (x^p, y^p)`, and let `G` be the untwist of `G2`.
- The ate value is linear in `P` among the points that `pi` fixes, for each `Q` in `G`.
- It is linear in `Q` in `G`, for each `P` that `pi` fixes.
- Both follow from the linearity of an ate-type pairing, whose hypotheses hold on `G`.
- The points of `G1` lie on `E` over `Fp12`.
- `pi` fixes them, because their coordinates lie in `Fp`.

Take a valid point `P` of `G1` other than `O`, and a valid point `Q` of the subgroup of `G2`.

Their pairing is the ate value of their points on `E`, raised to `p^6`.

The `p^6`-th power is the conjugation that the pairing applies because `x < 0`.

So `e(a g_1, b g_2) = e(g_1, g_2)^(a b)` for all `a` and `b` in `Fr`.

When `a` or `b` is zero, one of the points is `O`, and both sides are 1.

The pairing law of the check follows from this equation, so that law holds with no hypothesis.

See Miller, "The Weil Pairing, and Its Efficient Calculation", J. Cryptology 17 (2004).

See also [Vercauteren](https://eprint.iacr.org/2008/096), "Optimal pairings", Section 2.2.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

open TwistFrobenius WeierstrassCurve.Affine Miller

namespace Ate

/-- Miller's function of `|x|` and `Q`, at `P`, raised to the exponent `(p^12 - 1) / r`. -/
noncomputable def ateValue (P Q : ambientCurve.Point) : Fp12 :=
  ratioAt (lines ambientCurve blsX Q) P ^ finalExpExponent

/-- The ate value is linear in a point `P` that the Frobenius map fixes. -/
theorem ateValue_add_left {P₁ P₂ Q : ambientCurve.Point} (hP₁ : frobenius P₁ = P₁)
    (hP₂ : frobenius P₂ = P₂) (hQ : Q ∈ g2Subgroup) :
    ateValue (P₁ + P₂) Q = ateValue P₁ Q * ateValue P₂ Q :=
  pow_ratioAt_add_left primeFrobenius_apply (fun _ hR => eq_zero_of_frobenius_eq hR) hQ
    (LinesIn.lines hQ blsX) (ratioDivisor_lines hQ) hP₁ hP₂ even_finalExpExponent
    fun _ hz => pow_ateExponent hz

/-- The ate value is linear in a point `Q` of the untwist of `G2`. -/
theorem ateValue_add_right {P Q₁ Q₂ : ambientCurve.Point} (hP : frobenius P = P)
    (h₁ : Q₁ ∈ g2Subgroup) (h₂ : Q₂ ∈ g2Subgroup) :
    ateValue P (Q₁ + Q₂) = ateValue P Q₁ * ateValue P Q₂ :=
  pow_ratioAt_add_right primeFrobenius_apply (fun _ hR => frobenius_mem hR)
    (fun _ hR => eq_zero_of_frobenius_eq hR) h₁ h₂ (LinesIn.lines h₁ blsX)
    (LinesIn.lines h₂ blsX) (LinesIn.lines (g2Subgroup.add_mem h₁ h₂) blsX)
    (ratioDivisor_lines h₁) (ratioDivisor_lines h₂)
    (ratioDivisor_lines (g2Subgroup.add_mem h₁ h₂)) hP fun _ hz => pow_ateExponent hz

/-- The ate value of `n P` is the `n`-th power of that of `P`, when the Frobenius map fixes `P`. -/
theorem ateValue_nsmul_left {P Q : ambientCurve.Point} (hP : frobenius P = P)
    (hQ : Q ∈ g2Subgroup) (n : ℕ) : ateValue (n • P) Q = ateValue P Q ^ n := by
  induction n with
  | zero => simp [ateValue]
  | succ n ih =>
    rw [succ_nsmul, ateValue_add_left (by rw [map_nsmul, hP]) hP hQ, ih, pow_succ]

/-- The ate value at `Q = O` is 1, when the Frobenius map fixes `P`.

It is its own square.

It is not zero, since the only point of the untwist of `G2` that the Frobenius map fixes is `O`.
-/
theorem ateValue_zero_right {P : ambientCurve.Point} (hP : frobenius P = P) :
    ateValue P 0 = 1 := by
  have h := ateValue_add_right hP g2Subgroup.zero_mem g2Subgroup.zero_mem
  rw [add_zero] at h
  have hne : ateValue P 0 ≠ 0 := pow_ne_zero _
    ((LinesIn.lines g2Subgroup.zero_mem blsX).ratioAt_ne_zero fun hR =>
      eq_zero_of_frobenius_eq hR hP)
  exact (mul_eq_left₀ hne).mp h.symm

/-- The ate value of `n Q` is the `n`-th power of that of `Q`, when the Frobenius map fixes `P`. -/
theorem ateValue_nsmul_right {P Q : ambientCurve.Point} (hP : frobenius P = P)
    (hQ : Q ∈ g2Subgroup) (n : ℕ) : ateValue P (n • Q) = ateValue P Q ^ n := by
  induction n with
  | zero => rw [zero_nsmul, ateValue_zero_right hP, pow_zero]
  | succ n ih =>
    rw [succ_nsmul, ateValue_add_right hP (g2Subgroup.nsmul_mem hQ n) hQ, ih, pow_succ]

/-! ## `G1` on the curve over `Fp12` -/

/-- The inclusion of the points of `G1`, over `Fp`, into the points over `Fp12`. -/
noncomputable def g1Hom : G1.curve.toAffine.Point →+ ambientCurve.Point :=
  ShortWeierstrass.scaledHom fpToFp12 one_ne_zero (by rw [one_pow, mul_one, map_ofNat])

/-- The inclusion keeps the coordinates of a finite point. -/
theorem g1Hom_some {x y : ZMod Fp.modulus} (h : G1.curve.toAffine.Nonsingular x y) {X Y : Fp12}
    (hX : fpToFp12 x = X) (hY : fpToFp12 y = Y) : ∃ h', g1Hom (.some x y h) = .some X Y h' := by
  subst hX hY
  have e : g1Hom (.some x y h) = .some (fpToFp12 x * 1 ^ 2) (fpToFp12 y * 1 ^ 3)
      (ShortWeierstrass.scaled_nonsingular fpToFp12 1 one_ne_zero
        (by rw [one_pow, mul_one, map_ofNat]) h) := rfl
  simp only [one_pow, mul_one] at e
  exact ⟨_, e⟩

/-- The Frobenius map fixes the points of `G1`, because their coordinates lie in `Fp`. -/
theorem frobenius_g1Hom (P : G1.curve.toAffine.Point) : frobenius (g1Hom P) = g1Hom P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · have hf (a : ZMod Fp.modulus) : primeFrobenius (fpToFp12 a) = fpToFp12 a := by
      rw [primeFrobenius_apply, ← map_pow, ZMod.pow_card]
    obtain ⟨h', e⟩ := g1Hom_some h rfl rfl
    rw [e, mapPoint_some]
    simp only [hf]

/-- A valid point of `G1` other than `O` goes to the point of its affine coordinates. -/
theorem g1Hom_toPoint {P : G1} (hP : G1.Valid P) (hi : P.isInfinity = false) :
    ∃ h, g1Hom (G1.toPoint P) = .some (fpToFp12 (Fp.toZMod P.toAffine.1))
      (fpToFp12 (Fp.toZMod P.toAffine.2)) h := by
  have hz : ¬P.z.isZero = true := by simpa [G1.isInfinity] using hi
  have hzne : Fp.toZMod P.z ≠ 0 := fun hh => hz (G1.isZero_iff.mpr hh)
  have ex : Fp.toZMod P.toAffine.1 = Fp.toZMod P.x / Fp.toZMod P.z ^ 2 := by
    simp only [G1.toAffine, Fp.baseField_isZero, Fp.baseField_inverse, ite_eq_right hz]
    push_toZMod
    rw [Fp.toZMod_inverse]
    ring
  have ey : Fp.toZMod P.toAffine.2 = Fp.toZMod P.y / Fp.toZMod P.z ^ 3 := by
    simp only [G1.toAffine, Fp.baseField_isZero, Fp.baseField_inverse, ite_eq_right hz]
    push_toZMod
    rw [Fp.toZMod_inverse]
    ring
  rw [G1.toPoint, WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero (W := G1.curve) hP hzne]
  exact g1Hom_some _ (by rw [ex]; rfl) (by rw [ey]; rfl)

/-- Take a valid point `P` of `G1` other than `O`, and a valid point `Q` of the subgroup of `G2`.

Their pairing is the ate value of their points over `Fp12`, raised to `p^6`. -/
theorem pairing_eq_ateValue {P : G1} {Q : G2} (hP : G1.Valid P) (hi : P.isInfinity = false)
    (hQ : G2.Valid Q) (hQr : G2.inSubgroup Q = true) :
    pairing P Q = ateValue (g1Hom (G1.toPoint P)) (g2Hom (G2.toPoint Q)) ^ (Fp.modulus ^ 6) := by
  obtain ⟨h, e⟩ := g1Hom_toPoint hP hi
  rw [pairing_eq_finalExponentiation_loop hQ hQr hi, e, ateValue, finalExponentiation_eq_pow,
    Fp12.conjugate_eq_pow, ← pow_mul, ← pow_mul, mul_comm, loop_eq_linesAt _ _ h, ratioAt]

end Ate

open Ate

/-- The pairing is bilinear on the multiples of the generators.

For all `a` and `b` in `Fr`, `e(a g_1, b g_2) = e(g_1, g_2)^(a b)`. -/
theorem pairingBilinear : PairingBilinear := by
  intro a b
  have hP : frobenius (g1Hom (G1.toPoint (G1.generator : G1))) =
      g1Hom (G1.toPoint G1.generator) :=
    frobenius_g1Hom _
  have hQ : g2Hom (G2.toPoint G2.generator) ∈ g2Subgroup := AddSubgroup.mem_zmultiples _
  by_cases ha : a = 0
  · subst ha
    have hi : (G1.mul (G1.generator : G1) 0).isInfinity = true :=
      (G1.mul_generator_isInfinity_iff 0).mpr rfl
    simp only [pairing, hi, Bool.true_or, ↓reduceIte, Fr.val_zero, zero_mul, pow_zero,
      Fp12.one_eq_one]
  by_cases hb : b = 0
  · subst hb
    have hi : (G2.mul (G2.generator : G2) 0).isInfinity = true :=
      (G2.mul_generator_isInfinity_iff 0).mpr rfl
    simp only [pairing, hi, Bool.or_true, ↓reduceIte, Fr.val_zero, mul_zero, pow_zero,
      Fp12.one_eq_one]
  have hia : (G1.mul (G1.generator : G1) a).isInfinity = false :=
    Bool.eq_false_iff.mpr fun h => ha ((G1.mul_generator_isInfinity_iff a).mp h)
  rw [pairing_eq_ateValue (G1.valid_mul G1.valid_generator a) hia
      (G2.valid_mul G2.valid_generator b) (G2.inSubgroup_mul_generator b),
    pairing_eq_ateValue G1.valid_generator Fp.one_isZero G2.valid_generator
      G2.inSubgroup_generator,
    G1.toPoint_mul_generator, G2.toPoint_mul_generator, G1.ofFr, G2.ofFr, map_nsmul, map_nsmul,
    ateValue_nsmul_left hP (g2Subgroup.nsmul_mem hQ _), ateValue_nsmul_right hP hQ,
    ← pow_mul, ← pow_mul, ← pow_mul]
  congr 1
  ring

/-- The pairing law of the check holds with no hypothesis.

Let `P_i` represent `a_i g_1` and `Q_i` represent `b_i g_2`.

The check of the pairs `(P_i, Q_i)` passes exactly when `sum_i a_i b_i = 0`. -/
theorem pairingLaws : PairingLaws :=
  PairingLaws.of_bilinear pairingBilinear

end EthLib.Cryptography.Bls
