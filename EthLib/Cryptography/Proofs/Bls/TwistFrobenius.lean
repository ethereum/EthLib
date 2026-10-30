module

public import EthLib.Cryptography.Proofs.Bls.Fp12
public import EthLib.Cryptography.Proofs.Bls.G2Equiv
public import EthLib.Cryptography.Proofs.Bls.G2Order
public import EthLib.Cryptography.Proofs.Bls.HashToCurveValidity
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.FieldSimp

/-!
# Proofs: The concrete twist Frobenius endomorphism `psi`

Source: `RFC 9380 §8.8.2 and Appendix G.3`.

The extension tower:

- `Fp2 = Fp[i] / (i^2 + 1)`
- `Fp6 = Fp2[v] / (v^3 - (1 + i))`
- `Fp12 = Fp6[w] / (w^2 - v)`

The untwist sends `(x, y)` to `(x * w^(-2), y * w^(-3))`.

It embeds `E'(Fp2)` into `E : y^2 = x^3 + 4` over `Fp12`, and it is injective.

There, `psi` is the Frobenius map `(X, Y) -> (X^p, Y^p)`.

The Frobenius map is a group homomorphism, so `psi` is one too.

On the generator, `psi` acts as multiplication by the BLS parameter `x = -|x|`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

namespace TwistFrobenius

open WeierstrassCurve.Affine
open HashToCurve

/-! ## Finite-field cardinalities across the `Fp -> Fp2 -> Fp6 -> Fp12` tower -/

-- The exposed finite-type instances reduce through these coordinate equivalences.
def fp2Equiv : Fp2 ≃ Fp × Fp where
  toFun a := (a.c0, a.c1)
  invFun a := ⟨a.1, a.2⟩
  left_inv a := by cases a; rfl
  right_inv a := by cases a; rfl

def fp6Equiv : Fp6 ≃ Fp2 × Fp2 × Fp2 where
  toFun a := (a.c0, a.c1, a.c2)
  invFun a := ⟨a.1, a.2.1, a.2.2⟩
  left_inv a := by cases a; rfl
  right_inv a := by rcases a with ⟨a, b, c⟩; rfl

def fp12Equiv : Fp12 ≃ Fp6 × Fp6 where
  toFun a := (a.c0, a.c1)
  invFun a := ⟨a.1, a.2⟩
  left_inv a := by cases a; rfl
  right_inv a := by cases a; rfl

noncomputable instance instFintypeFp2 : Fintype Fp2 :=
  Fintype.ofEquiv (Fp × Fp) fp2Equiv.symm

noncomputable instance instFintypeFp6 : Fintype Fp6 :=
  Fintype.ofEquiv (Fp2 × Fp2 × Fp2) fp6Equiv.symm

noncomputable instance instFintypeFp12 : Fintype Fp12 :=
  Fintype.ofEquiv (Fp6 × Fp6) fp12Equiv.symm

/-- `Fp2` has `p^2` elements because it is a pair of `Fp` coordinates. -/
theorem card_fp2 : Fintype.card Fp2 = Fp.modulus ^ 2 := by
  rw [Fintype.card_congr fp2Equiv, Fintype.card_prod]
  rw [show Fintype.card Fp = Fp.modulus from Fintype.card_fin _]
  exact (pow_two _).symm

/-- `Fp6` has `p^6` elements because it is a triple of `Fp2` coordinates. -/
theorem card_fp6 : Fintype.card Fp6 = Fp.modulus ^ 6 := by
  rw [Fintype.card_congr fp6Equiv, Fintype.card_prod, Fintype.card_prod, card_fp2]
  ring

/-- `Fp12` has `p^12` elements because it is a pair of `Fp6` coordinates. -/
theorem card_fp12 : Fintype.card Fp12 = Fp.modulus ^ 12 := by
  rw [Fintype.card_congr fp12Equiv, Fintype.card_prod, card_fp6]
  ring

/-! ## Tower field inclusions and untwist constants -/

/-- Constant inclusion from `ZMod Fp.modulus` into `Fp2`. -/
def fpToFp2 : ZMod Fp.modulus →+* Fp2 where
  toFun := Fp2.ofFp
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := by
    let aa : Fp := a
    let bb : Fp := b
    open scoped Fin.CommRing in
    apply Fp2.ext
    · exact rfl
    · show (0 : Fp) = 0 + 0; ring
  map_mul' a b := by
    let aa : Fp := a
    let bb : Fp := b
    open scoped Fin.CommRing in
    apply Fp2.ext
    · show aa * bb = aa * bb - 0 * 0; ring
    · show (0 : Fp) = aa * 0 + 0 * bb; ring

@[simp] theorem fpToFp2_apply (a : Fp) : fpToFp2 a = Fp2.ofFp a := rfl

/-- Constant inclusion from `Fp2` into `Fp6`. -/
def fp2ToFp6 : Fp2 →+* Fp6 where
  toFun := Fp6.ofFp2
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := by apply Fp6.ext <;> simp
  map_mul' a b := by apply Fp6.ext <;> simp [Fp2.mulByOnePlusI_eq]

@[simp] theorem fp2ToFp6_apply (a : Fp2) : fp2ToFp6 a = Fp6.ofFp2 a := rfl

/-- Constant inclusion from `Fp6` into `Fp12`. -/
def fp6ToFp12 : Fp6 →+* Fp12 where
  toFun a := ⟨a, 0⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := by apply Fp12.ext <;> simp
  map_mul' a b := by apply Fp12.ext <;> simp [Fp6.mulByV_eq]

@[simp] theorem fp6ToFp12_apply (a : Fp6) : fp6ToFp12 a = ⟨a, 0⟩ := rfl

/-- Composite ring homomorphism from `Fp2` into `Fp12`. -/
def fp2ToFp12 : Fp2 →+* Fp12 := fp6ToFp12.comp fp2ToFp6

/-- Composite ring homomorphism from `ZMod Fp.modulus` into `Fp12`. -/
def fpToFp12 : ZMod Fp.modulus →+* Fp12 := fp2ToFp12.comp fpToFp2

@[simp] theorem fpToFp12_apply (a : Fp) :
    fpToFp12 a = ⟨Fp6.ofFp2 (Fp2.ofFp a), Fp6.zero⟩ := rfl

@[simp] theorem fp2ToFp12_apply (a : Fp2) :
    fp2ToFp12 a = ⟨Fp6.ofFp2 a, Fp6.zero⟩ := rfl

/-- Generator `w` of `Fp12 = Fp6[w] / (w^2 - v)`. -/
def w : Fp12 := ⟨0, 1⟩

theorem w_ne_zero : w ≠ 0 := by
  intro h
  exact one_ne_zero (congrArg Fp12.c1 h)

theorem v_cubed : Fp6.v ^ 3 = fp2ToFp6 Fp2.xi := by
  apply Fp6.ext <;> simp [pow_succ, Fp2.mulByOnePlusI_eq]

theorem w_squared : w ^ 2 = fp6ToFp12 Fp6.v := by
  apply Fp12.ext <;> simp [pow_two, w, Fp6.mulByV_eq]

theorem w_sixth : w ^ 6 = fp2ToFp12 Fp2.xi := by
  rw [show 6 = 2 * 3 by decide, pow_mul, w_squared, ← map_pow, v_cubed]
  rfl

/-- Cancels `xi = 1 + i` in `bTwist = 4 * xi` when scaling `(x, y)` by `(w^(-2), w^(-3))`. -/
theorem twist_coefficient : fp2ToFp12 G2.bTwist * (w⁻¹) ^ 6 = 4 := by
  have hb : G2.bTwist = (4 : Fp2) * Fp2.xi := by decide
  rw [hb, map_mul, map_ofNat, inv_pow, ← w_sixth]
  field_simp [w_ne_zero]

/-! ## Ambient curve `y^2 = x^3 + 4` over `Fp12` and short-curve scaling homomorphisms -/

/-- The ambient short Weierstrass curve `y^2 = x^3 + 4` over `Fp12`. -/
def ambientCurve : WeierstrassCurve.Affine Fp12 :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 4 }

@[simp] theorem ambient_equation (x y : Fp12) :
    ambientCurve.Equation x y ↔ y ^ 2 = x ^ 3 + 4 := by
  simp [equation_iff, ambientCurve]

/-- Every point of `y^2 = x^3 + 4` over `Fp12` is nonsingular, since `2` and `3` are nonzero mod `p`. -/
theorem ambient_nonsingular {x y : Fp12} (h : y ^ 2 = x ^ 3 + 4) :
    ambientCurve.Nonsingular x y := by
  rw [nonsingular_iff', ambient_equation]
  refine ⟨h, ?_⟩
  simp only [ambientCurve, zero_mul, mul_zero, add_zero, zero_sub, neg_ne_zero]
  have h2 : (2 : Fp12) ≠ 0 := by decide
  have h3 : (3 : Fp12) ≠ 0 := by decide
  by_cases hy : y = 0
  · left
    apply mul_ne_zero h3
    apply pow_ne_zero
    intro hx
    have hf : (0 : Fp12) = 4 := by simpa [hx, hy] using h
    exact (by decide : (0 : Fp12) ≠ 4) hf
  · exact Or.inr (mul_ne_zero h2 hy)

/-- Short Weierstrass curve `y^2 = x^3 + c` over an arbitrary field `F`. -/
def shortCurve {F : Type*} [Field F] (c : F) : WeierstrassCurve.Affine F :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := c }

@[simp] theorem short_equation {F : Type*} [Field F] (c x y : F) :
    (shortCurve c).Equation x y ↔ y ^ 2 = x ^ 3 + c := by
  simp [equation_iff, shortCurve]

@[simp] theorem short_negY {F : Type*} [Field F] (c x y : F) :
    (shortCurve c).negY x y = -y := by
  simp [negY, shortCurve]

section ScaledHom

variable {F : Type*} [Field F] (f : F →+* Fp12) (u : Fp12) (hu : u ≠ 0)

theorem scaled_equation {c x y : F} (hc : f c * u ^ 6 = 4)
    (h : (shortCurve c).Equation x y) :
    (f y * u ^ 3) ^ 2 = (f x * u ^ 2) ^ 3 + 4 := by
  have he := congrArg f ((short_equation c x y).mp h)
  simp only [map_pow, map_add] at he
  linear_combination u ^ 6 * he + hc

include hu in
theorem scaled_x_eq_iff (x t : F) : f x * u ^ 2 = f t * u ^ 2 ↔ x = t := by
  rw [mul_left_inj' (pow_ne_zero 2 hu), f.injective.eq_iff]

include hu in
theorem scaled_y_neg_eq_iff (y z : F) : f y * u ^ 3 = -(f z * u ^ 3) ↔ y = -z := by
  rw [← neg_mul, ← map_neg, mul_left_inj' (pow_ne_zero 3 hu), f.injective.eq_iff]

variable [DecidableEq F]

include hu in
/-- Chord and tangent slopes both scale by `u` across every branch. -/
theorem scaled_slope (c x t y z : F) :
    ambientCurve.slope (f x * u ^ 2) (f t * u ^ 2) (f y * u ^ 3) (f z * u ^ 3) =
      f ((shortCurve c).slope x t y z) * u := by
  simp only [slope, negY, ambientCurve, shortCurve, zero_mul, mul_zero, add_zero, sub_zero,
    scaled_x_eq_iff f u hu, scaled_y_neg_eq_iff f u hu]
  by_cases hx : x = t
  · subst t
    rw [ite_eq_left rfl, ite_eq_left rfl]
    by_cases hy : y = -z
    · rw [ite_eq_left hy, ite_eq_left hy, map_zero, zero_mul]
    · rw [ite_eq_right hy, ite_eq_right hy]
      simp only [map_div₀, map_mul, map_pow, map_ofNat, map_sub, map_neg]
      rw [show 3 * (f x * u ^ 2) ^ 2 = (3 * f x ^ 2) * u ^ 4 by ring,
        show f y * u ^ 3 - -(f y * u ^ 3) = (f y - -f y) * u ^ 3 by ring,
        mul_div_mul_comm]
      have hs : u ^ 4 / u ^ 3 = u := by field_simp [hu]
      rw [hs]
  · rw [ite_eq_right hx, ite_eq_right hx]
    simp only [map_div₀, map_sub]
    rw [← sub_mul, ← sub_mul, mul_div_mul_comm]
    have hs : u ^ 3 / u ^ 2 = u := by field_simp [hu]
    rw [hs]

omit [DecidableEq F] in
theorem scaled_addX (c x t m : F) :
    ambientCurve.addX (f x * u ^ 2) (f t * u ^ 2) (f m * u) =
      f ((shortCurve c).addX x t m) * u ^ 2 := by
  simp only [addX, ambientCurve, shortCurve, zero_mul, add_zero, sub_zero,
    map_sub, map_pow]
  ring

omit [DecidableEq F] in
theorem scaled_addY (c x t y m : F) :
    ambientCurve.addY (f x * u ^ 2) (f t * u ^ 2) (f y * u ^ 3) (f m * u) =
      f ((shortCurve c).addY x t y m) * u ^ 3 := by
  simp only [addY, negY, negAddY, addX, ambientCurve, shortCurve, zero_mul, add_zero,
    sub_zero, map_neg, map_add, map_mul, map_sub, map_pow]
  ring

variable {c : F} (hc : f c * u ^ 6 = 4)

noncomputable def scaledPoint : (shortCurve c).Point → ambientCurve.Point
  | .zero => 0
  | .some x y h => .some (f x * u ^ 2) (f y * u ^ 3)
      (ambient_nonsingular (scaled_equation f u hc h.1))

include hu in
theorem scaledPoint_add (P Q : (shortCurve c).Point) :
    scaledPoint f u hc (P + Q) = scaledPoint f u hc P + scaledPoint f u hc Q := by
  cases P with
  | zero => rfl
  | some x y hp =>
    cases Q with
    | zero => rfl
    | some t z hq =>
      by_cases hxy : x = t ∧ y = (shortCurve c).negY t z
      · rw [Point.add_of_Y_eq hxy.1 hxy.2]
        simp only [scaledPoint]
        have hsy : f y * u ^ 3 = ambientCurve.negY (f t * u ^ 2) (f z * u ^ 3) := by
          simp only [negY, ambientCurve, zero_mul, sub_zero]
          exact (scaled_y_neg_eq_iff f u hu y z).mpr (by simpa only [short_negY] using hxy.2)
        rw [Point.add_of_Y_eq (congrArg (fun x => f x * u ^ 2) hxy.1) hsy]
      · have hscaled : ¬(f x * u ^ 2 = f t * u ^ 2 ∧
            f y * u ^ 3 = ambientCurve.negY (f t * u ^ 2) (f z * u ^ 3)) := by
          simp only [negY, ambientCurve, zero_mul, sub_zero,
            scaled_x_eq_iff f u hu, scaled_y_neg_eq_iff f u hu]
          simpa only [short_negY] using hxy
        rw [Point.add_some hxy]
        simp only [scaledPoint]
        rw [Point.add_some hscaled, Point.some.injEq]
        simp only [scaled_slope f u hu c, scaled_addX f u c, scaled_addY f u c, and_self]

/-- Short-Weierstrass coordinate scaling `(x, y) -> (f x * u^2, f y * u^3)` as a group homomorphism. -/
noncomputable def scaledHom : (shortCurve c).Point →+ ambientCurve.Point where
  toFun := scaledPoint f u hc
  map_zero' := rfl
  map_add' := scaledPoint_add f u hu hc

@[simp] theorem scaledHom_apply (P : (shortCurve c).Point) :
    scaledHom f u hu hc P = scaledPoint f u hc P := rfl

include hu in
theorem scaledHom_injective : Function.Injective (scaledHom f u hu hc) := by
  intro P Q h
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some _ _ _ => cases h
  | some x y hp =>
    cases Q with
    | zero => cases h
    | some t z hq =>
      have hs : f x * u ^ 2 = f t * u ^ 2 ∧ f y * u ^ 3 = f z * u ^ 3 := Point.some.inj h
      have hx := (scaled_x_eq_iff f u hu x t).mp hs.1
      have hy : y = z := f.injective ((mul_left_inj' (pow_ne_zero 3 hu)).mp hs.2)
      subst t; subst z
      rfl

end ScaledHom

/-- Injective sextic untwist homomorphism from `G2.curve.toAffine.Point` into `E(Fp12)`. -/
noncomputable def g2Hom : G2.curve.toAffine.Point →+ ambientCurve.Point :=
  scaledHom fp2ToFp12 w⁻¹ (inv_ne_zero w_ne_zero) twist_coefficient

@[simp] theorem g2Hom_apply (P : G2.curve.toAffine.Point) :
    g2Hom P = scaledPoint fp2ToFp12 w⁻¹ twist_coefficient P := rfl

theorem g2Hom_injective : Function.Injective g2Hom :=
  scaledHom_injective _ _ _ _

/-! ## The `p`-Frobenius on `Fp12` and its commutation with the sextic untwist -/

/-- `p`-power Frobenius ring endomorphism on `Fp12`. -/
noncomputable def primeFrobenius : Fp12 →+* Fp12 := by
  let _ : Algebra (ZMod Fp.modulus) Fp12 := fpToFp12.toAlgebra
  exact (FiniteField.frobeniusAlgHom (ZMod Fp.modulus) Fp12).toRingHom

theorem primeFrobenius_apply (a : Fp12) : primeFrobenius a = a ^ Fp.modulus := by
  change a ^ Fintype.card (ZMod Fp.modulus) = _
  rw [ZMod.card]

/-- `p`-power Frobenius ring endomorphism on `Fp2`. -/
noncomputable def primeFrobenius2 : Fp2 →+* Fp2 := by
  let _ : Algebra (ZMod Fp.modulus) Fp2 := fpToFp2.toAlgebra
  exact (FiniteField.frobeniusAlgHom (ZMod Fp.modulus) Fp2).toRingHom

theorem primeFrobenius2_apply (a : Fp2) : primeFrobenius2 a = a ^ Fp.modulus := by
  change a ^ Fintype.card (ZMod Fp.modulus) = _
  rw [ZMod.card]

/-- Because `p = 3 mod 4`, `i^p = -i` and the `p`-power map on `Fp2` is conjugation. -/
theorem fp2_pow_p_eq_conjugate (a : Fp2) : a ^ Fp.modulus = a.conjugate := by
  have hi4 : Fp2.i ^ 4 = 1 := by
    rw [show 4 = 2 * 2 by decide, pow_mul, pow_two Fp2.i, Fp2.i_sq, neg_one_sq]
  have hi3 : Fp2.i ^ 3 = -Fp2.i := by
    rw [pow_succ, pow_two, Fp2.i_sq, neg_one_mul]
  have hip : primeFrobenius2 Fp2.i = -Fp2.i := by
    rw [primeFrobenius2_apply,
      show Fp.modulus = 4 * ((Fp.modulus - 3) / 4) + 3 by decide,
      pow_add, pow_mul, hi4, one_pow, one_mul, hi3]
  have hf (b : ZMod Fp.modulus) : primeFrobenius2 (fpToFp2 b) = fpToFp2 b := by
    rw [primeFrobenius2_apply, ← map_pow, ZMod.pow_card]
  have hd : a = fpToFp2 a.c0 + fpToFp2 a.c1 * Fp2.i := by
    open scoped Fin.CommRing in
    apply Fp2.ext
    · show a.c0 = a.c0 + (a.c1 * 0 - 0 * 1); ring
    · show a.c1 = 0 + (a.c1 * 1 + 0 * 0); ring
  rw [← primeFrobenius2_apply]
  conv_lhs => rw [hd, map_add, map_mul, hf a.c0, hf a.c1, hip]
  open scoped Fin.CommRing in
  apply Fp2.ext
  · show a.c0 + (a.c1 * -0 - 0 * -1) = a.c0; ring
  · show 0 + (a.c1 * -1 + 0 * -0) = -a.c1; ring

theorem primeFrobenius_fp2 (a : Fp2) :
    primeFrobenius (fp2ToFp12 a) = fp2ToFp12 a.conjugate := by
  rw [primeFrobenius_apply, ← map_pow, fp2_pow_p_eq_conjugate]

/-- Definitionally identical to `c1Psi` in `HashToCurve.psi`. -/
def psiAlpha : Fp2 := (Fp2.powNat ⟨Fp.one, Fp.one⟩ ((Fp.modulus - 1) / 3)).inverse

/-- Definitionally identical to `c2Psi` in `HashToCurve.psi`. -/
def psiBeta : Fp2 := (Fp2.powNat ⟨Fp.one, Fp.one⟩ ((Fp.modulus - 1) / 2)).inverse

theorem psiAlpha_eq : psiAlpha = (Fp2.xi ^ ((Fp.modulus - 1) / 3))⁻¹ := by
  unfold psiAlpha
  rw [Fp2.powNat_eq_pow]
  rfl

theorem psiBeta_eq : psiBeta = (Fp2.xi ^ ((Fp.modulus - 1) / 2))⁻¹ := by
  unfold psiBeta
  rw [Fp2.powNat_eq_pow]
  rfl

theorem primeFrobenius_wInv2 :
    primeFrobenius ((w⁻¹) ^ 2) = fp2ToFp12 psiAlpha * (w⁻¹) ^ 2 := by
  rw [primeFrobenius_apply, inv_pow, ← inv_pow, ← pow_mul,
    show 2 * Fp.modulus = 6 * ((Fp.modulus - 1) / 3) + 2 by decide,
    pow_add, pow_mul, inv_pow, w_sixth, inv_pow, ← map_pow, psiAlpha_eq, map_inv₀]

theorem primeFrobenius_wInv3 :
    primeFrobenius ((w⁻¹) ^ 3) = fp2ToFp12 psiBeta * (w⁻¹) ^ 3 := by
  rw [primeFrobenius_apply, inv_pow, ← inv_pow, ← pow_mul,
    show 3 * Fp.modulus = 6 * ((Fp.modulus - 1) / 2) + 3 by decide,
    pow_add, pow_mul, inv_pow, w_sixth, inv_pow, ← map_pow, psiBeta_eq, map_inv₀]

/-- `p`-power Frobenius group endomorphism `(X, Y) -> (X^p, Y^p)` on `E(Fp12)`. -/
noncomputable def primeFrobeniusHom : ambientCurve.Point →+ ambientCurve.Point :=
  scaledHom primeFrobenius 1 one_ne_zero (by rw [one_pow, mul_one, map_ofNat])

theorem primeFrobeniusHom_apply (P : ambientCurve.Point) :
    primeFrobeniusHom P = scaledPoint primeFrobenius 1
      (by rw [one_pow, mul_one, map_ofNat]) P := rfl

/-! ## Additivity of `psi` and its eigenvalue on `G2.generator` -/

private theorem alpha_cube : psiAlpha ^ 3 = psiBeta ^ 2 := by decide +kernel
private theorem beta_twist : psiBeta ^ 2 * G2.bTwist.conjugate = G2.bTwist := by decide +kernel

private theorem twist_frob_equation {x y : Fp2}
    (h : y ^ 2 = x ^ 3 + G2.bTwist) :
    (psiBeta * y.conjugate) ^ 2 = (psiAlpha * x.conjugate) ^ 3 + G2.bTwist := by
  have he := congrArg primeFrobenius2 h
  simp only [map_pow, map_add, primeFrobenius2_apply, fp2_pow_p_eq_conjugate] at he
  linear_combination psiBeta ^ 2 * he - x.conjugate ^ 3 * alpha_cube + beta_twist

private theorem twist_nonsingular {x y : Fp2}
    (h : y ^ 2 = x ^ 3 + G2.bTwist) : G2.curve.toAffine.Nonsingular x y := by
  apply (WeierstrassCurve.Jacobian.nonsingular_some (W' := G2.curve) x y).mp
  exact G2.valid_of_affine_equation (by simpa only [pow_succ, pow_zero, one_mul] using h)

/-- Action of the `RFC 9380 Appendix G.3` twist endomorphism on `G2.curve.toAffine.Point`. -/
noncomputable def mapPoint : G2.curve.toAffine.Point → G2.curve.toAffine.Point
  | .zero => 0
  | .some x y h => .some (psiAlpha * x.conjugate) (psiBeta * y.conjugate)
      -- The curve-membership proof can depend on private lemmas.
      (by exact twist_nonsingular (twist_frob_equation
        ((short_equation G2.bTwist x y).mp h.1)))

/-- Untwisting `mapPoint` yields the `p`-power Frobenius on `E(Fp12)`. -/
theorem untwist_mapPoint (P : G2.curve.toAffine.Point) :
    g2Hom (mapPoint P) = primeFrobeniusHom (g2Hom P) := by
  cases P with
  | zero => rfl
  | some x y h =>
    simp only [mapPoint, g2Hom_apply, scaledPoint, primeFrobeniusHom_apply,
      one_pow, mul_one, Point.some.injEq, map_mul, primeFrobenius_fp2]
    rw [primeFrobenius_wInv2, primeFrobenius_wInv3]
    constructor <;> ring

theorem mapPoint_add (P Q : G2.curve.toAffine.Point) :
    mapPoint (P + Q) = mapPoint P + mapPoint Q := by
  apply g2Hom_injective
  rw [untwist_mapPoint, map_add, map_add, map_add, untwist_mapPoint, untwist_mapPoint]

/-- The twist Frobenius endomorphism `psi` as an additive group endomorphism. -/
noncomputable def hom : G2.curve.toAffine.Point →+ G2.curve.toAffine.Point where
  toFun := mapPoint
  map_zero' := rfl
  map_add' := mapPoint_add

@[simp] theorem hom_apply (P : G2.curve.toAffine.Point) : hom P = mapPoint P := rfl

private theorem toAffine_eq_div (p : G2) (hi : p.z.isZero = false) :
    p.toAffine = (p.x / p.z ^ 2, p.y / p.z ^ 3) := by
  have hz : ¬p.z.isZero = true := by simp [hi]
  simp only [G2.toAffine, ite_eq_right hz]
  change (p.x * (p.z⁻¹ * p.z⁻¹), p.y * (p.z⁻¹ * p.z⁻¹ * p.z⁻¹)) = _
  apply Prod.ext <;> dsimp <;> simp only [div_eq_mul_inv] <;> ring

/-- Normalization connects `HashToCurve.psi` on valid representatives to `TwistFrobenius.hom`. -/
theorem toPoint_psi {P : G2} (hP : G2.Valid P) :
    G2.toPoint (psi P) = hom (G2.toPoint P) := by
  by_cases hi : P.z.isZero = true
  · have hp0 : G2.toPoint P = 0 :=
      WeierstrassCurve.Jacobian.Point.toAffine_of_Z_eq_zero (Fp2.isZero_iff.mp hi)
    rw [psi, ite_eq_left hi, hp0, map_zero]
  · have hf := Bool.eq_false_iff.mpr hi
    have hz : G2.rep P 2 ≠ 0 := fun hz => hi (Fp2.isZero_iff.mpr hz)
    have hnorm := WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero hP hz
    change G2.toPoint P = _ at hnorm
    rw [hnorm, hom_apply]
    have hv := psi_valid hP
    have he : psi P = ⟨psiAlpha * P.toAffine.1.conjugate,
        psiBeta * P.toAffine.2.conjugate, Fp2.one⟩ := by
      unfold psi
      rw [hf]
      rfl
    rw [he] at hv ⊢
    change WeierstrassCurve.Jacobian.Point.toAffine G2.curve _ = _
    rw [WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero hv one_ne_zero]
    simp only [mapPoint, toAffine_eq_div P hf,
      G2.rep_x, G2.rep_y, G2.rep_z, show Fp2.one = (1 : Fp2) from rfl,
      one_pow, div_one]

/-- `psi` respects `G2.add` on valid Jacobian representatives. -/
theorem toPoint_psi_add {P Q : G2} (hP : G2.Valid P) (hQ : G2.Valid Q) :
    G2.toPoint (psi (G2.add P Q)) = G2.toPoint (psi P) + G2.toPoint (psi Q) := by
  rw [toPoint_psi (G2.valid_add hP hQ), G2.toPoint_add hP hQ, map_add,
    toPoint_psi hP, toPoint_psi hQ]

/-- `psi` commutes with `G2.mulNat` on valid Jacobian representatives. -/
theorem toPoint_psi_mulNat {P : G2} (hP : G2.Valid P) (n : Nat) :
    G2.toPoint (psi (G2.mulNat P n)) = n • G2.toPoint (psi P) := by
  rw [toPoint_psi (G2.valid_mulNat hP n), G2.toPoint_mulNat hP, map_nsmul, toPoint_psi hP]

/-- Structural double-and-add ladder so the kernel evaluates `[blsAbsX] * g_2` directly. -/
private def mulNatAux : Nat → G2 → Nat → G2
  | 0, _, _ => G2.zero
  | fuel + 1, p, k =>
    if k = 0 then G2.zero
    else
      let half := mulNatAux fuel (G2.double p) (k / 2)
      if k % 2 = 1 then G2.add p half else half

private theorem mulNatAux_eq (fuel : Nat) (p : G2) (k : Nat)
    (hk : k < 2 ^ fuel) : mulNatAux fuel p k = G2.mulNat p k := by
  induction fuel generalizing p k with
  | zero =>
    have : k = 0 := by simpa using hk
    subst this
    rw [mulNatAux, G2.mulNat_def]
    simp
  | succ fuel ih =>
    rw [mulNatAux, G2.mulNat_def]
    by_cases h0 : k = 0
    · simp [h0]
    · have h2 : k / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at hk
        omega
      rw [ite_eq_right h0, ite_eq_right h0, ih (G2.double p) (k / 2) h2]

/-- `psi(g_2) = [x] * g_2` for the BLS parameter `x`, checked in the kernel. -/
theorem psi_generator_projectiveEq :
    G2.projectiveEq (psi G2.generator) (mulNegX G2.generator) = true := by
  unfold mulNegX
  rw [← mulNatAux_eq 65 G2.generator blsAbsX (by decide)]
  decide +kernel

/-- The `psi` eigenvalue on `G2.generator` equals the signed BLS parameter `x = -blsAbsX`. -/
theorem hom_generator :
    hom (G2.toPoint G2.generator) = -(blsAbsX • G2.toPoint G2.generator) := by
  rw [← toPoint_psi G2.valid_generator]
  have he := (G2.projectiveEq_eq_true_iff_toPoint_eq
    (psi_valid G2.valid_generator) (mulNegX_valid G2.valid_generator)).mp psi_generator_projectiveEq
  rw [he, mulNegX, G2.toPoint_neg (G2.valid_mulNat G2.valid_generator _),
    G2.toPoint_mulNat G2.valid_generator]

/-- Every multiple `[n] * g_2` satisfies `hom ([n] * g_2) = -[blsAbsX] * ([n] * g_2)`. -/
theorem hom_generator_nsmul (n : Nat) :
    hom (n • G2.toPoint G2.generator) = -(blsAbsX • (n • G2.toPoint G2.generator)) := by
  rw [map_nsmul, hom_generator, neg_nsmul, ← mul_nsmul, ← mul_nsmul, Nat.mul_comm]

end TwistFrobenius

end EthLib.Cryptography.Bls
