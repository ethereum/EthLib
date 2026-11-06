module

public import EthLib.Cryptography.Proofs.Bls.HashToCurve
public import EthLib.Cryptography.Proofs.Bls.G2Validity
public import EthLib.Cryptography.Proofs.Bls.HashToCurveMap

/-!
# Proofs: the 3-isogeny sends `E'` onto the twist

Source: RFC 9380 §8.8.2 and Appendix E.3.

The kernel checks the 13 coefficients of Appendix E.3 against closed rational forms.

Both denominators vanish only at `x = -6 + 6 * i`, and no point of `E'` has that abscissa.

So the isogeny sends every point of `E'` to a valid affine point of the twist.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.HashToCurve

open EthLib.Cryptography.Bls

set_option maxRecDepth 8000

local notation "I" => (Fp2.i : Fp2)

private def xn (x : Fp2) := x ^ 3 + (12 - 12 * I) * x ^ 2 - 24 * I * x + 304 + 304 * I
private def yn (x : Fp2) := -x ^ 3 + (-18 + 18 * I) * x ^ 2 + 264 * I * x + 752 + 752 * I
private def d (x : Fp2) := x + 6 - 6 * I

private theorem iso_poly (x : Fp2) :
    (x ^ 3 + (240 * I) * x + 1012 + 1012 * I) * (yn x) ^ 2 =
      (xn x) ^ 3 + (4 + 4 * I) * 729 * (d x) ^ 6 := by
  unfold xn yn d
  ring_nf
  have h2 : I ^ 2 = -1 := by simpa [pow_two] using Fp2.i_sq
  have h3 : I ^ 3 = -I := by rw [pow_succ, h2]; ring
  have h4 : I ^ 4 = 1 := by rw [show (4 : Nat) = 2 * 2 by decide, pow_mul, h2]; ring
  have h5 : I ^ 5 = I := by rw [pow_succ, h4]; ring
  have h6 : I ^ 6 = -1 := by rw [show (6 : Nat) = 2 * 3 by decide, pow_mul, h2]; ring
  have h7 : I ^ 7 = -I := by rw [pow_succ, h6]; ring
  rw [h2, h3, h4, h5, h6, h7]
  ring

private theorem k10_eq : (k10 : Fp2) = (304 + 304 * I) / 9 := by decide_eq_at_model [map_k10]
private theorem k11_eq : (k11 : Fp2) = (-24 * I) / 9 := by decide_eq_at_model [map_k11]
private theorem k12_eq : (k12 : Fp2) = (12 - 12 * I) / 9 := by decide_eq_at_model [map_k12]
private theorem k13_eq : (k13 : Fp2) = 1 / 9 := by decide_eq_at_model [map_k13]
private theorem k20_eq : (k20 : Fp2) = -72 * I := by decide_eq_at_model [map_k20]
private theorem k21_eq : (k21 : Fp2) = 12 - 12 * I := by decide_eq_at_model [map_k21]
private theorem k30_eq : (k30 : Fp2) = (752 + 752 * I) / 27 := by decide_eq_at_model [map_k30]
private theorem k31_eq : (k31 : Fp2) = (264 * I) / 27 := by decide_eq_at_model [map_k31]
private theorem k32_eq : (k32 : Fp2) = (-18 + 18 * I) / 27 := by decide_eq_at_model [map_k32]
private theorem k33_eq : (k33 : Fp2) = -1 / 27 := by decide_eq_at_model [map_k33]
private theorem k40_eq : (k40 : Fp2) = -432 - 432 * I := by decide_eq_at_model [map_k40]
private theorem k41_eq : (k41 : Fp2) = -216 * I := by decide_eq_at_model [map_k41]
private theorem k42_eq : (k42 : Fp2) = 18 - 18 * I := by decide_eq_at_model [map_k42]

-- The denominator `x_den` is `d(x)^2`.
private theorem xDen_eq (x : Fp2) : x * x + k21 * x + k20 = (d x) ^ 2 := by
  rw [k21_eq, k20_eq]
  unfold d
  linear_combination -36 * Fp2.i_sq

-- The denominator `y_den` is `d(x)^3`.
private theorem yDen_eq (x : Fp2) :
    x * x * x + k42 * (x * x) + k41 * x + k40 = (d x) ^ 3 := by
  rw [k42_eq, k41_eq, k40_eq]
  unfold d
  have hi3 : I ^ 3 = -I := by rw [pow_succ, pow_two, Fp2.i_sq]; ring
  ring_nf
  rw [show I ^ 2 = -1 by simpa [pow_two] using Fp2.i_sq, hi3]
  ring

private theorem xNum_eq (x : Fp2) :
    k13 * (x * x * x) + k12 * (x * x) + k11 * x + k10 = xn x / 9 := by
  rw [k13_eq, k12_eq, k11_eq, k10_eq]
  unfold xn
  ring

private theorem yNum_eq (x : Fp2) :
    k33 * (x * x * x) + k32 * (x * x) + k31 * x + k30 = yn x / 27 := by
  rw [k33_eq, k32_eq, k31_eq, k30_eq]
  unfold yn
  ring

open scoped EthLib.Cryptography.Bls.Fp

set_option exponentiation.threshold 512 in
/-- `2` is not a square modulo `Fp.modulus`, checked via Euler's criterion. -/
private theorem sq_ne_two (z : ZMod Fp.modulus) : z * z ≠ 2 := by
  intro h
  have h2 : z ^ 2 = ((2 : Nat) : ZMod Fp.modulus) := by
    linear_combination h
  have hz : z ≠ 0 := by
    intro hz0
    rw [hz0] at h
    revert h; decide
  have hfermat : z ^ (Fp.modulus - 1) = 1 := ZMod.pow_card_sub_one_eq_one hz
  rw [show Fp.modulus - 1 = 2 * ((Fp.modulus - 1) / 2) by decide,
    pow_mul, h2] at hfermat
  exact PowMod.natCast_pow_div_ne_one Fp.modulus 384 2 2
    (by decide) (by decide) hfermat

/-- `4 + 4*i` has norm `32 = 16 * 2`, so it has no square root in `Fp2`. -/
private theorem pole_not_on_curve (y : Fp2) : y * y ≠ 4 + 4 * I := by
  intro hy
  have hn := congrArg Fp2.norm hy
  rw [Fp2.norm_mul, show Fp2.norm (4 + 4 * I) = Fp.ofNat 32 by
    decide_eq_at_model [Fp2.norm, Fp2.add_c0, Fp2.add_c1, Fp2.mul_c0, Fp2.mul_c1, Fp2.i_c0,
      Fp2.i_c1]] at hn
  have hz := congrArg Fp.toZMod hn
  push_toZMod at hz
  apply sq_ne_two (Fp.toZMod (Fp2.norm y) / 4)
  have h4 : (4 : ZMod Fp.modulus) ≠ 0 := by decide
  field_simp [h4]
  linear_combination hz

private theorem d_ne_zero {x y : Fp2} (h : y * y = swuG x) : d x ≠ 0 := by
  intro hd
  have hx : x = -6 + 6 * I := by
    unfold d at hd
    linear_combination hd
  have hc : swuG (-6 + 6 * I) = 4 + 4 * I := by
    decide_eq_at_model [swuG, map_Aprime, map_Bprime]
  rw [hx, hc] at h
  exact pole_not_on_curve y h

-- Off the pole, the isogeny gives the affine point of its rational map.
private theorem isoMapG2_eq {x y : Fp2} (hd : d x ≠ 0) :
    isoMapG2 x y = ⟨xn x / (9 * (d x) ^ 2), y * yn x / (27 * (d x) ^ 3), Fp2.one⟩ := by
  have h2 : ((d x) ^ 2).isZero = false :=
    Bool.eq_false_iff.mpr fun h => pow_ne_zero 2 hd (Fp2.isZero_iff.mp h)
  have h3 : ((d x) ^ 3).isZero = false :=
    Bool.eq_false_iff.mpr fun h => pow_ne_zero 3 hd (Fp2.isZero_iff.mp h)
  unfold isoMapG2
  dsimp only
  rw [xDen_eq, yDen_eq, xNum_eq, yNum_eq, h2, h3]
  simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte, G2.mk.injEq]
  exact ⟨by ring, by ring, trivial⟩

/-- The isogeny sends every affine point of `E'` to an affine point of the twist.

Its denominators never vanish on `E'`, so it never returns the identity there.
-/
theorem isoMapG2_curve_eq {x y : Fp2} (h : y * y = swuG x) :
    ∃ a b, isoMapG2 x y = ⟨a, b, Fp2.one⟩ ∧ b * b = a * a * a + G2.bTwist := by
  have hd := d_ne_zero h
  refine ⟨_, _, isoMapG2_eq hd, ?_⟩
  have h9 : (9 : Fp2) ≠ 0 := by decide_eq_at_model []
  have h27 : (27 : Fp2) ≠ 0 := by decide_eq_at_model []
  have hb : G2.bTwist = 4 + 4 * I := by decide_eq_at_model [G2.map_bTwist]
  have ha : Aprime = 240 * I := by decide_eq_at_model [map_Aprime]
  have hb' : Bprime = 1012 + 1012 * I := by decide_eq_at_model [map_Bprime]
  rw [hb]
  unfold swuG at h
  rw [ha, hb'] at h
  field_simp
  have hp := iso_poly x
  linear_combination 729 * ((yn x) ^ 2 * h + hp)

/-- Mapping a source-curve point produces a nonsingular `G2` point. -/
theorem isoMapG2_valid {x y : Fp2} (h : y * y = swuG x) : G2.Valid (isoMapG2 x y) := by
  obtain ⟨a, b, he, hc⟩ := isoMapG2_curve_eq h
  rw [he]
  exact G2.valid_of_affine_equation hc

/-- The isogeny sends every output of the SSWU map to a nonsingular `G2` point. -/
theorem simpleSwu_isoMapG2_valid {u : Fp2} {p : Fp2 × Fp2} (h : simpleSwu u = .ok p) :
    G2.Valid (isoMapG2 p.1 p.2) :=
  isoMapG2_valid (simpleSwu_curve_eq h)

end EthLib.Cryptography.Bls.HashToCurve
