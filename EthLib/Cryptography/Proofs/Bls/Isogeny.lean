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

/-! ## The isogeny as written -/

namespace Affine

/-- The 3-isogeny of [RFC 9380 Appendix E.3][iso], as written: affine, with two inversions.

It is the reference for the isogeny of the specification, which computes the same point.

[iso]: https://www.rfc-editor.org/rfc/rfc9380#appendix-E.3
-/
def isoMapG2 {F : Type} [BaseField F] (xp yp : Fp2 F) : G2 F :=
  -- The powers `x'^2` and `x'^3`, shared by the four polynomials.
  let xp2 := xp * xp
  let xp3 := xp2 * xp
  -- `x_num = k_(1,3) * x'^3 + k_(1,2) * x'^2 + k_(1,1) * x' + k_(1,0)`.
  let xNum := k13 * xp3 + k12 * xp2 + k11 * xp + k10
  -- `x_den = x'^2 + k_(2,1) * x' + k_(2,0)`.
  let xDen := xp2 + k21 * xp + k20
  -- `y_num = k_(3,3) * x'^3 + k_(3,2) * x'^2 + k_(3,1) * x' + k_(3,0)`.
  let yNum := k33 * xp3 + k32 * xp2 + k31 * xp + k30
  -- `y_den = x'^3 + k_(4,2) * x'^2 + k_(4,1) * x' + k_(4,0)`.
  let yDen := xp3 + k42 * xp2 + k41 * xp + k40
  -- `x = x_num / x_den` and `y = y' * y_num / y_den`, as the affine point with `Z = 1`.
  if xDen.isZero || yDen.isZero then G2.zero else ⟨xNum / xDen, yp * yNum / yDen, Fp2.one⟩

end Affine

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
  exact PowMod.natCast_pow_div_ne_one Fp.modulus 2 2
    (by decide +kernel) hfermat

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
    Affine.isoMapG2 x y = ⟨xn x / (9 * (d x) ^ 2), y * yn x / (27 * (d x) ^ 3), Fp2.one⟩ := by
  have h2 : ((d x) ^ 2).isZero = false :=
    Bool.eq_false_iff.mpr fun h => pow_ne_zero 2 hd (Fp2.isZero_iff.mp h)
  have h3 : ((d x) ^ 3).isZero = false :=
    Bool.eq_false_iff.mpr fun h => pow_ne_zero 3 hd (Fp2.isZero_iff.mp h)
  unfold Affine.isoMapG2
  dsimp only
  rw [xDen_eq, yDen_eq, xNum_eq, yNum_eq, h2, h3]
  simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte, G1.mk.injEq]
  exact ⟨by ring, by ring, trivial⟩

/-- The isogeny sends every affine point of `E'` to an affine point of the twist.

Its denominators never vanish on `E'`, so it never returns the identity there.
-/
theorem Affine.isoMapG2_curve_eq {x y : Fp2} (h : y * y = swuG x) :
    ∃ a b, Affine.isoMapG2 x y = ⟨a, b, Fp2.one⟩ ∧ b * b = a * a * a + G2.bTwist := by
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
theorem Affine.isoMapG2_valid {x y : Fp2} (h : y * y = swuG x) :
    G2.Valid (Affine.isoMapG2 x y) := by
  obtain ⟨a, b, he, hc⟩ := Affine.isoMapG2_curve_eq h
  rw [he]
  exact G2.valid_of_affine_equation hc

/-- The isogeny sends every output of the SSWU map to a nonsingular `G2` point. -/
theorem Affine.simpleSwu_isoMapG2_valid {u : Fp2} {p : Fp2 × Fp2}
    (h : Affine.simpleSwu u = .ok p) : G2.Valid (Affine.isoMapG2 p.1 p.2) :=
  Affine.isoMapG2_valid (Affine.simpleSwu_curve_eq h)

/-! ## The isogeny of the specification, in Jacobian coordinates -/

-- The square of an element is its product by itself.
private theorem square_eq_mul' (a : Fp2) : FieldOps.square a = a * a := by
  rw [Cryptography.Fp2.fieldOps_square, Cryptography.Fp2.square_eq Fp.embedding]

-- A triple `(Z^2 a, Z^3 b, Z)` is the affine point `(a, b)` scaled by `Z`.
open WeierstrassCurve.Jacobian in
private theorem rep_eq_smul (X Y Z a b : Fp2) (hX : X = Z ^ 2 * a) (hY : Y = Z ^ 3 * b) :
    G2.rep ⟨X, Y, Z⟩ = Z • G2.rep ⟨a, b, Fp2.one⟩ := by
  subst hX hY
  rw [smul_fin3]
  simp only [G2.rep_x, G2.rep_y, G2.rep_z, Fp2.one_eq_one, mul_one]
  rfl

-- At `(x t, t, y)`, the Jacobian isogeny is the affine point scaled by `x_den y_den`.
open WeierstrassCurve.Jacobian in
private theorem isoMapG2_jacobian (x t y : Fp2) (ht : t ≠ 0) (h : y * y = swuG x) :
    G2.Valid (isoMapG2 (x * t, t, y)) ∧
      G2.toPoint (isoMapG2 (x * t, t, y)) = G2.toPoint (Affine.isoMapG2 x y) := by
  have hdx := d_ne_zero h
  -- Each homogenized polynomial is the affine one times `t^3`.
  have hB : (x * t * (x * t) + k21 * (x * t * t) + k20 * (t * t)) * t = t ^ 3 * d x ^ 2 := by
    rw [← xDen_eq]; ring
  have hD : x * t * (x * t) * (x * t) + k42 * (x * t * (x * t) * t) + k41 * (x * t * (t * t)) +
      k40 * (t * t * t) = t ^ 3 * d x ^ 3 := by
    rw [← yDen_eq]; ring
  have hA : k13 * (x * t * (x * t) * (x * t)) + k12 * (x * t * (x * t) * t) +
      k11 * (x * t * (t * t)) + k10 * (t * t * t) = t ^ 3 * (xn x / 9) := by
    rw [← xNum_eq]; ring
  have hC : k33 * (x * t * (x * t) * (x * t)) + k32 * (x * t * (x * t) * t) +
      k31 * (x * t * (t * t)) + k30 * (t * t * t) = t ^ 3 * (yn x / 27) := by
    rw [← yNum_eq]; ring
  have hB0 : t ^ 3 * d x ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero 3 ht) (pow_ne_zero 2 hdx)
  have hD0 : t ^ 3 * d x ^ 3 ≠ 0 := mul_ne_zero (pow_ne_zero 3 ht) (pow_ne_zero 3 hdx)
  have hBz : (t ^ 3 * d x ^ 2).isZero = false :=
    Bool.eq_false_iff.mpr fun h => hB0 (Fp2.isZero_iff.mp h)
  have hDz : (t ^ 3 * d x ^ 3).isZero = false :=
    Bool.eq_false_iff.mpr fun h => hD0 (Fp2.isZero_iff.mp h)
  simp only [isoMapG2, square_eq_mul', hA, hB, hC, hD, hBz, hDz, Bool.or_self,
    Bool.false_eq_true, ↓reduceIte]
  rw [isoMapG2_eq hdx]
  have hv : G2.Valid ⟨xn x / (9 * (d x) ^ 2), y * yn x / (27 * (d x) ^ 3), Fp2.one⟩ :=
    isoMapG2_eq hdx ▸ Affine.isoMapG2_valid h
  have hu : IsUnit (t ^ 3 * d x ^ 2 * (t ^ 3 * d x ^ 3)) := (mul_ne_zero hB0 hD0).isUnit
  have h9 : (9 : Fp2) ≠ 0 := by decide_eq_at_model []
  have h27 : (27 : Fp2) ≠ 0 := by decide_eq_at_model []
  have hr := rep_eq_smul
    (t ^ 3 * (xn x / 9) * (t ^ 3 * d x ^ 2) * (t ^ 3 * d x ^ 3 * (t ^ 3 * d x ^ 3)))
    (y * (t ^ 3 * (yn x / 27)) * (t ^ 3 * d x ^ 3 * (t ^ 3 * d x ^ 3)) *
      (t ^ 3 * d x ^ 2 * (t ^ 3 * d x ^ 2) * (t ^ 3 * d x ^ 2)))
    (t ^ 3 * d x ^ 2 * (t ^ 3 * d x ^ 3)) (xn x / (9 * (d x) ^ 2))
    (y * yn x / (27 * (d x) ^ 3)) (by field_simp) (by field_simp)
  refine ⟨?_, ?_⟩
  · show G2.curve.Nonsingular (G2.rep _)
    rw [hr, nonsingular_smul _ hu]
    exact hv
  · show Point.toAffine G2.curve (G2.rep _) = Point.toAffine G2.curve (G2.rep _)
    rw [hr]
    exact Point.toAffine_of_equiv (smul_equiv _ hu)

/-- At a point `(xn / xd, y)` of `E'`, the Jacobian isogeny gives the point of the affine one. -/
theorem isoMapG2_valid_toPoint {p : Fp2 × Fp2 × Fp2} (hd : p.2.1 ≠ 0)
    (h : p.2.2 * p.2.2 = swuG (p.1 / p.2.1)) :
    G2.Valid (isoMapG2 p) ∧
      G2.toPoint (isoMapG2 p) = G2.toPoint (Affine.isoMapG2 (p.1 / p.2.1) p.2.2) := by
  obtain ⟨n, t, y⟩ := p
  dsimp only at hd h ⊢
  have he := isoMapG2_jacobian (n / t) t y hd h
  rwa [div_mul_cancel₀ n hd] at he

/-- The isogeny sends every output of the SSWU map to a nonsingular `G2` point. -/
theorem simpleSwu_isoMapG2_valid (u : Fp2) : G2.Valid (isoMapG2 (simpleSwu u)) :=
  (isoMapG2_valid_toPoint (simpleSwu_xd_ne_zero u) (simpleSwu_curve_eq u)).1

-- Stated on a variable triple, so that neither the elaborator nor the kernel unfolds the map.
private theorem exists_affine_of {u : Fp2} {p : Fp2 × Fp2 × Fp2}
    (h : Affine.simpleSwu u = .ok (p.1 / p.2.1, p.2.2)) (hd : p.2.1 ≠ 0)
    (hc : p.2.2 * p.2.2 = swuG (p.1 / p.2.1)) :
    ∃ q, Affine.simpleSwu u = .ok q ∧
      G2.toPoint (isoMapG2 p) = G2.toPoint (Affine.isoMapG2 q.1 q.2) :=
  ⟨_, h, (isoMapG2_valid_toPoint hd hc).2⟩

/-- The SSWU map then the isogeny give the point of §6.6.2 and Appendix E.3 as written.

Both points are valid, by the two theorems above. -/
theorem toPoint_isoMapG2_simpleSwu (u : Fp2) :
    ∃ p, Affine.simpleSwu u = .ok p ∧
      G2.toPoint (isoMapG2 (simpleSwu u)) = G2.toPoint (Affine.isoMapG2 p.1 p.2) :=
  exists_affine_of (simpleSwu_eq_affine u) (simpleSwu_xd_ne_zero u) (simpleSwu_curve_eq u)

end EthLib.Cryptography.Bls.HashToCurve
