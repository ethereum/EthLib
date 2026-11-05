module

public import EthLib.Cryptography.Proofs.Bls.HashToCurve
public import EthLib.Cryptography.Proofs.Bls.G2Validity

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

-- The coefficients of Appendix E.3, written out so that `change` can check them below.
private def K10 : Fp2 := ⟨Fp.ofNat 0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6, Fp.ofNat 0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97d6⟩
private def K11 : Fp2 := ⟨Fp.ofNat 0, Fp.ofNat 0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71a⟩
private def K12 : Fp2 := ⟨Fp.ofNat 0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71e, Fp.ofNat 0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38d⟩
private def K13 : Fp2 := ⟨Fp.ofNat 0x171d6541fa38ccfaed6dea691f5fb614cb14b4e7f4e810aa22d6108f142b85757098e38d0f671c7188e2aaaaaaaa5ed1, Fp.ofNat 0⟩
private def K20 : Fp2 := ⟨Fp.ofNat 0, Fp.ofNat 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa63⟩
private def K21 : Fp2 := ⟨Fp.ofNat 0xc, Fp.ofNat 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa9f⟩
private def K30 : Fp2 := ⟨Fp.ofNat 0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706, Fp.ofNat 0x1530477c7ab4113b59a4c18b076d11930f7da5d4a07f649bf54439d87d27e500fc8c25ebf8c92f6812cfc71c71c6d706⟩
private def K31 : Fp2 := ⟨Fp.ofNat 0, Fp.ofNat 0x5c759507e8e333ebb5b7a9a47d7ed8532c52d39fd3a042a88b58423c50ae15d5c2638e343d9c71c6238aaaaaaaa97be⟩
private def K32 : Fp2 := ⟨Fp.ofNat 0x11560bf17baa99bc32126fced787c88f984f87adf7ae0c7f9a208c6b4f20a4181472aaa9cb8d555526a9ffffffffc71c, Fp.ofNat 0x8ab05f8bdd54cde190937e76bc3e447cc27c3d6fbd7063fcd104635a790520c0a395554e5c6aaaa9354ffffffffe38f⟩
private def K33 : Fp2 := ⟨Fp.ofNat 0x124c9ad43b6cf79bfbf7043de3811ad0761b0f37a1e26286b0e977c69aa274524e79097a56dc4bd9e1b371c71c718b10, Fp.ofNat 0⟩
private def K40 : Fp2 := ⟨Fp.ofNat 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb, Fp.ofNat 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa8fb⟩
private def K41 : Fp2 := ⟨Fp.ofNat 0, Fp.ofNat 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffa9d3⟩
private def K42 : Fp2 := ⟨Fp.ofNat 0x12, Fp.ofNat 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa99⟩

private theorem k10_eq : K10 = (304 + 304 * I) / 9 := by decide +kernel
private theorem k11_eq : K11 = (-24 * I) / 9 := by decide +kernel
private theorem k12_eq : K12 = (12 - 12 * I) / 9 := by decide +kernel
private theorem k13_eq : K13 = 1 / 9 := by decide +kernel
private theorem k20_eq : K20 = -72 * I := by decide +kernel
private theorem k21_eq : K21 = 12 - 12 * I := by decide +kernel
private theorem k30_eq : K30 = (752 + 752 * I) / 27 := by decide +kernel
private theorem k31_eq : K31 = (264 * I) / 27 := by decide +kernel
private theorem k32_eq : K32 = (-18 + 18 * I) / 27 := by decide +kernel
private theorem k33_eq : K33 = -1 / 27 := by decide +kernel
private theorem k40_eq : K40 = -432 - 432 * I := by decide +kernel
private theorem k41_eq : K41 = -216 * I := by decide +kernel
private theorem k42_eq : K42 = 18 - 18 * I := by decide +kernel

-- The denominator `x_den` is `d(x)^2`.
private theorem xDen_eq (x : Fp2) : x * x + k21 * x + k20 = (d x) ^ 2 := by
  change x * x + K21 * x + K20 = _
  rw [k21_eq, k20_eq]
  unfold d
  linear_combination -36 * Fp2.i_sq

-- The denominator `y_den` is `d(x)^3`.
private theorem yDen_eq (x : Fp2) :
    x * x * x + k42 * (x * x) + k41 * x + k40 = (d x) ^ 3 := by
  change x * x * x + K42 * (x * x) + K41 * x + K40 = _
  rw [k42_eq, k41_eq, k40_eq]
  unfold d
  have hi3 : I ^ 3 = -I := by rw [pow_succ, pow_two, Fp2.i_sq]; ring
  ring_nf
  rw [show I ^ 2 = -1 by simpa [pow_two] using Fp2.i_sq, hi3]
  ring

private theorem xNum_eq (x : Fp2) :
    k13 * (x * x * x) + k12 * (x * x) + k11 * x + k10 = xn x / 9 := by
  change K13 * (x * x * x) + K12 * (x * x) + K11 * x + K10 = _
  rw [k13_eq, k12_eq, k11_eq, k10_eq]
  unfold xn
  ring

private theorem yNum_eq (x : Fp2) :
    k33 * (x * x * x) + k32 * (x * x) + k31 * x + k30 = yn x / 27 := by
  change K33 * (x * x * x) + K32 * (x * x) + K31 * x + K30 = _
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
  rw [Fp2.norm_mul, show Fp2.norm (4 + 4 * I) = (32 : Fp) by decide +kernel] at hn
  let z : ZMod Fp.modulus := Fp2.norm y
  have hz : z * z = 32 := hn
  apply sq_ne_two (z / 4)
  have h4 : (4 : ZMod Fp.modulus) ≠ 0 := by decide
  field_simp [h4]
  linear_combination hz

private theorem d_ne_zero {x y : Fp2} (h : y * y = swuG x) : d x ≠ 0 := by
  intro hd
  have hx : x = -6 + 6 * I := by
    unfold d at hd
    linear_combination hd
  have hc : swuG (-6 + 6 * I) = 4 + 4 * I := by decide +kernel
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
  have h9 : (9 : Fp2) ≠ 0 := by decide
  have h27 : (27 : Fp2) ≠ 0 := by decide
  have hb : G2.bTwist = 4 + 4 * I := by decide +kernel
  have ha : Aprime = 240 * I := by decide +kernel
  have hb' : Bprime = 1012 + 1012 * I := by decide +kernel
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
