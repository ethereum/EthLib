module

public import EthLib.Cryptography.Proofs.Bls.MillerChain
public import EthLib.Cryptography.Proofs.Bls.TwistFrobenius
public import EthLib.Cryptography.Proofs.MillerAte

/-!
# Proofs: the Frobenius map on the untwist of `G2`

The linearity of an ate-type pairing rests on hypotheses about the curve, a map `pi` and a group.

This file proves them for the pairing of BLS12-381.

- The curve is `E : y^2 = x^3 + 4` over `Fp12`, and `pi` is the map `(x, y) -> (x^p, y^p)`.
- The group is the untwist of `G2`: the multiples of the untwist of the generator `g_2`.
- The untwist of `g_2` has the order `r`, so the order of each point of the group divides `r`.
- On the group, `pi` acts as the BLS parameter `x = -|x|`.
- So `pi` maps the group into itself.
- In the group, `pi` fixes only `O`, because `r` does not divide `|x| + 1`.
- On the group, `pi^7` acts as `|x|`, because `r` divides `|x|^7 + |x|`.

Take a point `Q` of the group.

Miller's function of `|x|` and `Q` has the divisor `|x| (Q) - (|x| Q) - (|x| - 1) (O)`.

Since `|x| Q = pi^7 Q`, this divisor is `|x| ((Q) - (O)) - ((pi^7 Q) - (O))`.

That is the ate divisor with the coefficient `|x|` at `pi^0` and `-1` at `pi^7`.

Its exponent is `n = |x| - p^7`.

Let `N = (p^12 - 1) / r` be the exponent of the final exponentiation.

Then `z^(N n) = 1` for every nonzero `z` in `Fp12`, because `r` divides `p^7 - |x|`.

`N` is even.

The kernel checks the four facts about numbers: the gcd, the two divisibilities and the parity.

See [Vercauteren](https://eprint.iacr.org/2008/096), "Optimal pairings", Section 2.2.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

open TwistFrobenius WeierstrassCurve.Affine Miller

namespace Ate

/-- The `p`-th power map fixes the coefficients of `y^2 = x^3 + 4` over `Fp12`. -/
theorem ambientCurve_map : ambientCurve.map primeFrobenius = ambientCurve := by
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;> simp [ShortWeierstrass.curve, map_ofNat]

/-- The map `(x, y) -> (x^p, y^p)` on the points of `y^2 = x^3 + 4` over `Fp12`. -/
noncomputable abbrev frobenius : ambientCurve.Point →+ ambientCurve.Point :=
  Miller.mapPoint primeFrobenius ambientCurve_map

/-- It is the Frobenius map under which the untwist of `psi` is computed. -/
theorem frobenius_eq_primeFrobeniusHom : frobenius = primeFrobeniusHom := by
  ext P
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · simp [mapPoint_some, primeFrobeniusHom_apply, ShortWeierstrass.scaledPoint]

/-- The untwist of the generator of `G2`. -/
noncomputable def g2Point : ambientCurve.Point := g2Hom (G2.toPoint G2.generator)

/-- The untwist of the generator has the order `r`, because the untwist is injective. -/
theorem addOrderOf_g2Point : addOrderOf g2Point = Fr.modulus := by
  rw [g2Point, addOrderOf_injective g2Hom g2Hom_injective, G2.addOrderOf_toPoint_generator]

/-- The untwist of `G2`: the multiples of the untwist of its generator. -/
noncomputable def g2Subgroup : AddSubgroup ambientCurve.Point := AddSubgroup.zmultiples g2Point

/-- The order of each point of the untwist of `G2` divides `r`. -/
theorem addOrderOf_dvd_of_mem {R : ambientCurve.Point} (hR : R ∈ g2Subgroup) :
    addOrderOf R ∣ Fr.modulus :=
  addOrderOf_g2Point ▸ addOrderOf_dvd_of_mem_zmultiples hR

/-- On the untwist of the generator, the Frobenius map acts as the BLS parameter `x = -|x|`. -/
theorem frobenius_g2Point : frobenius g2Point = -(blsX • g2Point) := by
  rw [frobenius_eq_primeFrobeniusHom, g2Point, ← untwist_mapPoint, ← hom_apply, hom_generator,
    map_neg, map_nsmul]

/-- On each point of the untwist of `G2`, the Frobenius map acts as `x = -|x|`. -/
theorem frobenius_of_mem {R : ambientCurve.Point} (hR : R ∈ g2Subgroup) :
    frobenius R = -(blsX • R) := by
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hR
  rw [map_zsmul, frobenius_g2Point]
  module

/-- The Frobenius map sends the untwist of `G2` into itself. -/
theorem frobenius_mem {R : ambientCurve.Point} (hR : R ∈ g2Subgroup) :
    frobenius R ∈ g2Subgroup := by
  rw [frobenius_of_mem hR]
  exact g2Subgroup.neg_mem (g2Subgroup.nsmul_mem hR _)

/-- In the untwist of `G2`, the Frobenius map fixes only `O`.

A fixed point has `(|x| + 1) R = O`, and `|x| + 1` is coprime to `r`. -/
theorem eq_zero_of_frobenius_eq {R : ambientCurve.Point} (hR : R ∈ g2Subgroup)
    (h : frobenius R = R) : R = 0 := by
  rw [frobenius_of_mem hR, neg_eq_iff_eq_neg, ← add_eq_zero_iff_eq_neg', ← succ_nsmul'] at h
  have hd := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero h) (addOrderOf_dvd_of_mem hR)
  rw [show Nat.gcd (blsX + 1) Fr.modulus = 1 by decide +kernel, Nat.dvd_one] at hd
  exact AddMonoid.addOrderOf_eq_one_iff.mp hd

/-- On the untwist of `G2`, the `j`-th power of the Frobenius map acts as `x^j`. -/
theorem frobenius_iterate_of_mem {R : ambientCurve.Point} (hR : R ∈ g2Subgroup) (j : ℕ) :
    frobenius^[j] R = (-(blsX : ℤ)) ^ j • R := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, map_zsmul, frobenius_of_mem hR, pow_succ]
    module

/-- On the untwist of `G2`, the seventh power of the Frobenius map acts as `|x|`.

`x^7 = -|x|^7`, and `r` divides `|x|^7 + |x|`. -/
theorem frobenius_iterate_seven {R : ambientCurve.Point} (hR : R ∈ g2Subgroup) :
    frobenius^[7] R = blsX • R := by
  rw [frobenius_iterate_of_mem hR, ← natCast_zsmul, ← sub_eq_zero, ← sub_smul]
  apply (addOrderOf_dvd_iff_zsmul_eq_zero).mp
  exact (Int.natCast_dvd_natCast.mpr (addOrderOf_dvd_of_mem hR)).trans (by decide +kernel)

/-! ## The divisor of Miller's function -/

/-- The pairs `(j, c_j)` of the ate divisor `|x| ((Q) - (O)) - ((pi^7 Q) - (O))`. -/
def ateCoeffs : List (ℕ × ℤ) := [(0, blsX), (7, -1)]

/-- For a point `Q` of the untwist of `G2`, Miller's function of `|x|` and `Q` has the ate divisor.

The divisor is `|x| ((Q) - (O)) - ((pi^7 Q) - (O))`. -/
theorem ratioDivisor_lines {Q : ambientCurve.Point} (hQ : Q ∈ g2Subgroup) :
    ratioDivisor (lines ambientCurve blsX Q) = ateDivisor frobenius Q ateCoeffs := by
  rw [ratioDivisor, linesDivisor_lines, millerDivisor, ateDivisor, ateCoeffs]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.iterate_zero,
    id_eq, frobenius_iterate_seven hQ, add_zero]
  module

/-- For every nonzero `z` in `Fp12`, `z^(N n) = 1`, with `n = |x| - p^7` and `N = (p^12 - 1) / r`.

`r` divides `p^7 - |x|`, so `p^12 - 1` divides `N n`. -/
theorem pow_ateExponent {z : Fp12} (hz : z ≠ 0) :
    z ^ ((finalExpExponent : ℤ) * ateExponent Fp.modulus ateCoeffs) = 1 := by
  have he : (finalExpExponent : ℤ) * ateExponent Fp.modulus ateCoeffs =
      ((Fp.modulus ^ 12 - 1 : ℕ) : ℤ) * -(((Fp.modulus ^ 7 - blsX) / Fr.modulus : ℕ) : ℤ) := by
    decide +kernel
  have h1 : z ^ (Fp.modulus ^ 12 - 1) = 1 := by
    rw [← card_fp12]
    exact FiniteField.pow_card_sub_one_eq_one z hz
  rw [he, zpow_mul, zpow_natCast, h1, one_zpow]

/-- The exponent `(p^12 - 1) / r` of the final exponentiation is even. -/
theorem even_finalExpExponent : Even finalExpExponent :=
  Nat.even_iff.mpr (by decide +kernel)

end Ate

end EthLib.Cryptography.Bls
