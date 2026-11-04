module

public import EthLib.Cryptography.Proofs.Bls.FinalExponentiation

/-!
# Proofs: the steps of the Miller loop

The Miller loop keeps its point on the twist and multiplies by sparse line values.

A step of the textbook loop multiplies by a line through untwisted points, at the point `P`.

Each step here multiplies by that line times `c w^3`, with `c` in `Fp2`.

The theorems need `T` finite, and `Y ≠ 0` to double or an `x` other than that of `Q` to add.

Then `c` is not zero, and the final exponentiation sends `c w^3` to 1.

No theorem here chains the steps over the whole loop.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

open TwistFrobenius

/-- The line through `(X, Y)` with slope `m`, at the point `(xp, yp)` of `G1`. -/
noncomputable def lineAt (X Y m : Fp12) (xp yp : Fp) : Fp12 :=
  (fpToFp12 yp - Y) - m * (fpToFp12 xp - X)

/-- The untwist of the affine point `(x, y)` of the twist: `(x w^(-2), y w^(-3))`. -/
noncomputable def untwist (x y : Fp2) : Fp12 × Fp12 :=
  (fp2ToFp12 x * w⁻¹ ^ 2, fp2ToFp12 y * w⁻¹ ^ 3)

private theorem lineValue_eq (c0 c2 c3 : Fp2) :
    lineValue c0 c2 c3 = fp2ToFp12 c0 + fp2ToFp12 c2 * w ^ 2 + fp2ToFp12 c3 * w ^ 3 := by
  rw [Fp12.eq_sum (lineValue c0 c2 c3)]
  simp only [lineValue, Fp2.zero_eq_zero, map_zero, zero_mul, add_zero]

private theorem two_eq : Fp2.ofFp (Fp.ofNat 2) = 2 := by decide

private theorem three_eq : Fp2.ofFp (Fp.ofNat 3) = 3 := by decide

private theorem two_ne_zero' : (2 : Fp12) ≠ 0 := by decide

private theorem fp2ToFp12_ne_zero {a : Fp2} (h : a ≠ 0) : fp2ToFp12 a ≠ 0 :=
  (map_ne_zero fp2ToFp12).mpr h

/-- The doubling step multiplies `f^2` by the tangent at the untwist of `T`, times `c w^3`.

Here `T = (X, Y, Z)` is a finite point with `Y ≠ 0`, and `c = 2 Y Z^3`. -/
theorem millerDouble_snd {T : G2} (hz : T.z ≠ 0) (hy : T.y ≠ 0) (xp yp : Fp) (f : Fp12) :
    let X := (untwist (T.x / T.z ^ 2) (T.y / T.z ^ 3)).1
    let Y := (untwist (T.x / T.z ^ 2) (T.y / T.z ^ 3)).2
    (millerDouble T xp yp f).2 =
      f * f * (fp2ToFp12 (2 * T.y * T.z ^ 3) * w ^ 3 * lineAt X Y (3 * X ^ 2 / (2 * Y)) xp yp) := by
  intro X Y
  have hw := w_ne_zero
  have hz' := fp2ToFp12_ne_zero hz
  have hy' := fp2ToFp12_ne_zero hy
  have h2 := two_ne_zero'
  simp only [X, Y, millerDouble, lineValue_eq, untwist, lineAt, two_eq, three_eq, map_mul,
    map_sub, map_neg, map_div₀, map_pow, map_ofNat]
  change _ = _ * (_ * (fp2ToFp12 (Fp2.ofFp yp) - _ - _ * (fp2ToFp12 (Fp2.ofFp xp) - _)))
  field_simp
  ring

/-- The addition step multiplies `f` by the line through the untwists of `T` and `Q`.

The line is multiplied by `c w^3`, with `c = (xq Z^2 - X) Z`.

Here `T = (X, Y, Z)` is a finite point, `Q = (xq, yq)`, and the two have different `x`. -/
theorem millerAdd_snd {T : G2} {xq yq : Fp2} (hz : T.z ≠ 0) (hx : xq * T.z ^ 2 - T.x ≠ 0)
    (xp yp : Fp) (f : Fp12) :
    let X := (untwist (T.x / T.z ^ 2) (T.y / T.z ^ 3)).1
    let Y := (untwist (T.x / T.z ^ 2) (T.y / T.z ^ 3)).2
    let X' := (untwist xq yq).1
    let Y' := (untwist xq yq).2
    (millerAdd T xq yq xp yp f).2 =
      f * (fp2ToFp12 ((xq * T.z ^ 2 - T.x) * T.z) * w ^ 3 *
        lineAt X Y ((Y' - Y) / (X' - X)) xp yp) := by
  intro X Y X' Y'
  have hw := w_ne_zero
  have hz' := fp2ToFp12_ne_zero hz
  have hx' : fp2ToFp12 T.z ^ 2 * fp2ToFp12 xq - fp2ToFp12 T.x ≠ 0 := by
    simpa only [map_sub, map_mul, map_pow, mul_comm] using fp2ToFp12_ne_zero hx
  have hd : fp2ToFp12 xq * w⁻¹ ^ 2 - fp2ToFp12 (T.x / T.z ^ 2) * w⁻¹ ^ 2 ≠ 0 := by
    rw [← sub_mul, ← map_sub]
    refine mul_ne_zero (fp2ToFp12_ne_zero ?_) (pow_ne_zero _ (inv_ne_zero hw))
    intro h
    apply hx
    rw [sub_eq_zero] at h ⊢
    rw [h, div_mul_cancel₀ _ (pow_ne_zero _ hz)]
  simp only [X, Y, X', Y', millerAdd, lineValue_eq, untwist, lineAt, map_mul, map_sub,
    map_neg, map_div₀, map_pow] at hd ⊢
  change _ = _ * (_ * (fp2ToFp12 (Fp2.ofFp yp) - _ - _ * (fp2ToFp12 (Fp2.ofFp xp) - _)))
  field_simp
  ring

end EthLib.Cryptography.Bls
