module

public import EthLib.Cryptography.Proofs.AltBn128.Fp12

/-!
# Proofs: the lines of the Miller loop of alt_bn128

The Miller loop evaluates each line by its coefficients in `Fp12`.

These coefficients are those of the line as the textbook writes it, in the ring `Fp12`.

- A line of slope `l w` through `(x1 w^2, y1 w^3)` is `l w (xt - x1 w^2) - (yt - y1 w^3)`.
- A vertical line is `xt - x1 w^2`.
-/

@[expose] public section

namespace EthLib.Cryptography.AltBn128

open Fp12 Polynomial

open scoped Fin.CommRing

local notation "r" => AdjoinRoot.root poly

/-- A line of slope `l w` is `l w (xt - x1 w^2) - (yt - y1 w^3)`. -/
theorem slopeLine_eq (l x1 y1 : Fp2) (xt yt : Fp) :
    slopeLine l x1 y1 xt yt = ofFp2Hom l * wPow 1 * (ofFpHom xt - ofFp2Hom x1 * wPow 1 ^ 2) -
      (ofFpHom yt - ofFp2Hom y1 * wPow 1 ^ 3) := by
  apply toQuot_injective
  change toQuot _ = toQuotHom _
  simp only [map_sub, map_mul, map_pow]
  change _ = toQuot (ofFp2 l) * toQuot (wPow 1) * (toQuot (ofFp xt) - toQuot (ofFp2 x1) *
    toQuot (wPow 1) ^ 2) - (toQuot (ofFp yt) - toQuot (ofFp2 y1) * toQuot (wPow 1) ^ 3)
  rw [toQuot_eq_terms, toQuot_ofFp2, toQuot_ofFp2, toQuot_ofFp2, toQuot_ofFp, toQuot_ofFp,
    toQuot_wPow]
  simp only [slopeLine, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
    List.getElem_cons_zero, Fp2.sub_c0, Fp2.sub_c1, Fp2.mul_c0, Fp2.mul_c1, map_add, map_sub,
    map_mul, map_neg, map_zero, Fin.val_one, pow_one]
  have h9 : ι (9 : Fp) = 9 := map_ofNat ι 9
  rw [h9]
  linear_combination (ι l.c1 * ι x1.c1 * r ^ 3) * root_pow_twelve

/-- A vertical line is `xt - x1 w^2`. -/
theorem verticalLine_eq (x1 : Fp2) (xt : Fp) :
    verticalLine x1 xt = ofFpHom xt - ofFp2Hom x1 * wPow 1 ^ 2 := by
  apply toQuot_injective
  change toQuot _ = toQuotHom _
  simp only [map_sub, map_mul, map_pow]
  change _ = toQuot (ofFp xt) - toQuot (ofFp2 x1) * toQuot (wPow 1) ^ 2
  rw [toQuot_eq_terms, toQuot_ofFp2, toQuot_ofFp, toQuot_wPow]
  simp only [verticalLine, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
    List.getElem_cons_zero, map_sub, map_mul, map_neg, map_zero, Fin.val_one, pow_one]
  ring

end EthLib.Cryptography.AltBn128
