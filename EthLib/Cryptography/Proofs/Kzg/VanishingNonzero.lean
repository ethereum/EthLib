import EthLib.Cryptography.Proofs.Kzg.Recovery
import EthLib.Cryptography.Proofs.Kzg.CosetInverse

/-!
# Proofs: the vanishing polynomial has no extra roots

The vanishing polynomial is the product of `(x - z_i)` over its chosen roots `z_i`.

A product in a field is zero only if one factor is.

So it is nonzero at every point outside its chosen roots.
-/

namespace EthLib.Cryptography.Kzg
open EthLib.Cryptography.Bls (Fr)
open EthLib.Cryptography.Kzg.Constants
open scoped EthLib.Cryptography.Bls.Fr
attribute [-instance] Fin.instNatPow

private theorem field_mul_ne_zero {F : Type*} [Field F] {a b : F}
    (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := mul_ne_zero ha hb

private theorem eval_linear_factor (z x : Fr) :
    evalPolyAt #[-z, Fr.one] x = x - z := by
  change (Fr.zero + (-z) * Fr.powNat x 0) + Fr.one * Fr.powNat x 1 = x - z
  rw [Bls.Fr.powNat_zero, Bls.Fr.powNat_succ, Bls.Fr.powNat_zero]
  change (0 + (-z) * 1) + 1 * (x * 1) = x - z
  rw [Fin.zero_add, Fin.mul_one, Fin.mul_one, Fin.one_mul]
  exact (add_comm (-z) x).trans (sub_eq_add_neg x z).symm

private theorem foldlM_vanishing_eval_ne_zero (xs : List Fr)
    (init v : PolynomialCoeff) (z : Fr)
    (hz : z ∉ xs) (hi : evalPolyAt init z ≠ 0)
    (h : xs.foldlM (fun q x => multiplyPolynomialcoeff q #[-x, Fr.one]) init = .ok v) :
    evalPolyAt v z ≠ 0 := by
  induction xs generalizing init with
  | nil => cases h; exact hi
  | cons x rest ih =>
    simp only [List.foldlM_cons, Bind.bind, Except.bind] at h
    split at h
    · cases h
    · rename_i q hq
      have hzx : z ≠ x := fun he => hz (List.mem_cons.mpr (Or.inl he))
      have hzr : z ∉ rest := fun he => hz (List.mem_cons.mpr (Or.inr he))
      apply ih q hzr _ h
      rw [evalPolyAt_mulPoly z hq, eval_linear_factor]
      exact field_mul_ne_zero (F := Fr) hi (sub_ne_zero.mpr hzx)

/-- The constructed vanishing polynomial has no roots beyond its input roots. -/
theorem vanishingPolynomialcoeff_eval_ne_zero {zs : Array Fr} {v : PolynomialCoeff}
    (hv : vanishingPolynomialcoeff zs = .ok v) {z : Fr} (hz : z ∉ zs.toList) :
    evalPolyAt v z ≠ 0 := by
  rw [vanishingPolynomialcoeff, ← Array.foldlM_toList] at hv
  apply foldlM_vanishing_eval_ne_zero zs.toList #[Fr.one] v z hz _ hv
  change Fr.zero + Fr.one * Fr.powNat z 0 ≠ 0
  rw [Bls.Fr.powNat_zero]
  change (0 : Fr) + 1 * 1 ≠ 0
  decide

end EthLib.Cryptography.Kzg
