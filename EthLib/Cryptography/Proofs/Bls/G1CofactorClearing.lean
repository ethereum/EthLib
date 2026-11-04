module

public import EthLib.Cryptography.Proofs.Bls.G1CofactorPoints
public import EthLib.Cryptography.Proofs.Bls.CofactorSpan

/-!
# Proofs: cofactor clearing lands in the subgroup of `G1`

Source: RFC 9380 §7 and §8.8.1, where `h_eff = 1 - x = 3 * 11 * 10177 * 859267 * 52437899`.

The torsion points of the cofactor and the generator all lie in the kernel of `[r * h_eff]`.

So `r * h` divides the size of that kernel, where `h = 3 * 11^2 * 10177^2 * 859267^2 * 52437899^2`.

`E(Fp)` has at most `2 * p + 1` points, and `p < r * h`.

So the kernel is all of `E(Fp)`, and `[h_eff] P` lies in the subgroup of order `r` for every `P`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.MapToCurve

open G1 G1Rotation CofactorSpan

/-- The points that `[r * h_eff]` sends to zero. -/
private noncomputable def landing : AddSubgroup curve.toAffine.Point :=
  ((Fr.modulus * H_EFF_G1) • AddMonoidHom.id curve.toAffine.Point).ker

private theorem mem_landing {q : Nat} {P : curve.toAffine.Point}
    (hq : q ∣ Fr.modulus * H_EFF_G1) (hP : q • P = 0) : P ∈ landing := by
  obtain ⟨c, hc⟩ := hq
  change (Fr.modulus * H_EFF_G1) • P = 0
  rw [hc, mul_comm, ← smul_smul, hP, nsmul_zero]

/-- `r * h`, where `h` is the cofactor of `G1`. -/
private def order : Nat :=
  3 * 11 ^ 2 * 10177 ^ 2 * 859267 ^ 2 * 52437899 ^ 2 * Fr.modulus

private theorem order_dvd {c : Nat} (h3 : 3 ∣ c) (h11 : 11 ^ 2 ∣ c) (h10177 : 10177 ^ 2 ∣ c)
    (h859267 : 859267 ^ 2 ∣ c) (h52437899 : 52437899 ^ 2 ∣ c) (hr : Fr.modulus ∣ c) :
    order ∣ c := by
  have h1 := (show Nat.Coprime 3 (11 ^ 2) by decide).mul_dvd_of_dvd_of_dvd h3 h11
  have h2 := (show Nat.Coprime (3 * 11 ^ 2) (10177 ^ 2) by decide).mul_dvd_of_dvd_of_dvd
    h1 h10177
  have h4 := (show Nat.Coprime (3 * 11 ^ 2 * 10177 ^ 2) (859267 ^ 2) by
    decide).mul_dvd_of_dvd_of_dvd h2 h859267
  have h5 := (show Nat.Coprime (3 * 11 ^ 2 * 10177 ^ 2 * 859267 ^ 2) (52437899 ^ 2) by
    decide).mul_dvd_of_dvd_of_dvd h4 h52437899
  exact (show Nat.Coprime (3 * 11 ^ 2 * 10177 ^ 2 * 859267 ^ 2 * 52437899 ^ 2) Fr.modulus by
    decide).mul_dvd_of_dvd_of_dvd h5 hr

private theorem landing_eq_top : landing = ⊤ := by
  have h3 : 3 ∣ Nat.card landing :=
    prime_dvd_card_of_mem (by norm_num) landing (mem_landing (by decide) p3_torsion)
      p3_torsion p3_ne_zero
  have h11 : 11 ^ 2 ∣ Nat.card landing :=
    prime_sq_dvd_card_of_mem (by norm_num) landing (mem_landing (by decide) p11_torsion)
      (mem_landing (by decide) q11_torsion) p11_torsion q11_torsion p11_ne_zero q11_not_nsmul
  have h10177 : 10177 ^ 2 ∣ Nat.card landing :=
    prime_sq_dvd_card_of_mem (by norm_num) landing (mem_landing (by decide) p10177_torsion)
      (mem_landing (by decide) q10177_torsion) p10177_torsion q10177_torsion p10177_ne_zero
      q10177_not_nsmul
  have h859267 : 859267 ^ 2 ∣ Nat.card landing :=
    prime_sq_dvd_card_of_mem (by norm_num) landing (mem_landing (by decide) p859267_torsion)
      (mem_landing (by decide) q859267_torsion) p859267_torsion q859267_torsion p859267_ne_zero
      q859267_not_nsmul
  have h52437899 : 52437899 ^ 2 ∣ Nat.card landing :=
    prime_sq_dvd_card_of_mem (by norm_num) landing (mem_landing (by decide) p52437899_torsion)
      (mem_landing (by decide) q52437899_torsion) p52437899_torsion q52437899_torsion
      p52437899_ne_zero q52437899_not_nsmul
  have hr : Fr.modulus ∣ Nat.card landing :=
    prime_dvd_card_of_mem Fr.modulus_prime landing
      (mem_landing (dvd_mul_right _ _) modulus_smul_generator) modulus_smul_generator
      toPoint_generator_ne_zero
  exact eq_top_of_elementary_bound landing
    (order_dvd h3 h11 h10177 h859267 h52437899 hr) card_point_le (by decide)

/-- Cofactor clearing sends every valid point to the subgroup of order `r`. -/
theorem clearCofactorG1_inSubgroup {P : G1} (hP : Valid P) :
    inSubgroup (clearCofactorG1 P) = true := by
  apply (inSubgroup_iff_modulus_smul_eq_zero (valid_mulNat hP _)).mpr
  rw [toPoint_mulNat hP, smul_smul]
  have hm : toPoint P ∈ landing := by
    rw [landing_eq_top]
    trivial
  exact hm

end EthLib.Cryptography.Bls.MapToCurve
