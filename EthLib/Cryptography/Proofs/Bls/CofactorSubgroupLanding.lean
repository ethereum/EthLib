module

public import EthLib.Cryptography.Proofs.Bls.CofactorSpan
public import EthLib.Cryptography.Proofs.Bls.CofactorIndependence
public import EthLib.Cryptography.Proofs.Bls.CofactorPointQ2713
public import EthLib.Cryptography.Proofs.Bls.CofactorPointQ11953
public import EthLib.Cryptography.Proofs.Bls.CofactorPointQ262069
public import EthLib.Cryptography.Proofs.Bls.CofactorPointLarge

/-!
# Proofs: `clearCofactor` and `hashToG2` land in the prime-order `G2` subgroup

Source: `RFC 9380 §8.8.2 and Appendix G.3` and `IRTF draft-irtf-cfrg-bls-signature-04`.

`clearCofactor` sends every point on the twist into the subgroup of order `r`.

The torsion witnesses all lie in the kernel of `[r] * clearCofactor`.

So that kernel is the whole twist, by the size bound `2 * p^2 + 1`.

Hence hash to curve always returns a point in the subgroup of order `r`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.HashToCurve

open CofactorCertificate CofactorPrimes CofactorSpan

private noncomputable def landingKernel : AddSubgroup G2.curve.toAffine.Point :=
  (Fr.modulus • cofactorHom).ker

private theorem mem_landing_of_clear_zero {P : G2} (hP : G2.Valid P)
    (hc : (clearAux P).isInfinity = true) : G2.toPoint P ∈ landingKernel := by
  change Fr.modulus • cofactorHom (G2.toPoint P) = 0
  rw [cofactor_zero_cert P hP hc, nsmul_zero]

private theorem generator_mem_landing : G2.toPoint G2.generator ∈ landingKernel := by
  change Fr.modulus • cofactorHom (G2.toPoint G2.generator) = 0
  rw [← toPoint_clearCofactor G2.valid_generator]
  exact (G2.inSubgroup_iff_modulus_smul_eq_zero
    (clearCofactor_valid G2.valid_generator)).mp
      (clearCofactor_inSubgroup_of_inSubgroup G2.valid_generator G2.inSubgroup_generator)

private theorem landingKernel_eq_top : landingKernel = ⊤ := by
  have h13 : 13 ^ 2 ∣ Nat.card landingKernel :=
    prime_sq_dvd_card_of_mem prime_13 landingKernel
      (mem_landing_of_clear_zero q13_valid q13_clear_zero)
      (mem_landing_of_clear_zero independent13_valid independent13_clear_zero)
      q13_annihilator independent13_annihilator q13_nonzero independent13_not_span
  have h23 : 23 ^ 2 ∣ Nat.card landingKernel :=
    prime_sq_dvd_card_of_mem prime_23 landingKernel
      (mem_landing_of_clear_zero q23_valid q23_clear_zero)
      (mem_landing_of_clear_zero independent23_valid independent23_clear_zero)
      q23_annihilator independent23_annihilator q23_nonzero independent23_not_span
  have h2713 : 2713 ∣ Nat.card landingKernel :=
    prime_dvd_card_of_mem prime_2713 landingKernel
      (mem_landing_of_clear_zero q2713_valid q2713_clear_zero)
      q2713_annihilator q2713_nonzero
  have h11953 : 11953 ∣ Nat.card landingKernel :=
    prime_dvd_card_of_mem prime_11953 landingKernel
      (mem_landing_of_clear_zero q11953_valid q11953_clear_zero)
      q11953_annihilator q11953_nonzero
  have h262069 : 262069 ∣ Nat.card landingKernel :=
    prime_dvd_card_of_mem prime_262069 landingKernel
      (mem_landing_of_clear_zero q262069_valid q262069_clear_zero)
      q262069_annihilator q262069_nonzero
  have hlarge : largePrime ∣ Nat.card landingKernel :=
    prime_dvd_card_of_mem largePrime_prime landingKernel
      (mem_landing_of_clear_zero large_valid large_clear_zero)
      large_annihilator large_nonzero
  have hr : Fr.modulus ∣ Nat.card landingKernel :=
    prime_dvd_card_of_mem Fr.modulus_prime landingKernel generator_mem_landing
      G2.modulus_smul_generator G2.toPoint_generator_ne_zero
  exact eq_top_of_elementary_bound landingKernel
    (candidate_dvd_of_prime_divisors h13 h23 h2713 h11953 h262069 hlarge hr)
    G2.card_point_le candidate_gt_field_square

/-- `cofactorHom` maps every affine twist point into the `r`-torsion subgroup. -/
theorem cofactorHom_modulus_smul (P : G2.curve.toAffine.Point) :
    Fr.modulus • cofactorHom P = 0 := by
  have hm : P ∈ landingKernel := by rw [landingKernel_eq_top]; trivial
  exact hm

/-- Cofactor clearing lands in the subgroup of order `r` (RFC 9380 Appendix G.3). -/
theorem clearCofactor_inSubgroup {P : G2} (hP : G2.Valid P) :
    G2.inSubgroup (clearCofactor P) = true := by
  apply (G2.inSubgroup_iff_modulus_smul_eq_zero (clearCofactor_valid hP)).mpr
  rw [toPoint_clearCofactor hP]
  exact cofactorHom_modulus_smul _

/-- Every successful `hashToG2` output satisfies `G2.inSubgroup P = true` (`RFC 9380 §8.8.2`). -/
theorem hashToG2_inSubgroup {msg dst : ByteArray} {P : G2}
    (h : hashToG2 msg dst = .ok P) : G2.inSubgroup P = true := by
  unfold hashToG2 at h
  cases hf : hashToFieldFp2 msg dst 2 with
  | error e => simp [hf, bind, Except.bind] at h
  | ok us =>
    simp [hf, bind, Except.bind, pure, Except.pure] at h
    subst P
    exact clearCofactor_inSubgroup (G2.valid_add
      (simpleSwu_isoMapG2_valid us[0]!) (simpleSwu_isoMapG2_valid us[1]!))

/-- Hash to curve succeeds on every input and returns a valid point of order `r`. -/
theorem hashToG2_total_inSubgroup (msg dst : ByteArray) :
    ∃ P : G2, hashToG2 msg dst = .ok P ∧ G2.Valid P ∧ G2.inSubgroup P = true := by
  obtain ⟨P, hok, hval⟩ := hashToG2_total msg dst
  exact ⟨P, hok, hval, hashToG2_inSubgroup hok⟩

end EthLib.Cryptography.Bls.HashToCurve
