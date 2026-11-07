module

public import EthLib.Cryptography.Proofs.Bls.CofactorSubgroupLanding

/-!
# Proofs: the cofactor clearing of `G2` is the multiplication by `h_eff`

RFC 9380 §7 defines the cofactor clearing as the multiplication by the scalar `h_eff` of §8.8.2.

The code computes it by the method of Appendix G.3, with the endomorphism `psi`.

Both are group homomorphisms of the twist, so they agree on a subgroup.

That subgroup holds the torsion witnesses of the cofactor and the generator of order `r`.

On a witness of order `q`, both maps give `O`, because `q` divides `h_eff`.

On the generator, the kernel checks that the method gives `(h_eff mod r) g_2`.

So the subgroup has an order that `h_2 r` divides, and the twist has at most `2 p^2 + 1` points.

Hence it is the whole twist, and the method gives `h_eff P` for every valid point `P`.

So every output of the hash to `G2` is `h_eff` times a valid point of the twist.

See [RFC 9380](https://www.rfc-editor.org/rfc/rfc9380), §7, §8.8.2 and Appendix G.3.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.HashToCurve

open CofactorCertificate CofactorPrimes CofactorSpan

/-- The points on which the cofactor clearing is the multiplication by `h_eff`. -/
private noncomputable def effKernel : AddSubgroup G2.curve.toAffine.Point :=
  (cofactorHom - H_EFF_G2 • AddMonoidHom.id _).ker

/-- A point lies in the subgroup when the two maps agree on it. -/
private theorem mem_effKernel_iff (P : G2.curve.toAffine.Point) :
    P ∈ effKernel ↔ cofactorHom P = H_EFF_G2 • P := by
  change cofactorHom P - H_EFF_G2 • P = 0 ↔ _
  exact sub_eq_zero

/-- A witness of order `q` that the method sends to `O` lies in it, if `q` divides `h_eff`. -/
private theorem mem_eff_of_clear_zero {P : G2} (hP : G2.Valid P)
    (hc : (clearAux P).isInfinity = true) {q : Nat} (hq : q • G2.toPoint P = 0)
    (hdvd : q ∣ H_EFF_G2) : G2.toPoint P ∈ effKernel := by
  rw [mem_effKernel_iff, cofactor_zero_cert P hP hc]
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, mul_nsmul, hq, nsmul_zero]

/-- The generator of order `r` lies in the subgroup, by a kernel computation. -/
private theorem generator_mem_eff : G2.toPoint G2.generator ∈ effKernel := by
  rw [mem_effKernel_iff, ← toPoint_clearCofactor G2.valid_generator, G2.nsmul_generator_mod,
    ← G2.toPoint_mulNat G2.valid_generator]
  apply (G2.projectiveEq_eq_true_iff_toPoint_eq (clearCofactor_valid G2.valid_generator)
    (G2.valid_mulNat G2.valid_generator _)).mp
  rw [← G2.mulNatAux_eq 130 G2.generator _ (by decide), ← clearAux_eq]
  decide_g2_at_model [map_clearAux]

/-- The subgroup is the whole twist. -/
private theorem effKernel_eq_top : effKernel = ⊤ := by
  have h13 : 13 ^ 2 ∣ Nat.card effKernel :=
    prime_sq_dvd_card_of_mem prime_13 effKernel
      (mem_eff_of_clear_zero q13_valid q13_clear_zero q13_annihilator (by decide))
      (mem_eff_of_clear_zero independent13_valid independent13_clear_zero
        independent13_annihilator (by decide))
      q13_annihilator independent13_annihilator q13_nonzero independent13_not_span
  have h23 : 23 ^ 2 ∣ Nat.card effKernel :=
    prime_sq_dvd_card_of_mem prime_23 effKernel
      (mem_eff_of_clear_zero q23_valid q23_clear_zero q23_annihilator (by decide))
      (mem_eff_of_clear_zero independent23_valid independent23_clear_zero
        independent23_annihilator (by decide))
      q23_annihilator independent23_annihilator q23_nonzero independent23_not_span
  have h2713 : 2713 ∣ Nat.card effKernel :=
    prime_dvd_card_of_mem prime_2713 effKernel
      (mem_eff_of_clear_zero q2713_valid q2713_clear_zero q2713_annihilator (by decide))
      q2713_annihilator q2713_nonzero
  have h11953 : 11953 ∣ Nat.card effKernel :=
    prime_dvd_card_of_mem prime_11953 effKernel
      (mem_eff_of_clear_zero q11953_valid q11953_clear_zero q11953_annihilator (by decide))
      q11953_annihilator q11953_nonzero
  have h262069 : 262069 ∣ Nat.card effKernel :=
    prime_dvd_card_of_mem prime_262069 effKernel
      (mem_eff_of_clear_zero q262069_valid q262069_clear_zero q262069_annihilator
        (by decide))
      q262069_annihilator q262069_nonzero
  have hlarge : largePrime ∣ Nat.card effKernel :=
    prime_dvd_card_of_mem largePrime_prime effKernel
      (mem_eff_of_clear_zero large_valid large_clear_zero large_annihilator
        (by decide +kernel))
      large_annihilator large_nonzero
  have hr : Fr.modulus ∣ Nat.card effKernel :=
    prime_dvd_card_of_mem Fr.modulus_prime effKernel generator_mem_eff
      G2.modulus_smul_generator G2.toPoint_generator_ne_zero
  exact eq_top_of_elementary_bound effKernel
    (candidate_dvd_of_prime_divisors h13 h23 h2713 h11953 h262069 hlarge hr)
    G2.card_point_le candidate_gt_field_square

/-- The cofactor clearing of RFC 9380 Appendix G.3 is the multiplication by `h_eff` of §8.8.2.

It holds for every valid point of the twist, as §7 requires of a fast method. -/
theorem toPoint_clearCofactor_eq_hEff {P : G2} (hP : G2.Valid P) :
    G2.toPoint (clearCofactor P) = H_EFF_G2 • G2.toPoint P := by
  rw [toPoint_clearCofactor hP]
  have hm : G2.toPoint P ∈ effKernel := by rw [effKernel_eq_top]; trivial
  exact (mem_effKernel_iff _).mp hm

/-- Every output of the hash to `G2` is `h_eff` times a valid point of the twist. -/
theorem hashToG2_eq_hEff_smul {msg dst : ByteArray} {P : G2} (h : hashToG2 msg dst = .ok P) :
    ∃ Q : G2, G2.Valid Q ∧ G2.toPoint P = H_EFF_G2 • G2.toPoint Q := by
  obtain ⟨Q, hQ, hP⟩ := hashToG2_eq_clearCofactor h
  rw [hP]
  exact ⟨Q, hQ, toPoint_clearCofactor_eq_hEff hQ⟩

end EthLib.Cryptography.Bls.HashToCurve
