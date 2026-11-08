module

public import EthLib.Cryptography.Proofs.Bls.CofactorSpan
public import EthLib.Cryptography.Proofs.Bls.CofactorIndependence
public import EthLib.Cryptography.Proofs.Bls.CofactorPointQ2713
public import EthLib.Cryptography.Proofs.Bls.CofactorPointQ11953
public import EthLib.Cryptography.Proofs.Bls.CofactorPointQ262069
public import EthLib.Cryptography.Proofs.Bls.CofactorPointLarge

/-!
# Proofs: Twist curve cardinality and `G2.generator` span completeness

The torsion witnesses and the size bound give `|E'(Fp2)| = h_2 * r` exactly.

`r` does not divide `h_2`, so the points of order `r` form one cyclic group.

The generator spans it.

So every point of order dividing `r` is `[a] * g_2` for some `a`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.G2

open CofactorCertificate CofactorPrimes CofactorSpan

/-- The torsion witnesses show that `h_2 * r` divides the twist group order. -/
theorem candidate_dvd_card_point : orderCandidate ∣ Nat.card curve.toAffine.Point := by
  have h13 : 13 ^ 2 ∣ Nat.card curve.toAffine.Point :=
    prime_sq_dvd_card_of_independent prime_13 (toPoint q13) (toPoint independent13)
      q13_annihilator independent13_annihilator q13_nonzero independent13_not_span
  have h23 : 23 ^ 2 ∣ Nat.card curve.toAffine.Point :=
    prime_sq_dvd_card_of_independent prime_23 (toPoint q23) (toPoint independent23)
      q23_annihilator independent23_annihilator q23_nonzero independent23_not_span
  have h2713 : 2713 ∣ Nat.card curve.toAffine.Point :=
    prime_dvd_card_of_annihilated prime_2713 (toPoint q2713) q2713_annihilator q2713_nonzero
  have h11953 : 11953 ∣ Nat.card curve.toAffine.Point :=
    prime_dvd_card_of_annihilated prime_11953 (toPoint q11953) q11953_annihilator q11953_nonzero
  have h262069 : 262069 ∣ Nat.card curve.toAffine.Point :=
    prime_dvd_card_of_annihilated prime_262069 (toPoint q262069) q262069_annihilator q262069_nonzero
  have hlarge : largePrime ∣ Nat.card curve.toAffine.Point :=
    prime_dvd_card_of_annihilated largePrime_prime (toPoint large) large_annihilator large_nonzero
  have hr : Fr.modulus ∣ Nat.card curve.toAffine.Point :=
    prime_dvd_card_of_annihilated Fr.modulus_prime (toPoint generator)
      modulus_smul_generator toPoint_generator_ne_zero
  exact candidate_dvd_of_prime_divisors h13 h23 h2713 h11953 h262069 hlarge hr

/-- `|E'(Fp2)| = h_2 * r`, with no appeal to Hasse's theorem or point counting. -/
theorem card_point_eq_candidate : Nat.card curve.toAffine.Point = orderCandidate := by
  obtain ⟨k, hk⟩ := candidate_dvd_card_point
  have hcpos : 0 < Nat.card curve.toAffine.Point := Nat.card_pos
  have hnpos : 0 < orderCandidate := Nat.lt_of_le_of_lt (Nat.zero_le _) candidate_gt_field_square
  have hbound : Nat.card curve.toAffine.Point < 2 * orderCandidate := by
    have h := card_point_le
    have hn := candidate_gt_field_square
    omega
  have hk0 : k ≠ 0 := by
    intro hz
    rw [hz, Nat.mul_zero] at hk
    omega
  have hk2 : k < 2 := by
    apply (Nat.mul_lt_mul_left hnpos).mp
    rw [← hk, Nat.mul_comm orderCandidate 2]
    exact hbound
  have hk1 : k = 1 := by omega
  simpa only [hk1, Nat.mul_one] using hk

/-- Quotienting `E'(Fp2)` by the `G2.generator` span leaves order `orderCandidate / r = h_2`. -/
theorem card_quotient_generator_span :
    Nat.card (curve.toAffine.Point ⧸ AddSubgroup.zmultiples (toPoint generator)) =
      orderCandidate / Fr.modulus := by
  have hc := (AddSubgroup.zmultiples (toPoint generator)).card_eq_card_quotient_mul_card_addSubgroup
  rw [Nat.card_zmultiples, addOrderOf_toPoint_generator, card_point_eq_candidate] at hc
  exact Nat.eq_div_of_mul_eq_left (Nat.ne_of_gt Fr.modulus_pos) hc.symm

/-- The twist cofactor `orderCandidate / r` is coprime to `r`, so `E'(Fp2)[r]` has rank `1`. -/
theorem quotient_generator_span_card_coprime :
    Nat.Coprime (Nat.card (curve.toAffine.Point ⧸ AddSubgroup.zmultiples (toPoint generator)))
      Fr.modulus := by
  rw [card_quotient_generator_span]
  decide +kernel

/-- Every `r`-torsion point on `E'(Fp2)` is a bounded natural multiple of `toPoint generator`. -/
theorem exists_nsmul_generator_of_modulus_smul_eq_zero {Q : curve.toAffine.Point}
    (hQ : Fr.modulus • Q = 0) :
    ∃ n : Nat, n < Fr.modulus ∧ Q = n • toPoint generator := by
  classical
  let H : AddSubgroup curve.toAffine.Point := AddSubgroup.zmultiples (toPoint generator)
  have hqzero : (QuotientAddGroup.mk Q : curve.toAffine.Point ⧸ H) = 0 := by
    by_contra hn
    have hq : Fr.modulus • (QuotientAddGroup.mk Q : curve.toAffine.Point ⧸ H) = 0 := by
      change Fr.modulus • (QuotientAddGroup.mk' H Q) = 0
      rw [← map_nsmul, hQ, _root_.map_zero]
    have hd := prime_dvd_card_of_annihilated Fr.modulus_prime _ hq hn
    change Fr.modulus ∣ Nat.card (curve.toAffine.Point ⧸ AddSubgroup.zmultiples (toPoint generator)) at hd
    rw [card_quotient_generator_span] at hd
    exact (show ¬Fr.modulus ∣ orderCandidate / Fr.modulus by decide +kernel) hd
  have hm : Q ∈ AddSubgroup.zmultiples (toPoint generator) :=
    (QuotientAddGroup.eq_zero_iff Q).mp hqzero
  rw [mem_zmultiples_iff_mem_range_addOrderOf, addOrderOf_toPoint_generator] at hm
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hm
  exact ⟨n, Finset.mem_range.mp hn, he.symm⟩

end EthLib.Cryptography.Bls.G2
