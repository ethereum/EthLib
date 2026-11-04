module

public import EthLib.Cryptography.Secp256r1.Curve
public import EthLib.Cryptography.Proofs.Secp256k1.Field
public import EthLib.Cryptography.Proofs.Pratt

/-!
# Proofs: the fields of secp256r1

Both moduli are prime, by Pratt certificates that the kernel checks.

`Fp` is `ZMod p` by definition, so a proof states its algebra over `ZMod p`.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256r1

namespace Fp

-- The certificates compute powers mod 256-bit numbers, deeper than the default.
set_option maxRecDepth 8000

/-- `6700417` is prime, with witness `5`. -/
private theorem prime_6700417 : Nat.Prime 6700417 :=
  Pratt.prime_of_lucas 6700417 5 256 [(2, 7), (3, 1), (17449, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `204061199` is prime, with witness `11`. -/
private theorem prime_204061199 : Nat.Prime 204061199 :=
  Pratt.prime_of_lucas 204061199 11 256 [(2, 1), (11, 1), (23, 1), (107, 1), (3769, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `34282281433` is prime, with witness `17`. -/
private theorem prime_34282281433 : Nat.Prime 34282281433 :=
  Pratt.prime_of_lucas 34282281433 17 256 [(2, 3), (3, 1), (7, 1), (204061199, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_204061199)
    (by decide) (by decide)

/-- `66417393611` is prime, with witness `6`. -/
private theorem prime_66417393611 : Nat.Prime 66417393611 :=
  Pratt.prime_of_lucas 66417393611 6 256 [(2, 1), (5, 1), (53, 1), (173, 1), (197, 1), (3677, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `11290956913871` is prime, with witness `13`. -/
private theorem prime_11290956913871 : Nat.Prime 11290956913871 :=
  Pratt.prime_of_lucas 11290956913871 13 256 [(2, 1), (5, 1), (17, 1), (66417393611, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_66417393611)
    (by decide) (by decide)

/-- `46076956964474543` is prime, with witness `5`. -/
private theorem prime_46076956964474543 : Nat.Prime 46076956964474543 :=
  Pratt.prime_of_lucas 46076956964474543 5 256 [(2, 1), (23, 1), (18169, 1), (78283, 1), (704251, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `774023187263532362759620327192479577272145303` is prime, with witness `3`. -/
private theorem prime_774023187263532362759620327192479577272145303 : Nat.Prime 774023187263532362759620327192479577272145303 :=
  Pratt.prime_of_lucas 774023187263532362759620327192479577272145303 3 256 [(2, 1), (3, 2), (2411, 1), (34282281433, 1), (11290956913871, 1), (46076956964474543, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_34282281433
    · exact prime_11290956913871
    · exact prime_46076956964474543)
    (by decide) (by decide)

/-- `835945042244614951780389953367877943453916927241` is prime, with witness `11`. -/
private theorem prime_835945042244614951780389953367877943453916927241 : Nat.Prime 835945042244614951780389953367877943453916927241 :=
  Pratt.prime_of_lucas 835945042244614951780389953367877943453916927241 11 256 [(2, 3), (3, 3), (5, 1), (774023187263532362759620327192479577272145303, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact prime_774023187263532362759620327192479577272145303)
    (by decide) (by decide)

theorem modulus_prime : Nat.Prime modulus :=
  Pratt.prime_of_lucas modulus 6 256 [(2, 1), (3, 1), (5, 2), (17, 1), (257, 1), (641, 1), (1531, 1), (65537, 1), (490463, 1), (6700417, 1), (835945042244614951780389953367877943453916927241, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_6700417
    · exact prime_835945042244614951780389953367877943453916927241)
    (by decide) (by decide)

instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

/-- `Fp` is `ZMod modulus` as a ring.

The map is the identity, so it carries every operation over, and the algebra of `ZMod` applies. -/
def toZMod : Fp ≃+* ZMod modulus := RingEquiv.refl _

@[simp] theorem toZMod_zero : toZMod 0 = 0 := rfl

@[simp] theorem toZMod_one : toZMod 1 = 1 := rfl

@[simp] theorem toZMod_neg (a : Fp) : toZMod (-a) = -toZMod a := rfl

@[simp] theorem toZMod_sub (a b : Fp) : toZMod (a - b) = toZMod a - toZMod b := rfl

/-- Square and multiply computes `a^e`, for an exponent below `2^256`. -/
theorem toZMod_powBits (a : Fp) (e : Nat) (he : e < 2 ^ 256) :
    toZMod (Secp256k1.Fin.powBits 256 a e) = toZMod a ^ e :=
  Secp256k1.Fin.powBits_eq_pow 256 a e he

/-- Fermat's inverse is the field inverse, and both send `0` to `0`. -/
@[simp] theorem toZMod_inv (a : Fp) : toZMod a.inv = (toZMod a)⁻¹ := by
  rw [inv, toZMod_powBits _ _ (by decide)]
  by_cases h : toZMod a = 0
  · rw [h, zero_pow (by decide), inv_zero]
  · -- `a^(m - 2) * a = a^(m - 1) = 1`, by Fermat's little theorem.
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, show modulus - 2 + 1 = modulus - 1 by decide]
    exact ZMod.pow_card_sub_one_eq_one h

end Fp

namespace Fn

set_option maxRecDepth 8000

/-- `9350987` is prime, with witness `2`. -/
private theorem prime_9350987 : Nat.Prime 9350987 :=
  Pratt.prime_of_lucas 9350987 2 256 [(2, 1), (17, 1), (229, 1), (1201, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `187019741` is prime, with witness `2`. -/
private theorem prime_187019741 : Nat.Prime 187019741 :=
  Pratt.prime_of_lucas 187019741 2 256 [(2, 2), (5, 1), (9350987, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_9350987)
    (by decide) (by decide)

/-- `311245691` is prime, with witness `2`. -/
private theorem prime_311245691 : Nat.Prime 311245691 :=
  Pratt.prime_of_lucas 311245691 2 256 [(2, 1), (5, 1), (7, 1), (17, 1), (29, 2), (311, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `622491383` is prime, with witness `5`. -/
private theorem prime_622491383 : Nat.Prime 622491383 :=
  Pratt.prime_of_lucas 622491383 5 256 [(2, 1), (311245691, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · norm_num
    · exact prime_311245691)
    (by decide) (by decide)

/-- `3969899` is prime, with witness `2`. -/
private theorem prime_3969899 : Nat.Prime 3969899 :=
  Pratt.prime_of_lucas 3969899 2 256 [(2, 1), (19, 1), (104471, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `1002328039319` is prime, with witness `19`. -/
private theorem prime_1002328039319 : Nat.Prime 1002328039319 :=
  Pratt.prime_of_lucas 1002328039319 19 256 [(2, 1), (126241, 1), (3969899, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact prime_3969899)
    (by decide) (by decide)

/-- `191039911` is prime, with witness `3`. -/
private theorem prime_191039911 : Nat.Prime 191039911 :=
  Pratt.prime_of_lucas 191039911 3 256 [(2, 1), (3, 1), (5, 1), (41, 1), (155317, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num)
    (by decide) (by decide)

/-- `208150935158385979` is prime, with witness `2`. -/
private theorem prime_208150935158385979 : Nat.Prime 208150935158385979 :=
  Pratt.prime_of_lucas 208150935158385979 2 256 [(2, 1), (3, 1), (11, 1), (43, 1), (127, 1), (3023, 1), (191039911, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_191039911)
    (by decide) (by decide)

/-- `2624747550333869278416773953` is prime, with witness `7`. -/
private theorem prime_2624747550333869278416773953 : Nat.Prime 2624747550333869278416773953 :=
  Pratt.prime_of_lucas 2624747550333869278416773953 7 256 [(2, 6), (3, 2), (1297, 1), (16879, 1), (208150935158385979, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_208150935158385979)
    (by decide) (by decide)

theorem modulus_prime : Nat.Prime modulus :=
  Pratt.prime_of_lucas modulus 7 256 [(2, 4), (3, 1), (71, 1), (131, 1), (373, 1), (3407, 1), (17449, 1), (38189, 1), (187019741, 1), (622491383, 1), (1002328039319, 1), (2624747550333869278416773953, 1)] (by decide) (by decide)
    (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_187019741
    · exact prime_622491383
    · exact prime_1002328039319
    · exact prime_2624747550333869278416773953)
    (by decide) (by decide)

instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

/-- `Fn` is `ZMod modulus` as a ring.

The map is the identity, so it carries every operation over, and the algebra of `ZMod` applies. -/
def toZMod : Fn ≃+* ZMod modulus := RingEquiv.refl _

@[simp] theorem toZMod_zero : toZMod 0 = 0 := rfl

@[simp] theorem toZMod_one : toZMod 1 = 1 := rfl

@[simp] theorem toZMod_neg (a : Fn) : toZMod (-a) = -toZMod a := rfl

@[simp] theorem toZMod_sub (a b : Fn) : toZMod (a - b) = toZMod a - toZMod b := rfl

/-- Square and multiply computes `a^e`, for an exponent below `2^256`. -/
theorem toZMod_powBits (a : Fn) (e : Nat) (he : e < 2 ^ 256) :
    toZMod (Secp256k1.Fin.powBits 256 a e) = toZMod a ^ e :=
  Secp256k1.Fin.powBits_eq_pow 256 a e he

/-- Fermat's inverse is the field inverse, and both send `0` to `0`. -/
@[simp] theorem toZMod_inv (a : Fn) : toZMod a.inv = (toZMod a)⁻¹ := by
  rw [inv, toZMod_powBits _ _ (by decide)]
  by_cases h : toZMod a = 0
  · rw [h, zero_pow (by decide), inv_zero]
  · -- `a^(m - 2) * a = a^(m - 1) = 1`, by Fermat's little theorem.
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, show modulus - 2 + 1 = modulus - 1 by decide]
    exact ZMod.pow_card_sub_one_eq_one h

end Fn

end EthLib.Cryptography.Secp256r1
