module

public import EthLib.Cryptography.Proofs.PowMod
public import Mathlib.NumberTheory.LucasPrimality
public import Mathlib.Tactic.NormNum.Prime

/-!
# Proofs: Kernel-checked Lucas certificates for the prime factors of the twist group order
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.CofactorPrimes
open EthLib.Cryptography

-- The largest certificates check bounds up to `2^449`, above the default threshold of `2^256`.
set_option exponentiation.threshold 512

private theorem pow_one_4920833 : ((3 : Nat) : ZMod 4920833) ^ (4920833 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 4920833 24 3 (4920833 - 1) (by decide)]
  decide +kernel

private theorem pow_ne_4920833 : ∀ q : Nat, q.Prime → q ∣ 4920833 - 1 →
    ((3 : Nat) : ZMod 4920833) ^ ((4920833 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 4920833 - 1 = 2 ^ 9 * (7 * (1373)) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 4920833 24 3 2 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 7 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 4920833 24 3 7 (by decide) (by decide +kernel)
  · obtain rfl := heq 1373 (by norm_num) hdvd
    exact PowMod.natCast_pow_div_ne_one 4920833 24 3 1373 (by decide) (by decide +kernel)

theorem prime_4920833 : Nat.Prime 4920833 :=
  lucas_primality 4920833 ((3 : Nat) : ZMod 4920833) pow_one_4920833 pow_ne_4920833

private theorem pow_one_52872661 : ((2 : Nat) : ZMod 52872661) ^ (52872661 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 52872661 27 2 (52872661 - 1) (by decide)]
  decide +kernel

private theorem pow_ne_52872661 : ∀ q : Nat, q.Prime → q ∣ 52872661 - 1 →
    ((2 : Nat) : ZMod 52872661) ^ ((52872661 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 52872661 - 1 = 2 ^ 2 * (3 ^ 2 * (5 * (83 * (3539)))) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 52872661 27 2 2 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 52872661 27 2 3 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 5 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 52872661 27 2 5 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 83 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 52872661 27 2 83 (by decide) (by decide +kernel)
  · obtain rfl := heq 3539 (by norm_num) hdvd
    exact PowMod.natCast_pow_div_ne_one 52872661 27 2 3539 (by decide) (by decide +kernel)

theorem prime_52872661 : Nat.Prime 52872661 :=
  lucas_primality 52872661 ((2 : Nat) : ZMod 52872661) pow_one_52872661 pow_ne_52872661

private theorem pow_one_12211063 : ((5 : Nat) : ZMod 12211063) ^ (12211063 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 12211063 25 5 (12211063 - 1) (by decide)]
  decide +kernel

private theorem pow_ne_12211063 : ∀ q : Nat, q.Prime → q ∣ 12211063 - 1 →
    ((5 : Nat) : ZMod 12211063) ^ ((12211063 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 12211063 - 1 = 2 * (3 * (103 * (19759))) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 12211063 25 5 2 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 12211063 25 5 3 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 103 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 12211063 25 5 103 (by decide) (by decide +kernel)
  · obtain rfl := heq 19759 (by norm_num) hdvd
    exact PowMod.natCast_pow_div_ne_one 12211063 25 5 19759 (by decide) (by decide +kernel)

theorem prime_12211063 : Nat.Prime 12211063 :=
  lucas_primality 12211063 ((5 : Nat) : ZMod 12211063) pow_one_12211063 pow_ne_12211063

private theorem pow_one_1402724681 : ((3 : Nat) : ZMod 1402724681) ^ (1402724681 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 1402724681 32 3 (1402724681 - 1) (by decide)]
  decide +kernel

private theorem pow_ne_1402724681 : ∀ q : Nat, q.Prime → q ∣ 1402724681 - 1 →
    ((3 : Nat) : ZMod 1402724681) ^ ((1402724681 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 1402724681 - 1 = 2 ^ 3 * (5 * (7 * (1307 * (3833)))) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 1402724681 32 3 2 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 5 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 1402724681 32 3 5 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 7 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 1402724681 32 3 7 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 1307 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 1402724681 32 3 1307 (by decide) (by decide +kernel)
  · obtain rfl := heq 3833 (by norm_num) hdvd
    exact PowMod.natCast_pow_div_ne_one 1402724681 32 3 3833 (by decide) (by decide +kernel)

theorem prime_1402724681 : Nat.Prime 1402724681 :=
  lucas_primality 1402724681 ((3 : Nat) : ZMod 1402724681) pow_one_1402724681 pow_ne_1402724681

private theorem pow_one_16297965815447 : ((5 : Nat) : ZMod 16297965815447) ^ (16297965815447 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 16297965815447 45 5 (16297965815447 - 1) (by decide)]
  decide +kernel

private theorem pow_ne_16297965815447 : ∀ q : Nat, q.Prime → q ∣ 16297965815447 - 1 →
    ((5 : Nat) : ZMod 16297965815447) ^ ((16297965815447 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 16297965815447 - 1 = 2 * (7 ^ 3 * (68059 * (349079))) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 16297965815447 45 5 2 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 7 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 16297965815447 45 5 7 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 68059 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 16297965815447 45 5 68059 (by decide) (by decide +kernel)
  · obtain rfl := heq 349079 (by norm_num) hdvd
    exact PowMod.natCast_pow_div_ne_one 16297965815447 45 5 349079 (by decide) (by decide +kernel)

theorem prime_16297965815447 : Nat.Prime 16297965815447 :=
  lucas_primality 16297965815447 ((5 : Nat) : ZMod 16297965815447) pow_one_16297965815447 pow_ne_16297965815447

private theorem pow_one_810774871 : ((11 : Nat) : ZMod 810774871) ^ (810774871 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 810774871 31 11 (810774871 - 1) (by decide)]
  decide +kernel

private theorem pow_ne_810774871 : ∀ q : Nat, q.Prime → q ∣ 810774871 - 1 →
    ((11 : Nat) : ZMod 810774871) ^ ((810774871 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 810774871 - 1 = 2 * (3 * (5 * (89 * (151 * (2011))))) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 810774871 31 11 2 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 810774871 31 11 3 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 5 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 810774871 31 11 5 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 89 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 810774871 31 11 89 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 151 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 810774871 31 11 151 (by decide) (by decide +kernel)
  · obtain rfl := heq 2011 (by norm_num) hdvd
    exact PowMod.natCast_pow_div_ne_one 810774871 31 11 2011 (by decide) (by decide +kernel)

theorem prime_810774871 : Nat.Prime 810774871 :=
  lucas_primality 810774871 ((11 : Nat) : ZMod 810774871) pow_one_810774871 pow_ne_810774871

private theorem pow_one_63240439939 : ((3 : Nat) : ZMod 63240439939) ^ (63240439939 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 63240439939 37 3 (63240439939 - 1) (by decide)]
  decide +kernel

private theorem pow_ne_63240439939 : ∀ q : Nat, q.Prime → q ∣ 63240439939 - 1 →
    ((3 : Nat) : ZMod 63240439939) ^ ((63240439939 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 63240439939 - 1 = 2 * (3 * (13 * (810774871))) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 63240439939 37 3 2 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 63240439939 37 3 3 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 13 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 63240439939 37 3 13 (by decide) (by decide +kernel)
  · obtain rfl := heq 810774871 prime_810774871 hdvd
    exact PowMod.natCast_pow_div_ne_one 63240439939 37 3 810774871 (by decide) (by decide +kernel)

theorem prime_63240439939 : Nat.Prime 63240439939 :=
  lucas_primality 63240439939 ((3 : Nat) : ZMod 63240439939) pow_one_63240439939 pow_ne_63240439939

private theorem pow_one_1770732318293 : ((2 : Nat) : ZMod 1770732318293) ^ (1770732318293 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 1770732318293 42 2 (1770732318293 - 1) (by decide)]
  decide +kernel

private theorem pow_ne_1770732318293 : ∀ q : Nat, q.Prime → q ∣ 1770732318293 - 1 →
    ((2 : Nat) : ZMod 1770732318293) ^ ((1770732318293 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 1770732318293 - 1 = 2 ^ 2 * (7 * (63240439939)) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 1770732318293 42 2 2 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 7 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 1770732318293 42 2 7 (by decide) (by decide +kernel)
  · obtain rfl := heq 63240439939 prime_63240439939 hdvd
    exact PowMod.natCast_pow_div_ne_one 1770732318293 42 2 63240439939 (by decide) (by decide +kernel)

theorem prime_1770732318293 : Nat.Prime 1770732318293 :=
  lucas_primality 1770732318293 ((2 : Nat) : ZMod 1770732318293) pow_one_1770732318293 pow_ne_1770732318293

private theorem pow_one_21561538103037546247 : ((5 : Nat) : ZMod 21561538103037546247) ^ (21561538103037546247 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 21561538103037546247 66 5 (21561538103037546247 - 1) (by decide)]
  decide +kernel

private theorem pow_ne_21561538103037546247 : ∀ q : Nat, q.Prime → q ∣ 21561538103037546247 - 1 →
    ((5 : Nat) : ZMod 21561538103037546247) ^ ((21561538103037546247 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 21561538103037546247 - 1 = 2 * (3 ^ 3 * (225493 * (1770732318293))) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 21561538103037546247 66 5 2 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 21561538103037546247 66 5 3 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 225493 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 21561538103037546247 66 5 225493 (by decide) (by decide +kernel)
  · obtain rfl := heq 1770732318293 prime_1770732318293 hdvd
    exact PowMod.natCast_pow_div_ne_one 21561538103037546247 66 5 1770732318293 (by decide) (by decide +kernel)

theorem prime_21561538103037546247 : Nat.Prime 21561538103037546247 :=
  lucas_primality 21561538103037546247 ((5 : Nat) : ZMod 21561538103037546247) pow_one_21561538103037546247 pow_ne_21561538103037546247

private theorem pow_one_86246152412150184989 : ((2 : Nat) : ZMod 86246152412150184989) ^ (86246152412150184989 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 86246152412150184989 68 2 (86246152412150184989 - 1) (by decide)]
  decide +kernel

private theorem pow_ne_86246152412150184989 : ∀ q : Nat, q.Prime → q ∣ 86246152412150184989 - 1 →
    ((2 : Nat) : ZMod 86246152412150184989) ^ ((86246152412150184989 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 86246152412150184989 - 1 = 2 ^ 2 * (21561538103037546247) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 86246152412150184989 68 2 2 (by decide) (by decide +kernel)
  · obtain rfl := heq 21561538103037546247 prime_21561538103037546247 hdvd
    exact PowMod.natCast_pow_div_ne_one 86246152412150184989 68 2 21561538103037546247 (by decide) (by decide +kernel)

theorem prime_86246152412150184989 : Nat.Prime 86246152412150184989 :=
  lucas_primality 86246152412150184989 ((2 : Nat) : ZMod 86246152412150184989) pow_one_86246152412150184989 pow_ne_86246152412150184989

private theorem pow_one_6716327 : ((5 : Nat) : ZMod 6716327) ^ (6716327 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 6716327 24 5 (6716327 - 1) (by decide)]
  decide +kernel

private theorem pow_ne_6716327 : ∀ q : Nat, q.Prime → q ∣ 6716327 - 1 →
    ((5 : Nat) : ZMod 6716327) ^ ((6716327 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 6716327 - 1 = 2 * (17 * (197539)) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 6716327 24 5 2 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 17 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 6716327 24 5 17 (by decide) (by decide +kernel)
  · obtain rfl := heq 197539 (by norm_num) hdvd
    exact PowMod.natCast_pow_div_ne_one 6716327 24 5 197539 (by decide) (by decide +kernel)

theorem prime_6716327 : Nat.Prime 6716327 :=
  lucas_primality 6716327 ((5 : Nat) : ZMod 6716327) pow_one_6716327 pow_ne_6716327

private theorem pow_one_40297963 : ((2 : Nat) : ZMod 40297963) ^ (40297963 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 40297963 27 2 (40297963 - 1) (by decide)]
  decide +kernel

private theorem pow_ne_40297963 : ∀ q : Nat, q.Prime → q ∣ 40297963 - 1 →
    ((2 : Nat) : ZMod 40297963) ^ ((40297963 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 40297963 - 1 = 2 * (3 * (6716327)) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 40297963 27 2 2 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 40297963 27 2 3 (by decide) (by decide +kernel)
  · obtain rfl := heq 6716327 prime_6716327 hdvd
    exact PowMod.natCast_pow_div_ne_one 40297963 27 2 6716327 (by decide) (by decide +kernel)

theorem prime_40297963 : Nat.Prime 40297963 :=
  lucas_primality 40297963 ((2 : Nat) : ZMod 40297963) pow_one_40297963 pow_ne_40297963

private theorem pow_one_241787779 : ((2 : Nat) : ZMod 241787779) ^ (241787779 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 241787779 29 2 (241787779 - 1) (by decide)]
  decide +kernel

private theorem pow_ne_241787779 : ∀ q : Nat, q.Prime → q ∣ 241787779 - 1 →
    ((2 : Nat) : ZMod 241787779) ^ ((241787779 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 241787779 - 1 = 2 * (3 * (40297963)) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 241787779 29 2 2 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 241787779 29 2 3 (by decide) (by decide +kernel)
  · obtain rfl := heq 40297963 prime_40297963 hdvd
    exact PowMod.natCast_pow_div_ne_one 241787779 29 2 40297963 (by decide) (by decide +kernel)

theorem prime_241787779 : Nat.Prime 241787779 :=
  lucas_primality 241787779 ((2 : Nat) : ZMod 241787779) pow_one_241787779 pow_ne_241787779

private theorem pow_one_1435735831703 : ((5 : Nat) : ZMod 1435735831703) ^ (1435735831703 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 1435735831703 42 5 (1435735831703 - 1) (by decide)]
  decide +kernel

private theorem pow_ne_1435735831703 : ∀ q : Nat, q.Prime → q ∣ 1435735831703 - 1 →
    ((5 : Nat) : ZMod 1435735831703) ^ ((1435735831703 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 1435735831703 - 1 = 2 * (2969 * (241787779)) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 1435735831703 42 5 2 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2969 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 1435735831703 42 5 2969 (by decide) (by decide +kernel)
  · obtain rfl := heq 241787779 prime_241787779 hdvd
    exact PowMod.natCast_pow_div_ne_one 1435735831703 42 5 241787779 (by decide) (by decide +kernel)

theorem prime_1435735831703 : Nat.Prime 1435735831703 :=
  lucas_primality 1435735831703 ((5 : Nat) : ZMod 1435735831703) pow_one_1435735831703 pow_ne_1435735831703

private theorem pow_one_1367711 : ((7 : Nat) : ZMod 1367711) ^ (1367711 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 1367711 22 7 (1367711 - 1) (by decide)]
  decide +kernel

private theorem pow_ne_1367711 : ∀ q : Nat, q.Prime → q ∣ 1367711 - 1 →
    ((7 : Nat) : ZMod 1367711) ^ ((1367711 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 1367711 - 1 = 2 * (5 * (233 * (587))) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 1367711 22 7 2 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 5 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 1367711 22 7 5 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 233 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 1367711 22 7 233 (by decide) (by decide +kernel)
  · obtain rfl := heq 587 (by norm_num) hdvd
    exact PowMod.natCast_pow_div_ne_one 1367711 22 7 587 (by decide) (by decide +kernel)

theorem prime_1367711 : Nat.Prime 1367711 :=
  lucas_primality 1367711 ((7 : Nat) : ZMod 1367711) pow_one_1367711 pow_ne_1367711

private theorem pow_one_12192593745179 : ((2 : Nat) : ZMod 12192593745179) ^ (12192593745179 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 12192593745179 45 2 (12192593745179 - 1) (by decide)]
  decide +kernel

private theorem pow_ne_12192593745179 : ∀ q : Nat, q.Prime → q ∣ 12192593745179 - 1 →
    ((2 : Nat) : ZMod 12192593745179) ^ ((12192593745179 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 12192593745179 - 1 = 2 * (7 * (11 * (107 * (541 * (1367711))))) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 12192593745179 45 2 2 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 7 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 12192593745179 45 2 7 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 11 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 12192593745179 45 2 11 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 107 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 12192593745179 45 2 107 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 541 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 12192593745179 45 2 541 (by decide) (by decide +kernel)
  · obtain rfl := heq 1367711 prime_1367711 hdvd
    exact PowMod.natCast_pow_div_ne_one 12192593745179 45 2 1367711 (by decide) (by decide +kernel)

theorem prime_12192593745179 : Nat.Prime 12192593745179 :=
  lucas_primality 12192593745179 ((2 : Nat) : ZMod 12192593745179) pow_one_12192593745179 pow_ne_12192593745179

private theorem pow_one_512088937297519 : ((6 : Nat) : ZMod 512088937297519) ^ (512088937297519 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 512088937297519 50 6 (512088937297519 - 1) (by decide)]
  decide +kernel

private theorem pow_ne_512088937297519 : ∀ q : Nat, q.Prime → q ∣ 512088937297519 - 1 →
    ((6 : Nat) : ZMod 512088937297519) ^ ((512088937297519 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 512088937297519 - 1 = 2 * (3 * (7 * (12192593745179))) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 512088937297519 50 6 2 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 512088937297519 50 6 3 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 7 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 512088937297519 50 6 7 (by decide) (by decide +kernel)
  · obtain rfl := heq 12192593745179 prime_12192593745179 hdvd
    exact PowMod.natCast_pow_div_ne_one 512088937297519 50 6 12192593745179 (by decide) (by decide +kernel)

theorem prime_512088937297519 : Nat.Prime 512088937297519 :=
  lucas_primality 512088937297519 ((6 : Nat) : ZMod 512088937297519) pow_one_512088937297519 pow_ne_512088937297519

private theorem pow_one_1857858664515398933 : ((2 : Nat) : ZMod 1857858664515398933) ^ (1857858664515398933 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 1857858664515398933 62 2 (1857858664515398933 - 1) (by decide)]
  decide +kernel

private theorem pow_ne_1857858664515398933 : ∀ q : Nat, q.Prime → q ∣ 1857858664515398933 - 1 →
    ((2 : Nat) : ZMod 1857858664515398933) ^ ((1857858664515398933 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 1857858664515398933 - 1 = 2 ^ 2 * (907 * (512088937297519)) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 1857858664515398933 62 2 2 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 907 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 1857858664515398933 62 2 907 (by decide) (by decide +kernel)
  · obtain rfl := heq 512088937297519 prime_512088937297519 hdvd
    exact PowMod.natCast_pow_div_ne_one 1857858664515398933 62 2 512088937297519 (by decide) (by decide +kernel)

theorem prime_1857858664515398933 : Nat.Prime 1857858664515398933 :=
  lucas_primality 1857858664515398933 ((2 : Nat) : ZMod 1857858664515398933) pow_one_1857858664515398933 pow_ne_1857858664515398933

private theorem pow_one_22294303974184787197 : ((14 : Nat) : ZMod 22294303974184787197) ^ (22294303974184787197 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 22294303974184787197 66 14 (22294303974184787197 - 1) (by decide)]
  decide +kernel

private theorem pow_ne_22294303974184787197 : ∀ q : Nat, q.Prime → q ∣ 22294303974184787197 - 1 →
    ((14 : Nat) : ZMod 22294303974184787197) ^ ((22294303974184787197 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 22294303974184787197 - 1 = 2 ^ 2 * (3 * (1857858664515398933)) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 22294303974184787197 66 14 2 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 22294303974184787197 66 14 3 (by decide) (by decide +kernel)
  · obtain rfl := heq 1857858664515398933 prime_1857858664515398933 hdvd
    exact PowMod.natCast_pow_div_ne_one 22294303974184787197 66 14 1857858664515398933 (by decide) (by decide +kernel)

theorem prime_22294303974184787197 : Nat.Prime 22294303974184787197 :=
  lucas_primality 22294303974184787197 ((14 : Nat) : ZMod 22294303974184787197) pow_one_22294303974184787197 pow_ne_22294303974184787197

private theorem pow_one_19931107752921199754119 : ((3 : Nat) : ZMod 19931107752921199754119) ^ (19931107752921199754119 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 19931107752921199754119 76 3 (19931107752921199754119 - 1) (by decide)]
  decide +kernel

private theorem pow_ne_19931107752921199754119 : ∀ q : Nat, q.Prime → q ∣ 19931107752921199754119 - 1 →
    ((3 : Nat) : ZMod 19931107752921199754119) ^ ((19931107752921199754119 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 19931107752921199754119 - 1 = 2 * (3 * (149 * (22294303974184787197))) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 19931107752921199754119 76 3 2 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 19931107752921199754119 76 3 3 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 149 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 19931107752921199754119 76 3 149 (by decide) (by decide +kernel)
  · obtain rfl := heq 22294303974184787197 prime_22294303974184787197 hdvd
    exact PowMod.natCast_pow_div_ne_one 19931107752921199754119 76 3 22294303974184787197 (by decide) (by decide +kernel)

theorem prime_19931107752921199754119 : Nat.Prime 19931107752921199754119 :=
  lucas_primality 19931107752921199754119 ((3 : Nat) : ZMod 19931107752921199754119) pow_one_19931107752921199754119 pow_ne_19931107752921199754119

private theorem pow_one_81162125843606155545104998607900118769099783 : ((5 : Nat) : ZMod 81162125843606155545104998607900118769099783) ^ (81162125843606155545104998607900118769099783 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 81162125843606155545104998607900118769099783 147 5 (81162125843606155545104998607900118769099783 - 1) (by decide)]
  decide +kernel

private theorem pow_ne_81162125843606155545104998607900118769099783 : ∀ q : Nat, q.Prime → q ∣ 81162125843606155545104998607900118769099783 - 1 →
    ((5 : Nat) : ZMod 81162125843606155545104998607900118769099783) ^ ((81162125843606155545104998607900118769099783 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 81162125843606155545104998607900118769099783 - 1 = 2 * (3 ^ 2 * (2731 * (57697 * (1435735831703 * (19931107752921199754119))))) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 81162125843606155545104998607900118769099783 147 5 2 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 81162125843606155545104998607900118769099783 147 5 3 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2731 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 81162125843606155545104998607900118769099783 147 5 2731 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 57697 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 81162125843606155545104998607900118769099783 147 5 57697 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 1435735831703 prime_1435735831703 h
    exact PowMod.natCast_pow_div_ne_one 81162125843606155545104998607900118769099783 147 5 1435735831703 (by decide) (by decide +kernel)
  · obtain rfl := heq 19931107752921199754119 prime_19931107752921199754119 hdvd
    exact PowMod.natCast_pow_div_ne_one 81162125843606155545104998607900118769099783 147 5 19931107752921199754119 (by decide) (by decide +kernel)

theorem prime_81162125843606155545104998607900118769099783 : Nat.Prime 81162125843606155545104998607900118769099783 :=
  lucas_primality 81162125843606155545104998607900118769099783 ((5 : Nat) : ZMod 81162125843606155545104998607900118769099783) pow_one_81162125843606155545104998607900118769099783 pow_ne_81162125843606155545104998607900118769099783

private theorem pow_one_26935696298915610574513298451669528361624243820491956655650666425177 : ((3 : Nat) : ZMod 26935696298915610574513298451669528361624243820491956655650666425177) ^ (26935696298915610574513298451669528361624243820491956655650666425177 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 26935696298915610574513298451669528361624243820491956655650666425177 225 3 (26935696298915610574513298451669528361624243820491956655650666425177 - 1) (by decide)]
  decide +kernel

private theorem pow_ne_26935696298915610574513298451669528361624243820491956655650666425177 : ∀ q : Nat, q.Prime → q ∣ 26935696298915610574513298451669528361624243820491956655650666425177 - 1 →
    ((3 : Nat) : ZMod 26935696298915610574513298451669528361624243820491956655650666425177) ^ ((26935696298915610574513298451669528361624243820491956655650666425177 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 26935696298915610574513298451669528361624243820491956655650666425177 - 1 = 2 ^ 3 * (13 * (37 * (86246152412150184989 * (81162125843606155545104998607900118769099783)))) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 26935696298915610574513298451669528361624243820491956655650666425177 225 3 2 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 13 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 26935696298915610574513298451669528361624243820491956655650666425177 225 3 13 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 37 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 26935696298915610574513298451669528361624243820491956655650666425177 225 3 37 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 86246152412150184989 prime_86246152412150184989 h
    exact PowMod.natCast_pow_div_ne_one 26935696298915610574513298451669528361624243820491956655650666425177 225 3 86246152412150184989 (by decide) (by decide +kernel)
  · obtain rfl := heq 81162125843606155545104998607900118769099783 prime_81162125843606155545104998607900118769099783 hdvd
    exact PowMod.natCast_pow_div_ne_one 26935696298915610574513298451669528361624243820491956655650666425177 225 3 81162125843606155545104998607900118769099783 (by decide) (by decide +kernel)

theorem prime_26935696298915610574513298451669528361624243820491956655650666425177 : Nat.Prime 26935696298915610574513298451669528361624243820491956655650666425177 :=
  lucas_primality 26935696298915610574513298451669528361624243820491956655650666425177 ((3 : Nat) : ZMod 26935696298915610574513298451669528361624243820491956655650666425177) pow_one_26935696298915610574513298451669528361624243820491956655650666425177 pow_ne_26935696298915610574513298451669528361624243820491956655650666425177

private theorem pow_one_4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 : ((3 : Nat) : ZMod 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297) ^ (4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 382 3 (4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 - 1) (by decide)]
  decide +kernel

private theorem pow_ne_4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 : ∀ q : Nat, q.Prime → q ∣ 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 - 1 →
    ((3 : Nat) : ZMod 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297) ^ ((4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 - 1 = 2 ^ 3 * (373 * (8329 * (37501 * (661873 * (12211063 * (1402724681 * (16297965815447 * (26935696298915610574513298451669528361624243820491956655650666425177)))))))) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 382 3 2 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 373 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 382 3 373 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 8329 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 382 3 8329 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 37501 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 382 3 37501 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 661873 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 382 3 661873 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 12211063 prime_12211063 h
    exact PowMod.natCast_pow_div_ne_one 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 382 3 12211063 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 1402724681 prime_1402724681 h
    exact PowMod.natCast_pow_div_ne_one 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 382 3 1402724681 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 16297965815447 prime_16297965815447 h
    exact PowMod.natCast_pow_div_ne_one 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 382 3 16297965815447 (by decide) (by decide +kernel)
  · obtain rfl := heq 26935696298915610574513298451669528361624243820491956655650666425177 prime_26935696298915610574513298451669528361624243820491956655650666425177 hdvd
    exact PowMod.natCast_pow_div_ne_one 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 382 3 26935696298915610574513298451669528361624243820491956655650666425177 (by decide) (by decide +kernel)

theorem prime_4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 : Nat.Prime 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 :=
  lucas_primality 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 ((3 : Nat) : ZMod 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297) pow_one_4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 pow_ne_4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297

private theorem pow_one_402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 : ((13 : Nat) : ZMod 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249) ^ (402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 449 13 (402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 - 1) (by decide)]
  decide +kernel

private theorem pow_ne_402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 : ∀ q : Nat, q.Prime → q ∣ 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 - 1 →
    ((13 : Nat) : ZMod 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249) ^ ((402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 - 1 = 2 ^ 4 * (3 * (11 * (631 * (4920833 * (52872661 * (4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297)))))) := by decide +kernel
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 449 13 2 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 449 13 3 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 11 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 449 13 11 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 631 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 449 13 631 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 4920833 prime_4920833 h
    exact PowMod.natCast_pow_div_ne_one 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 449 13 4920833 (by decide) (by decide +kernel)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 52872661 prime_52872661 h
    exact PowMod.natCast_pow_div_ne_one 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 449 13 52872661 (by decide) (by decide +kernel)
  · obtain rfl := heq 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 prime_4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 hdvd
    exact PowMod.natCast_pow_div_ne_one 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 449 13 4638704574076146691498289350639807119782054683906549022985642612861209609656189848749536921852444848596916990932297 (by decide) (by decide +kernel)

theorem prime_402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 : Nat.Prime 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 :=
  lucas_primality 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 ((13 : Nat) : ZMod 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249) pow_one_402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249 pow_ne_402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249

theorem prime_13 : Nat.Prime 13 := by norm_num

theorem prime_23 : Nat.Prime 23 := by norm_num

theorem prime_2713 : Nat.Prime 2713 := by norm_num

theorem prime_11953 : Nat.Prime 11953 := by norm_num

theorem prime_262069 : Nat.Prime 262069 := by norm_num

def largePrime : Nat := 402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249

theorem largePrime_prime : Nat.Prime largePrime :=
  prime_402096035359507321594726366720466575392706800671181159425656785868777272553337714697862511267018014931937703598282857976535744623203249

end EthLib.Cryptography.Bls.CofactorPrimes
