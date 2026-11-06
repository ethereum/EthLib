module

public import EthLib.Cryptography.Bls.Fp
public import EthLib.Cryptography.Proofs.PowMod
public import EthLib.Cryptography.Proofs.Inverse
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.NumberTheory.LucasPrimality
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Proofs: `Fp` as a Mathlib finite field

This file maps `Fp`, which is `Fin p`, to Mathlib's `ZMod p`, as the scalar field proofs do.

The notes of the scalar field proofs on the scoped field instance apply here too.

## Primality of the modulus

The factors of `p - 1` reach 234 bits, beyond the range of `norm_num`.

So the primality of `p` is a chain of Lucas certificates, a Pratt tree.

The factorization is `p - 1 = 2 * 3^2 * 11 * 23 * 47 * 10177 * 859267 * 52437899 * q1 * q2`.

The two large primes are these:

- `q1 = 2584487767265781317813`.
- `q2 = 15778400344354997994418419698270088123916926905054652752758194827714659`.

Each of the two large factors carries its own certificate, with ten auxiliary primes in total.

The kernel checks every modular power, so the whole tree needs no compiled code.

The square root is not treated here, but with the decompression proofs that need it.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Fp

-- Kernel evaluation of `powModAux` (384 recursion steps) and the
-- `decide`-checked factorization identities exceed the default depth.
set_option maxRecDepth 8000
-- The `2 ^ 384` fuel bounds below are only ever evaluated by the
-- kernel inside `decide`; keep the elaborator from warning about them.
set_option exponentiation.threshold 512

/-! ## The Lucas certificate chain (Pratt tree) for `p` -/

private theorem pow_card_sub_one_9272813673901 :
    ((2 : Nat) : ZMod 9272813673901) ^ (9272813673901 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 9272813673901 384 2 (9272813673901 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_9272813673901 :
    ∀ q : Nat, q.Prime → q ∣ 9272813673901 - 1 →
      ((2 : Nat) : ZMod 9272813673901) ^ ((9272813673901 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 9272813673901 - 1 = 2 ^ 2 * (3 * (5 ^ 2 * (7 * (7577 * (582767))))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 9272813673901 384 2 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 9272813673901 384 2 3 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 5 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 9272813673901 384 2 5 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 7 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 9272813673901 384 2 7 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 7577 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 9272813673901 384 2 7577 (by decide) (by decide)
  · obtain rfl := heq 582767 (by norm_num) hdvd
    exact PowMod.natCast_pow_div_ne_one 9272813673901 384 2 582767 (by decide) (by decide)

/-- Pratt-tree node: `9272813673901` is prime (Lucas certificate, witness `2`). -/
private theorem prime_9272813673901 : Nat.Prime 9272813673901 :=
  lucas_primality 9272813673901 ((2 : Nat) : ZMod 9272813673901)
    pow_card_sub_one_9272813673901 pow_div_prime_ne_one_9272813673901

private theorem pow_card_sub_one_1928745244171409 :
    ((3 : Nat) : ZMod 1928745244171409) ^ (1928745244171409 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 1928745244171409 384 3 (1928745244171409 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_1928745244171409 :
    ∀ q : Nat, q.Prime → q ∣ 1928745244171409 - 1 →
      ((3 : Nat) : ZMod 1928745244171409) ^ ((1928745244171409 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 1928745244171409 - 1 = 2 ^ 4 * (13 * (9272813673901)) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 1928745244171409 384 3 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 13 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 1928745244171409 384 3 13 (by decide) (by decide)
  · obtain rfl := heq 9272813673901 prime_9272813673901 hdvd
    exact PowMod.natCast_pow_div_ne_one 1928745244171409 384 3 9272813673901 (by decide) (by decide)

/-- Pratt-tree node: `1928745244171409` is prime (Lucas certificate, witness `3`). -/
private theorem prime_1928745244171409 : Nat.Prime 1928745244171409 :=
  lucas_primality 1928745244171409 ((3 : Nat) : ZMod 1928745244171409)
    pow_card_sub_one_1928745244171409 pow_div_prime_ne_one_1928745244171409

private theorem pow_card_sub_one_7259797099061183477 :
    ((2 : Nat) : ZMod 7259797099061183477) ^ (7259797099061183477 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 7259797099061183477 384 2 (7259797099061183477 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_7259797099061183477 :
    ∀ q : Nat, q.Prime → q ∣ 7259797099061183477 - 1 →
      ((2 : Nat) : ZMod 7259797099061183477) ^ ((7259797099061183477 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 7259797099061183477 - 1 = 2 ^ 2 * (941 * (1928745244171409)) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 7259797099061183477 384 2 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 941 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 7259797099061183477 384 2 941 (by decide) (by decide)
  · obtain rfl := heq 1928745244171409 prime_1928745244171409 hdvd
    exact PowMod.natCast_pow_div_ne_one 7259797099061183477 384 2 1928745244171409 (by decide) (by decide)

/-- Pratt-tree node: `7259797099061183477` is prime (Lucas certificate, witness `2`). -/
private theorem prime_7259797099061183477 : Nat.Prime 7259797099061183477 :=
  lucas_primality 7259797099061183477 ((2 : Nat) : ZMod 7259797099061183477)
    pow_card_sub_one_7259797099061183477 pow_div_prime_ne_one_7259797099061183477

private theorem pow_card_sub_one_2584487767265781317813 :
    ((2 : Nat) : ZMod 2584487767265781317813) ^ (2584487767265781317813 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 2584487767265781317813 384 2 (2584487767265781317813 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_2584487767265781317813 :
    ∀ q : Nat, q.Prime → q ∣ 2584487767265781317813 - 1 →
      ((2 : Nat) : ZMod 2584487767265781317813) ^ ((2584487767265781317813 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 2584487767265781317813 - 1 = 2 ^ 2 * (89 * (7259797099061183477)) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 2584487767265781317813 384 2 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 89 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 2584487767265781317813 384 2 89 (by decide) (by decide)
  · obtain rfl := heq 7259797099061183477 prime_7259797099061183477 hdvd
    exact PowMod.natCast_pow_div_ne_one 2584487767265781317813 384 2 7259797099061183477 (by decide) (by decide)

/-- Pratt-tree node: `2584487767265781317813` is prime (Lucas certificate, witness `2`). -/
private theorem prime_2584487767265781317813 : Nat.Prime 2584487767265781317813 :=
  lucas_primality 2584487767265781317813 ((2 : Nat) : ZMod 2584487767265781317813)
    pow_card_sub_one_2584487767265781317813 pow_div_prime_ne_one_2584487767265781317813

private theorem pow_card_sub_one_64881703735777 :
    ((5 : Nat) : ZMod 64881703735777) ^ (64881703735777 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 64881703735777 384 5 (64881703735777 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_64881703735777 :
    ∀ q : Nat, q.Prime → q ∣ 64881703735777 - 1 →
      ((5 : Nat) : ZMod 64881703735777) ^ ((64881703735777 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 64881703735777 - 1 = 2 ^ 5 * (3 ^ 7 * (927093389)) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 64881703735777 384 5 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 64881703735777 384 5 3 (by decide) (by decide)
  · obtain rfl := heq 927093389 (by norm_num) hdvd
    exact PowMod.natCast_pow_div_ne_one 64881703735777 384 5 927093389 (by decide) (by decide)

/-- Pratt-tree node: `64881703735777` is prime (Lucas certificate, witness `5`). -/
private theorem prime_64881703735777 : Nat.Prime 64881703735777 :=
  lucas_primality 64881703735777 ((5 : Nat) : ZMod 64881703735777)
    pow_card_sub_one_64881703735777 pow_div_prime_ne_one_64881703735777

private theorem pow_card_sub_one_92691255082156974996979 :
    ((3 : Nat) : ZMod 92691255082156974996979) ^ (92691255082156974996979 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 92691255082156974996979 384 3 (92691255082156974996979 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_92691255082156974996979 :
    ∀ q : Nat, q.Prime → q ∣ 92691255082156974996979 - 1 →
      ((3 : Nat) : ZMod 92691255082156974996979) ^ ((92691255082156974996979 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 92691255082156974996979 - 1 = 2 * (3 * (31 * (467 * (16447 * (64881703735777))))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two h
    exact PowMod.natCast_pow_div_ne_one 92691255082156974996979 384 3 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 92691255082156974996979 384 3 3 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 31 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 92691255082156974996979 384 3 31 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 467 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 92691255082156974996979 384 3 467 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 16447 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 92691255082156974996979 384 3 16447 (by decide) (by decide)
  · obtain rfl := heq 64881703735777 prime_64881703735777 hdvd
    exact PowMod.natCast_pow_div_ne_one 92691255082156974996979 384 3 64881703735777 (by decide) (by decide)

/-- Pratt-tree node: `92691255082156974996979` is prime (Lucas certificate, witness `3`). -/
private theorem prime_92691255082156974996979 : Nat.Prime 92691255082156974996979 :=
  lucas_primality 92691255082156974996979 ((3 : Nat) : ZMod 92691255082156974996979)
    pow_card_sub_one_92691255082156974996979 pow_div_prime_ne_one_92691255082156974996979

private theorem pow_card_sub_one_43670061551 :
    ((7 : Nat) : ZMod 43670061551) ^ (43670061551 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 43670061551 384 7 (43670061551 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_43670061551 :
    ∀ q : Nat, q.Prime → q ∣ 43670061551 - 1 →
      ((7 : Nat) : ZMod 43670061551) ^ ((43670061551 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 43670061551 - 1 = 2 * (5 ^ 2 * (17 * (51376543))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two h
    exact PowMod.natCast_pow_div_ne_one 43670061551 384 7 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 5 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 43670061551 384 7 5 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 17 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 43670061551 384 7 17 (by decide) (by decide)
  · obtain rfl := heq 51376543 (by norm_num) hdvd
    exact PowMod.natCast_pow_div_ne_one 43670061551 384 7 51376543 (by decide) (by decide)

/-- Pratt-tree node: `43670061551` is prime (Lucas certificate, witness `7`). -/
private theorem prime_43670061551 : Nat.Prime 43670061551 :=
  lucas_primality 43670061551 ((7 : Nat) : ZMod 43670061551)
    pow_card_sub_one_43670061551 pow_div_prime_ne_one_43670061551

private theorem pow_card_sub_one_13090036741 :
    ((10 : Nat) : ZMod 13090036741) ^ (13090036741 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 13090036741 384 10 (13090036741 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_13090036741 :
    ∀ q : Nat, q.Prime → q ∣ 13090036741 - 1 →
      ((10 : Nat) : ZMod 13090036741) ^ ((13090036741 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 13090036741 - 1 = 2 ^ 2 * (3 * (5 * (11 * (47 * (421987))))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 13090036741 384 10 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 13090036741 384 10 3 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 5 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 13090036741 384 10 5 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 11 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 13090036741 384 10 11 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 47 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 13090036741 384 10 47 (by decide) (by decide)
  · obtain rfl := heq 421987 (by norm_num) hdvd
    exact PowMod.natCast_pow_div_ne_one 13090036741 384 10 421987 (by decide) (by decide)

/-- Pratt-tree node: `13090036741` is prime (Lucas certificate, witness `10`). -/
private theorem prime_13090036741 : Nat.Prime 13090036741 :=
  lucas_primality 13090036741 ((10 : Nat) : ZMod 13090036741)
    pow_card_sub_one_13090036741 pow_div_prime_ne_one_13090036741

private theorem pow_card_sub_one_3819663927398918131021 :
    ((6 : Nat) : ZMod 3819663927398918131021) ^ (3819663927398918131021 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 3819663927398918131021 384 6 (3819663927398918131021 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_3819663927398918131021 :
    ∀ q : Nat, q.Prime → q ∣ 3819663927398918131021 - 1 →
      ((6 : Nat) : ZMod 3819663927398918131021) ^ ((3819663927398918131021 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 3819663927398918131021 - 1 = 2 ^ 2 * (3 ^ 2 * (5 * (19 * (113 * (755057 * (13090036741)))))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 3819663927398918131021 384 6 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one 3819663927398918131021 384 6 3 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 5 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 3819663927398918131021 384 6 5 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 19 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 3819663927398918131021 384 6 19 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 113 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 3819663927398918131021 384 6 113 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 755057 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 3819663927398918131021 384 6 755057 (by decide) (by decide)
  · obtain rfl := heq 13090036741 prime_13090036741 hdvd
    exact PowMod.natCast_pow_div_ne_one 3819663927398918131021 384 6 13090036741 (by decide) (by decide)

/-- Pratt-tree node: `3819663927398918131021` is prime (Lucas certificate, witness `6`). -/
private theorem prime_3819663927398918131021 : Nat.Prime 3819663927398918131021 :=
  lucas_primality 3819663927398918131021 ((6 : Nat) : ZMod 3819663927398918131021)
    pow_card_sub_one_3819663927398918131021 pow_div_prime_ne_one_3819663927398918131021

private theorem pow_card_sub_one_1125266252156850182658904441386709967 :
    ((5 : Nat) : ZMod 1125266252156850182658904441386709967) ^ (1125266252156850182658904441386709967 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 1125266252156850182658904441386709967 384 5 (1125266252156850182658904441386709967 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_1125266252156850182658904441386709967 :
    ∀ q : Nat, q.Prime → q ∣ 1125266252156850182658904441386709967 - 1 →
      ((5 : Nat) : ZMod 1125266252156850182658904441386709967) ^ ((1125266252156850182658904441386709967 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 1125266252156850182658904441386709967 - 1 = 2 * (3373 * (43670061551 * (3819663927398918131021))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two h
    exact PowMod.natCast_pow_div_ne_one 1125266252156850182658904441386709967 384 5 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3373 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 1125266252156850182658904441386709967 384 5 3373 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 43670061551 prime_43670061551 h
    exact PowMod.natCast_pow_div_ne_one 1125266252156850182658904441386709967 384 5 43670061551 (by decide) (by decide)
  · obtain rfl := heq 3819663927398918131021 prime_3819663927398918131021 hdvd
    exact PowMod.natCast_pow_div_ne_one 1125266252156850182658904441386709967 384 5 3819663927398918131021 (by decide) (by decide)

/-- Pratt-tree node: `1125266252156850182658904441386709967` is prime (Lucas certificate, witness `5`). -/
private theorem prime_1125266252156850182658904441386709967 : Nat.Prime 1125266252156850182658904441386709967 :=
  lucas_primality 1125266252156850182658904441386709967 ((5 : Nat) : ZMod 1125266252156850182658904441386709967)
    pow_card_sub_one_1125266252156850182658904441386709967 pow_div_prime_ne_one_1125266252156850182658904441386709967

private theorem pow_card_sub_one_15778400344354997994418419698270088123916926905054652752758194827714659 :
    ((2 : Nat) : ZMod 15778400344354997994418419698270088123916926905054652752758194827714659) ^ (15778400344354997994418419698270088123916926905054652752758194827714659 - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff 15778400344354997994418419698270088123916926905054652752758194827714659 384 2 (15778400344354997994418419698270088123916926905054652752758194827714659 - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_15778400344354997994418419698270088123916926905054652752758194827714659 :
    ∀ q : Nat, q.Prime → q ∣ 15778400344354997994418419698270088123916926905054652752758194827714659 - 1 →
      ((2 : Nat) : ZMod 15778400344354997994418419698270088123916926905054652752758194827714659) ^ ((15778400344354997994418419698270088123916926905054652752758194827714659 - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : 15778400344354997994418419698270088123916926905054652752758194827714659 - 1 = 2 * (3 * (53 * (475709467 * (92691255082156974996979 * (1125266252156850182658904441386709967))))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two h
    exact PowMod.natCast_pow_div_ne_one 15778400344354997994418419698270088123916926905054652752758194827714659 384 2 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 15778400344354997994418419698270088123916926905054652752758194827714659 384 2 3 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 53 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 15778400344354997994418419698270088123916926905054652752758194827714659 384 2 53 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 475709467 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one 15778400344354997994418419698270088123916926905054652752758194827714659 384 2 475709467 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 92691255082156974996979 prime_92691255082156974996979 h
    exact PowMod.natCast_pow_div_ne_one 15778400344354997994418419698270088123916926905054652752758194827714659 384 2 92691255082156974996979 (by decide) (by decide)
  · obtain rfl := heq 1125266252156850182658904441386709967 prime_1125266252156850182658904441386709967 hdvd
    exact PowMod.natCast_pow_div_ne_one 15778400344354997994418419698270088123916926905054652752758194827714659 384 2 1125266252156850182658904441386709967 (by decide) (by decide)

/-- Pratt-tree node: `15778400344354997994418419698270088123916926905054652752758194827714659` is prime (Lucas certificate, witness `2`). -/
private theorem prime_15778400344354997994418419698270088123916926905054652752758194827714659 : Nat.Prime 15778400344354997994418419698270088123916926905054652752758194827714659 :=
  lucas_primality 15778400344354997994418419698270088123916926905054652752758194827714659 ((2 : Nat) : ZMod 15778400344354997994418419698270088123916926905054652752758194827714659)
    pow_card_sub_one_15778400344354997994418419698270088123916926905054652752758194827714659 pow_div_prime_ne_one_15778400344354997994418419698270088123916926905054652752758194827714659

private theorem pow_card_sub_one_modulus :
    ((2 : Nat) : ZMod modulus) ^ (modulus - 1) = 1 := by
  rw [PowMod.natCast_pow_eq_one_iff modulus 384 2 (modulus - 1) (by decide)]
  decide

private theorem pow_div_prime_ne_one_modulus :
    ∀ q : Nat, q.Prime → q ∣ modulus - 1 →
      ((2 : Nat) : ZMod modulus) ^ ((modulus - 1) / q) ≠ 1 := by
  intro q hq hdvd
  have heq : ∀ p' : Nat, p'.Prime → q ∣ p' → q = p' := fun p' hp h =>
    (Nat.prime_dvd_prime_iff_eq hq hp).mp h
  have hfact : modulus - 1 = 2 * (3 ^ 2 * (11 * (23 * (47 * (10177 * (859267 * (52437899 * (2584487767265781317813 * (15778400344354997994418419698270088123916926905054652752758194827714659))))))))) := by decide
  rw [hfact] at hdvd
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2 Nat.prime_two h
    exact PowMod.natCast_pow_div_ne_one modulus 384 2 2 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 3 (by norm_num) (hq.dvd_of_dvd_pow h)
    exact PowMod.natCast_pow_div_ne_one modulus 384 2 3 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 11 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one modulus 384 2 11 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 23 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one modulus 384 2 23 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 47 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one modulus 384 2 47 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 10177 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one modulus 384 2 10177 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 859267 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one modulus 384 2 859267 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 52437899 (by norm_num) h
    exact PowMod.natCast_pow_div_ne_one modulus 384 2 52437899 (by decide) (by decide)
  rcases (hq.dvd_mul).mp hdvd with h | hdvd
  · obtain rfl := heq 2584487767265781317813 prime_2584487767265781317813 h
    exact PowMod.natCast_pow_div_ne_one modulus 384 2 2584487767265781317813 (by decide) (by decide)
  · obtain rfl := heq 15778400344354997994418419698270088123916926905054652752758194827714659 prime_15778400344354997994418419698270088123916926905054652752758194827714659 hdvd
    exact PowMod.natCast_pow_div_ne_one modulus 384 2 15778400344354997994418419698270088123916926905054652752758194827714659 (by decide) (by decide)

/-- The BLS12-381 base field modulus is prime, by a Lucas certificate
chain (Pratt tree): every prime factor of `p - 1` beyond `norm_num`
range carries its own certificate above. Witness: `2` is a
primitive root mod `p`. -/
theorem modulus_prime : Nat.Prime modulus :=
  lucas_primality modulus ((2 : Nat) : ZMod modulus)
    pow_card_sub_one_modulus pow_div_prime_ne_one_modulus

instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

/-- `Fp` is (definitionally) Mathlib's `ZMod Fp.modulus`, as rings. -/
def toZMod : Fp ≃+* ZMod modulus := RingEquiv.refl _

/-! ## The integer of an element

These lemmas give the integer of each result, so a proof does not need the representation of `Fp`.
-/

/-- The integer of an element is below `p`. -/
theorem val_lt (a : Fp) : a.val < modulus := a.isLt

/-- Two elements with the same integer are equal. -/
theorem ext {a b : Fp} (h : a.val = b.val) : a = b := Fin.ext h

/-- The element of `n` has the integer `n mod p`. -/
theorem val_ofNat (n : Nat) : (ofNat n).val = n % modulus := rfl

/-- The element of an integer below `p` has that integer. -/
theorem val_ofNat_of_lt {n : Nat} (h : n < modulus) : (ofNat n).val = n := by
  rw [val_ofNat, Nat.mod_eq_of_lt h]

/-- Zero has the integer `0`. -/
@[simp] theorem val_zero : (0 : Fp).val = 0 := rfl

/-- One has the integer `1`. -/
@[simp] theorem val_one : (1 : Fp).val = 1 := rfl

/-- The integer of a sum is the sum mod `p`. -/
theorem val_add (a b : Fp) : (a + b).val = (a.val + b.val) % modulus := rfl

/-- The integer of a product is the product mod `p`. -/
theorem val_mul (a b : Fp) : (a * b).val = a.val * b.val % modulus := rfl

/-- The integer of a negation is `p` minus the integer, mod `p`. -/
theorem val_neg (a : Fp) : (-a).val = (modulus - a.val) % modulus := rfl

/-- The zero test reads the integer. -/
theorem isZero_eq (a : Fp) : a.isZero = (a.val == 0) := rfl

/-- Zero passes the zero test. -/
theorem zero_isZero : Fp.zero.isZero = true :=
  (isZero_eq 0).trans (by rw [val_zero]; rfl)

/-- One fails the zero test. -/
theorem one_isZero : Fp.one.isZero = false :=
  (isZero_eq 1).trans (by rw [val_one]; rfl)

/-! ## The base-field operations of `Fp` -/

/-- The extensions read the equality of `Fp` as its boolean equality. -/
@[simp] theorem baseField_beq (a b : Fp) : BaseField.beq a b = a.beq b := rfl

/-- The extensions read the zero test of `Fp` as its own. -/
@[simp] theorem baseField_isZero (a : Fp) : BaseField.isZero a = a.isZero := rfl

/-- The extensions read the inverse of `Fp` as its own. -/
@[simp] theorem baseField_inverse (a : Fp) : BaseField.inverse a = a.inverse := rfl

/-- The zero that the extensions read is the zero of `Fp`. -/
@[simp] theorem baseField_zero : (BaseField.zero : Fp) = 0 := rfl

/-- The one that the extensions read is the one of `Fp`. -/
@[simp] theorem baseField_one : (BaseField.one : Fp) = 1 := rfl

/-- The curves read the natural numbers in `Fp` through its own map. -/
@[simp] theorem baseField_ofNat (n : Nat) : (BaseField.ofNat n : Fp) = Fp.ofNat n := rfl

/-- Hash-to-curve raises `Fp` to a natural power through its own map. -/
@[simp] theorem baseField_powNat (a : Fp) (n : Nat) : BaseField.powNat a n = Fp.powNat a n := rfl

/-- The sign of an `Fp` element is the parity of its value. -/
@[simp] theorem baseField_sgn0 (a : Fp) : BaseField.sgn0 a = (a.val % 2 == 1) := rfl

/-- The square root that the extensions read from `Fp` is its own square root.

The square root of `Fp` fails only with the error for a non-square, so the two agree on errors too.
-/
theorem sqrtOrError_eq (a : Fp) : sqrtOrError a = Fp.sqrt a := by
  have hs : Fp.sqrt a = .error .notASquare ∨ ∃ s, Fp.sqrt a = .ok s := by
    unfold Fp.sqrt
    dsimp only
    split <;> simp
  unfold sqrtOrError
  dsimp only [BaseField.sqrt]
  rcases hs with h | ⟨s, h⟩ <;> rw [h]

/-! ## Bridge: spec operations = Mathlib operations -/

/-- `Fp.powNat` is monoid power, phrased over `ZMod Fp.modulus`
(definitionally `Fp`). Public (unlike `Fr`'s analogue): downstream
proofs at large exponents must stay inside the `ZMod` instance world —
a cross-instance defeq check on `x ^ ((p+1)/4)` would try to unfold
the power. `Fp`-facing version: `powNat_eq_pow`. -/
theorem powNat_eq_zmod_pow (a : ZMod modulus) (n : Nat) :
    Fp.powNat a n = a ^ n := by
  induction n using Nat.strongRecOn generalizing a with
  | _ n ih =>
    -- `a` is a `ZMod` element passed where `powNat` takes an `Fp`.
    -- `rw` checks the rewritten goal at `implicit` transparency, where that
    -- is ill-typed, so the equation and the recursive call go in by
    -- `trans` and `erw`.
    refine (Fp.powNat.eq_1 a n).trans ?_
    split
    · rename_i h
      subst h
      rw [pow_zero]
      rfl
    · rename_i h
      dsimp only
      erw [ih (n / 2) (by omega)]
      -- `show` re-elaborates the goal with uniform `ZMod` instance
      -- paths (the `*` inherited from `powNat`'s body is the spec's
      -- `Fin` one), so the `pow` rewrites below can match.
      show (if n % 2 = 1 then a * (a * a) ^ (n / 2) else (a * a) ^ (n / 2)) = a ^ n
      by_cases h2 : n % 2 = 1
      · rw [ite_eq_left h2, ← pow_two, ← pow_mul, ← pow_succ']
        congr 1
        omega
      · rw [ite_eq_right h2, ← pow_two, ← pow_mul]
        congr 1
        omega

/-- The Euclidean inverse is the field inverse of `ZMod p`, and both send `0` to `0`.

It is stated over `ZMod p`, which the field instance below needs. -/
private theorem inverse_eq_zmod_inv (a : ZMod modulus) :
    Fp.inverse a = a⁻¹ :=
  Fin.inverse_map toZMod (fun x => (ZMod.natCast_zmod_val (toZMod x)).symm) a

/-- The Mathlib field structure on `ZMod Fp.modulus`, named so it can be
used as the source of the structure update in `instField` below. -/
-- The exposed field instance reduces through this structure.
@[reducible] def zmodField : Field (ZMod modulus) := inferInstance

/-- The field structure of `ZMod p` on `Fp`, with the division of the specification.

The scalar field proofs explain why the division must be that one, and why the instance is scoped.

Activate it with `open scoped EthLib.Cryptography.Bls.Fp`. -/
scoped instance instField : Field Fp :=
  { zmodField with
    div := (· / ·)
    -- A `by` field keeps its private proof dependencies out of the public data.
    div_eq_mul_inv := by
      intro a b
      exact congrArg (fun x : ZMod modulus =>
          @HMul.hMul (ZMod modulus) (ZMod modulus) (ZMod modulus) _ a x)
        (inverse_eq_zmod_inv b)
    nnratCast_def := fun q => by
      have h : (q : ZMod modulus)
          = (q.num : ZMod modulus) / (q.den : ZMod modulus) := NNRat.cast_def q
      rw [div_eq_mul_inv, ← inverse_eq_zmod_inv] at h
      exact h
    ratCast_def := fun q => by
      have h : (q : ZMod modulus)
          = (q.num : ZMod modulus) / (q.den : ZMod modulus) := Rat.cast_def q
      rw [div_eq_mul_inv, ← inverse_eq_zmod_inv] at h
      exact h }

@[simp] theorem zero_def : Fp.zero = (0 : Fp) := rfl

@[simp] theorem one_def : Fp.one = (1 : Fp) := rfl

/-- The spec's `Fp.ofNat` is Mathlib's `Nat.cast`. -/
theorem ofNat_eq_natCast (n : Nat) : Fp.ofNat n = (n : Fp) := by
  apply Fin.ext
  rw [ofNat, Fin.val_ofNat]
  exact (ZMod.val_natCast modulus n).symm

/-- The spec's `Fp.powNat` is Mathlib's monoid power. -/
theorem powNat_eq_pow (a : Fp) (n : Nat) : a.powNat n = a ^ n :=
  powNat_eq_zmod_pow a n

/-- The Euclidean inverse is the field inverse, and both send `0` to `0`. -/
theorem inverse_eq_inv (a : Fp) : a.inverse = a⁻¹ :=
  inverse_eq_zmod_inv a

/-- The spec's division (`a * b.inverse`, registered at high priority
over core's `Fin` Nat-division) is field division. -/
theorem div_eq_mul_inv' (a b : Fp) : a / b = a * b⁻¹ := by
  show a * b.inverse = a * b⁻¹
  rw [inverse_eq_inv]

-- Smoke tests: the scoped field structure interoperates with the
-- globally available `Fin` instances the executable spec uses.
example (a b : Fp) : a * b = b * a := mul_comm a b
example (a b : Fp) : a - b = a + -b := sub_eq_add_neg a b
example (a : Fp) (h : a ≠ 0) : a * a⁻¹ = 1 := mul_inv_cancel₀ h

end EthLib.Cryptography.Bls.Fp
