module

public import EthLib.Cryptography.BinaryField.GF64
public import Mathlib.Tactic.NormNum.Prime

/-!
# Proofs: the generator certificate of `GF(2^64)`

The multiplicative group of `K = GF(2^64)` has `N = 2^64 - 1` elements.

- `N` is the product of the seven primes 3, 5, 17, 257, 641, 65537 and 6700417.
- Each prime that divides `N` is one of these seven.
- For each of the seven primes `p`, the power `g^(N / p)` of `g = x` is not `1`.

The seven primes are the Fermat numbers `F0` to `F4` and the two prime factors of `F5`.

The kernel computes each power on the words of `K`, by square and multiply.

Take an element `a` with `a^N = 1`.

It has order `N` when `a^(N / p)` is not `1` for each prime `p` that divides `N`.

So these results certify that `g` has order `N`, once `g^N = 1` is known.

This file does not prove `g^N = 1`, nor that the order of `g` is `N`.

Lidl and Niederreiter, Finite Fields, chapter 2, call an element of order `N` a primitive element.
-/

@[expose] public section

namespace EthLib.Cryptography.BinaryField.GF64

/-- The order of the multiplicative group of K. -/
def ORDER : ℕ := 2 ^ 64 - 1

/-- The order is the product of the seven primes 3, 5, 17, 257, 641, 65537 and 6700417. -/
theorem order_eq_prod : ORDER = 3 * 5 * 17 * 257 * 641 * 65537 * 6700417 := by
  norm_num [ORDER]

/-- A prime that divides the order is one of its seven prime factors. -/
theorem prime_factor_cases {p : ℕ} (hp : p.Prime) (hdvd : p ∣ ORDER) :
    p = 3 ∨ p = 5 ∨ p = 17 ∨ p = 257 ∨ p = 641 ∨ p = 65537 ∨ p = 6700417 := by
  rw [order_eq_prod] at hdvd
  -- Six splits of the product leave one divisibility for each prime factor.
  rw [hp.dvd_mul, hp.dvd_mul, hp.dvd_mul, hp.dvd_mul, hp.dvd_mul, hp.dvd_mul] at hdvd
  rcases hdvd with ((((((h | h) | h) | h) | h) | h) | h) <;>
    rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h] <;> simp

/-! ## The seven powers

The kernel evaluation of each power needs a recursion depth above the default of 512.
-/

set_option maxRecDepth 2000 in
/-- The power `g^((2^64 - 1) / 3)` is not `1`. -/
theorem g_pow_ne_one_3 : g ^ (ORDER / 3) ≠ 1 := by
  show g ^ 6148914691236517205 ≠ 1
  decide +kernel

set_option maxRecDepth 2000 in
/-- The power `g^((2^64 - 1) / 5)` is not `1`. -/
theorem g_pow_ne_one_5 : g ^ (ORDER / 5) ≠ 1 := by
  show g ^ 3689348814741910323 ≠ 1
  decide +kernel

set_option maxRecDepth 2000 in
/-- The power `g^((2^64 - 1) / 17)` is not `1`. -/
theorem g_pow_ne_one_17 : g ^ (ORDER / 17) ≠ 1 := by
  show g ^ 1085102592571150095 ≠ 1
  decide +kernel

set_option maxRecDepth 2000 in
/-- The power `g^((2^64 - 1) / 257)` is not `1`. -/
theorem g_pow_ne_one_257 : g ^ (ORDER / 257) ≠ 1 := by
  show g ^ 71777214294589695 ≠ 1
  decide +kernel

set_option maxRecDepth 2000 in
/-- The power `g^((2^64 - 1) / 641)` is not `1`. -/
theorem g_pow_ne_one_641 : g ^ (ORDER / 641) ≠ 1 := by
  show g ^ 28778071877862015 ≠ 1
  decide +kernel

set_option maxRecDepth 2000 in
/-- The power `g^((2^64 - 1) / 65537)` is not `1`. -/
theorem g_pow_ne_one_65537 : g ^ (ORDER / 65537) ≠ 1 := by
  show g ^ 281470681808895 ≠ 1
  decide +kernel

set_option maxRecDepth 2000 in
/-- The power `g^((2^64 - 1) / 6700417)` is not `1`. -/
theorem g_pow_ne_one_6700417 : g ^ (ORDER / 6700417) ≠ 1 := by
  show g ^ 2753074036095 ≠ 1
  decide +kernel

end EthLib.Cryptography.BinaryField.GF64
