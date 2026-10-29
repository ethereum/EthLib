import EthLib.Cryptography.Proofs.Sphincs.Encoding
import EthLib.Cryptography.Proofs.Xmss.CodeSize

/-!
# Proofs: the size of the target-sum code

The code is every string of 64 digits, each from 0 to 3, summing to 128.

Its size fixes how often one counter lands in the code.

```text
|C| = [z^128] (1 + z + z^2 + z^3)^64
    = sum over b of (-1)^b * C(64, b) * C(128 - 4b + 63, 63)
|C| / 2^128 = 2^-13.84...,  about one counter in 14,670
```

A digest is a codeword only through its digits, and no two digests share one.

So at most `|C|` of the `2^128` digests are codewords.

If digests were uniform, all `2^32` counters would fail with probability below `exp(-2^18)`.

That bound on the number is proved here.

That digests behave as uniform values is the random-oracle assumption, and is not.
-/

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-- The number of codewords. -/
def CODE_SIZE : ℕ := 23195210617839120199658819909693679

/-- The number of codewords, counted by the leanXMSS dynamic program over digit strings. -/
theorem card_digitStrings_code :
    Fintype.card (Xmss.DigitStrings V CHAIN_LENGTH TARGET_SUM) = CODE_SIZE := by
  rw [← Xmss.countRow_eq_card CHAIN_LENGTH TARGET_SUM V TARGET_SUM (le_refl _)]
  -- About 33,000 additions of large numbers, which the kernel evaluates.
  decide +kernel

/-- The inclusion-exclusion count gives the same number.

Term `b` corrects for `b` digits forced above 3. -/
theorem inclusion_exclusion_code :
    (∑ b ∈ Finset.range (TARGET_SUM / CHAIN_LENGTH + 1),
      (-1 : ℤ) ^ b * (Nat.choose V b : ℤ)
        * (Nat.choose (TARGET_SUM - CHAIN_LENGTH * b + V - 1) (V - 1) : ℤ))
      = CODE_SIZE := by
  -- Pascal's recursion is exponential, falling factorials are linear.
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

/-- Codewords as the specification stores them: digit vectors summing to the target. -/
theorem card_onTarget :
    Nat.card {x : Codeword // Internal.digitSum x = TARGET_SUM} = CODE_SIZE := by
  -- A vector is a function from positions to digits.
  let e : {x : Codeword // Internal.digitSum x = TARGET_SUM}
      ≃ Xmss.DigitStrings V CHAIN_LENGTH TARGET_SUM :=
    { toFun := fun x => ⟨fun i => x.1[i], by
        have := x.2
        rw [digitSum_eq_sum] at this
        simpa using this⟩
      invFun := fun y => ⟨Vector.ofFn y.1, by
        rw [digitSum_eq_sum]
        simpa using y.2⟩
      left_inv := fun x => by ext; simp
      right_inv := fun y => by ext; simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, card_digitStrings_code]

/-- One counter lands in the code with probability `2^-13.84`, between `2^-14` and `2^-13`. -/
theorem code_probability :
    (1 : ℚ) / 2 ^ 14 ≤ (CODE_SIZE : ℚ) / 2 ^ 128 ∧ (CODE_SIZE : ℚ) / 2 ^ 128 ≤ 1 / 2 ^ 13 := by
  rw [CODE_SIZE]
  constructor <;> norm_num

/-- With uniform digests, all `2^32` counters miss the code with probability below `exp(-2^18)`.

```text
    (1 - p)^(2^32) <= exp(-p)^(2^32) = exp(-2^32 p),   and  2^32 p >= 2^18
```
-/
theorem all_counters_fail_probability :
    (1 - (CODE_SIZE : ℝ) / 2 ^ 128) ^ MAX_COUNTER_TRIALS ≤ Real.exp (-(2 ^ 18)) := by
  set p : ℝ := (CODE_SIZE : ℝ) / 2 ^ 128
  -- The expected number of codewords among all counters is above `2^18`.
  have hmean : (2 : ℝ) ^ 18 ≤ 2 ^ 32 * p := by
    simp only [p, CODE_SIZE]
    norm_num
  -- One minus `p` is at most `exp(-p)`, and both sides are nonnegative.
  have hp : 0 ≤ 1 - p := by
    simp only [p, CODE_SIZE]
    norm_num
  calc (1 - p) ^ MAX_COUNTER_TRIALS
      ≤ Real.exp (-p) ^ MAX_COUNTER_TRIALS :=
        pow_le_pow_left₀ hp (by linarith [Real.add_one_le_exp (-p)]) _
    _ = Real.exp (-(2 ^ 32 * p)) := by
        rw [← Real.exp_nat_mul, MAX_COUNTER_TRIALS]
        congr 1
        push_cast
        ring
    _ ≤ Real.exp (-(2 ^ 18)) := Real.exp_le_exp.mpr (by linarith)

end EthLib.Cryptography.Sphincs
