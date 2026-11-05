module

public import EthLib.Cryptography.Proofs.Xmss.Encoding

/-!
# Proofs: the size of the target-sum code

The code is every string of 58 digits, each from 0 to 3, summing to 106.

Its size fixes how often one randomizer trial lands in the code.

```text
|C| = [z^106] (1 + z + z^2 + z^3)^58
    = sum over b of (-1)^b * C(58, b) * C(106 - 4b + 57, 57)
|C| / 2^128 = 2^-20.0045...
```

So one signature grinds about `2^20` trials per layer, as the specification states.

A digest is a codeword only through its digits, and no two digests share one.

So at most `|C|` of the `2^128` digests are codewords.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-- The number of codewords. -/
def CODE_SIZE : ℕ := 323504418562481994618807509487594

/-! ## The size of the code -/

/-- The number of codewords. -/
theorem card_digitStrings_code :
    Fintype.card (Wots.DigitStrings V CHAIN_LENGTH TARGET_SUM)
      = CODE_SIZE := by
  rw [← Wots.countRow_eq_card CHAIN_LENGTH TARGET_SUM V TARGET_SUM (le_refl _)]
  -- About 66,000 additions of large numbers, which the kernel evaluates.
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
    Nat.card {x : Vector (Fin CHAIN_LENGTH) V // Internal.digitSum x = TARGET_SUM}
      = CODE_SIZE := by
  -- A vector is a function from positions to digits.
  let e : {x : Vector (Fin CHAIN_LENGTH) V // Internal.digitSum x = TARGET_SUM}
      ≃ Wots.DigitStrings V CHAIN_LENGTH TARGET_SUM :=
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

/-- One trial lands in the code with probability `2^-20.0045`, between `2^-21` and `2^-20`. -/
theorem code_probability :
    (1 : ℚ) / 2 ^ 21 ≤ (CODE_SIZE : ℚ) / 2 ^ 128 ∧ (CODE_SIZE : ℚ) / 2 ^ 128 ≤ 1 / 2 ^ 20 := by
  rw [CODE_SIZE]
  constructor <;> norm_num

end EthLib.Cryptography.Xmss
