import Mathlib.Tactic.SplitIfs
import EthLib.Precompiles.Modexp.Gas

/-!
# Proofs: `Gas`

What the gas formula guarantees.

- The price is never below the minimum, 500.
- The iteration count is at least 1.
- It follows the case split of EIP-198 for the exponent.
- That includes the case where the literal EIP-7883 pseudocode reads differently.
- The price does not fall when the base, the modulus or the exponent grows longer.
- For lengths in bounds, the price is at most 528449536.

The known answers at the end are the worked examples of EIP-198 and EIP-7883.
-/

namespace EthLib.Precompiles.Modexp

open EthLib.Precompiles.Modexp.Constants

/-- The iteration count is at least 1. -/
theorem one_le_iterations (expLen expHead : Nat) : 1 ≤ iterations expLen expHead := by
  exact Nat.le_max_right _ _

/-- A short exponent, of at most 32 bytes, equal to zero is charged one iteration.

EIP-198: "If `length_of_EXPONENT <= 32`, and all bits in `EXPONENT` are 0, return 0".

The count is then raised to 1. -/
theorem iterations_short_zero {expLen : Nat} (h : expLen ≤ EXPONENT_HEAD_BYTES) :
    iterations expLen 0 = 1 := by
  simp [iterations, h]

/-- A short exponent is charged the index of its highest set bit, at least 1.

EIP-198: "return the index of the highest bit in `EXPONENT`". -/
theorem iterations_short {expLen : Nat} (expHead : Nat) (h : expLen ≤ EXPONENT_HEAD_BYTES) :
    iterations expLen expHead = max (Nat.log2 expHead) 1 := by
  simp [iterations, h]

/-- A long exponent is charged 16 per byte beyond 32, plus the highest set bit of its head.

EIP-7883 scales the 8 of EIP-198 to 16. -/
theorem iterations_long {expLen : Nat} (expHead : Nat) (h : EXPONENT_HEAD_BYTES < expLen) :
    iterations expLen expHead
      = ITERATIONS_PER_EXTRA_EXPONENT_BYTE * (expLen - EXPONENT_HEAD_BYTES) + Nat.log2 expHead := by
  have h1 : ¬ expLen ≤ EXPONENT_HEAD_BYTES := Nat.not_le.mpr h
  have h2 : 1 ≤ ITERATIONS_PER_EXTRA_EXPONENT_BYTE * (expLen - EXPONENT_HEAD_BYTES) := by
    have : 0 < expLen - EXPONENT_HEAD_BYTES := Nat.sub_pos_of_lt h
    unfold ITERATIONS_PER_EXTRA_EXPONENT_BYTE
    omega
  simp only [iterations, ite_eq_right h1]
  exact Nat.max_eq_left (by omega)

/-- A long exponent whose first 32 bytes are zero is charged exactly 16 per byte beyond 32.

EIP-198 says to return exactly `8 * (length_of_EXPONENT - 32)` here.
EIP-7883 scales that 8 to 16.
Read literally, the EIP-7883 pseudocode would charge one iteration less.

It adds `(0).bit_length() - 1 = -1` for the zero head. -/
theorem iterations_long_zero_head {expLen : Nat} (h : EXPONENT_HEAD_BYTES < expLen) :
    iterations expLen 0
      = ITERATIONS_PER_EXTRA_EXPONENT_BYTE * (expLen - EXPONENT_HEAD_BYTES) := by
  rw [iterations_long 0 h]
  simp

/-- The price is never below the minimum. -/
theorem min_gas_le_gasCost (baseLen modLen expLen expHead : Nat) :
    MIN_GAS ≤ gasCost baseLen modLen expLen expHead :=
  Nat.le_max_left _ _

/-- A longer base does not lower the complexity. -/
theorem complexity_mono_base {b b' : Nat} (m : Nat) (h : b ≤ b') :
    complexity b m ≤ complexity b' m := by
  unfold complexity WORD_BYTES SMALL_LENGTH_BYTES MIN_COMPLEXITY
  simp only
  split_ifs with h1 h2 h2
  · -- Both operands are long: the word counts compare, and so do their squares.
    have : (max b m + 8 - 1) / 8 ≤ (max b' m + 8 - 1) / 8 := by omega
    exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left this 2)
  · -- A longer base cannot be short when the shorter one is long.
    omega
  · -- The short side is 16.
    -- A long operand has at least 5 words, so its complexity is at least 50.
    have : 5 ≤ (max b' m + 8 - 1) / 8 := by omega
    have : 5 ^ 2 ≤ ((max b' m + 8 - 1) / 8) ^ 2 := Nat.pow_le_pow_left this 2
    omega
  · -- Both operands are short: both cost 16.
    exact Nat.le_refl _

/-- A longer modulus does not lower the complexity. -/
theorem complexity_mono_modulus (b : Nat) {m m' : Nat} (h : m ≤ m') :
    complexity b m ≤ complexity b m' := by
  -- The complexity is symmetric, so swap the two lengths and reuse the base case.
  have e : ∀ x y, complexity x y = complexity y x := by
    intro x y
    simp [complexity, Nat.max_comm]
  rw [e b m, e b m']
  exact complexity_mono_base b h

/-- A longer exponent does not lower the iteration count, for the same head. -/
theorem iterations_mono {l l' : Nat} (expHead : Nat) (h : l ≤ l') :
    iterations l expHead ≤ iterations l' expHead := by
  unfold iterations ITERATIONS_PER_EXTRA_EXPONENT_BYTE EXPONENT_HEAD_BYTES
  simp only
  split_ifs <;> omega

/-- The price does not fall when the base grows longer. -/
theorem gasCost_mono_base {b b' : Nat} (m e h : Nat) (hb : b ≤ b') :
    gasCost b m e h ≤ gasCost b' m e h := by
  unfold gasCost
  exact Nat.max_le.mpr ⟨Nat.le_max_left _ _,
    Nat.le_trans (Nat.mul_le_mul_right _ (complexity_mono_base m hb)) (Nat.le_max_right _ _)⟩

/-- The price does not fall when the modulus grows longer. -/
theorem gasCost_mono_modulus (b : Nat) {m m' : Nat} (e h : Nat) (hm : m ≤ m') :
    gasCost b m e h ≤ gasCost b m' e h := by
  unfold gasCost
  exact Nat.max_le.mpr ⟨Nat.le_max_left _ _,
    Nat.le_trans (Nat.mul_le_mul_right _ (complexity_mono_modulus b hm)) (Nat.le_max_right _ _)⟩

/-- The price does not fall when the exponent grows longer, for the same head. -/
theorem gasCost_mono_exponent (b m : Nat) {l l' : Nat} (h : Nat) (hl : l ≤ l') :
    gasCost b m l h ≤ gasCost b m l' h := by
  unfold gasCost
  exact Nat.max_le.mpr ⟨Nat.le_max_left _ _,
    Nat.le_trans (Nat.mul_le_mul_left _ (iterations_mono h hl)) (Nat.le_max_right _ _)⟩

/-- For lengths in bounds, the price is at most 528449536.

```text
    complexity  <= 2 * (1024 / 8)^2              = 32768
    iterations  <= 16 * (1024 - 32) + 255        = 16127
    price       <= 32768 * 16127                 = 528449536
```

The head holds 32 bytes, so its highest set bit has index at most 255. -/
theorem gasCost_le {b m e h : Nat} (hb : b ≤ MAX_LENGTH_BYTES) (hm : m ≤ MAX_LENGTH_BYTES)
    (he : e ≤ MAX_LENGTH_BYTES) (hh : h < 2 ^ 256) :
    gasCost b m e h ≤ 528449536 := by
  unfold MAX_LENGTH_BYTES at hb hm he
  -- The complexity is largest at the longest lengths.
  have hc : complexity b m ≤ 32768 :=
    calc complexity b m ≤ complexity 1024 m := complexity_mono_base m hb
      _ ≤ complexity 1024 1024 := complexity_mono_modulus 1024 hm
      _ = 32768 := by decide
  -- The head has at most 256 bits, so the index of its highest bit is at most 255.
  have hlog : Nat.log2 h ≤ 255 := by
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · simp [h0]
    · exact Nat.le_of_lt_succ ((Nat.log2_lt (Nat.pos_iff_ne_zero.mp hpos)).mpr hh)
  -- The iteration count is largest at the longest exponent.
  have hi : iterations e h ≤ 16127 :=
    calc iterations e h ≤ iterations 1024 h := iterations_mono h he
      _ = ITERATIONS_PER_EXTRA_EXPONENT_BYTE * (1024 - EXPONENT_HEAD_BYTES) + Nat.log2 h :=
          iterations_long h (by decide)
      _ ≤ 16127 := by unfold ITERATIONS_PER_EXTRA_EXPONENT_BYTE EXPONENT_HEAD_BYTES; omega
  unfold gasCost MIN_GAS
  exact Nat.max_le.mpr ⟨by decide, Nat.mul_le_mul hc hi⟩

/-! ## Known answers

EIP-198 lists the index of the highest bit for five short exponents:
"eg. 1 -> 0, 2 -> 1, 3 -> 1, 255 -> 7, 256 -> 8".

The count is then raised to at least 1. -/

example : iterations 1 1 = 1 := by decide +kernel
example : iterations 1 2 = 1 := by decide +kernel
example : iterations 1 3 = 1 := by decide +kernel
example : iterations 1 255 = 7 := by decide +kernel
example : iterations 2 256 = 8 := by decide +kernel

/-! The `modexp_nagydani_*` calls of the EIP-7883 table.
The exponent is `2` (square), `3` (qube) or `0x10001`.
The base and the modulus have the same length.
The exponent has 1 byte, or 3 bytes for `0x10001`.

The prices are the column "EIP-7883 Pricing" of EIP-7883, Test Cases.
The lengths are in the inputs of `vectors.json`, in
`tests/osaka/eip7883_modexp_gas_increase/vector/` of execution-specs at `2c0c8e7`. -/

-- `modexp_nagydani_1_square` and `_qube`: 64-byte operands.
-- `decide` runs in the elaborator, and the kernel rechecks the proof it builds.
example : gasCost 64 64 1 2 = 500 := by decide
example : gasCost 64 64 1 3 = 500 := by decide
-- `modexp_nagydani_1_pow0x10001`
example : gasCost 64 64 3 0x10001 = 2048 := by decide
-- `modexp_nagydani_2_*`: 128-byte operands.
example : gasCost 128 128 1 2 = 512 := by decide
example : gasCost 128 128 1 3 = 512 := by decide
example : gasCost 128 128 3 0x10001 = 8192 := by decide
-- `modexp_nagydani_3_*`: 256-byte operands.
example : gasCost 256 256 1 2 = 2048 := by decide
example : gasCost 256 256 1 3 = 2048 := by decide
example : gasCost 256 256 3 0x10001 = 32768 := by decide
-- `modexp_nagydani_4_*`: 512-byte operands.
example : gasCost 512 512 1 2 = 8192 := by decide
example : gasCost 512 512 1 3 = 8192 := by decide
example : gasCost 512 512 3 0x10001 = 131072 := by decide
-- `modexp_nagydani_5_*`: 1024-byte operands.
example : gasCost 1024 1024 1 2 = 32768 := by decide
example : gasCost 1024 1024 1 3 = 32768 := by decide
example : gasCost 1024 1024 3 0x10001 = 524288 := by decide

end EthLib.Precompiles.Modexp
