module

public import EthLib.Execution.Evm.Precompiles.Modexp.Gas

/-!
# Proofs: `Gas`

What the gas formula guarantees.

- The iteration count is at least 1, at every fork.
- It follows the case split of EIP-198 for the exponent, at every fork.
- That includes the case where the literal EIP-7883 pseudocode reads differently.
- From Fusaka, the price is never below the minimum, 500.
- From Fusaka, the price does not fall when an operand grows longer.
- From Fusaka, for lengths in bounds, the price is at most 528449536.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Modexp

open EthLib.Base (Fork)
open EthLib.Execution.Evm.Precompiles.Modexp.Constants

/-- The iteration count is at least 1. -/
theorem one_le_iterations (fork : Fork) (expLen expHead : Nat) :
    1 ≤ iterations fork expLen expHead := by
  exact Nat.le_max_right _ _

/-- A short exponent, of at most 32 bytes, equal to zero is charged one iteration.

EIP-198: "If `length_of_EXPONENT <= 32`, and all bits in `EXPONENT` are 0, return 0".

The count is then raised to 1. -/
theorem iterations_short_zero (fork : Fork) {expLen : Nat} (h : expLen ≤ EXPONENT_HEAD_BYTES) :
    iterations fork expLen 0 = 1 := by
  simp [iterations, h]

/-- A short exponent is charged the index of its highest set bit, at least 1.

EIP-198: "return the index of the highest bit in `EXPONENT`". -/
theorem iterations_short (fork : Fork) {expLen : Nat} (expHead : Nat)
    (h : expLen ≤ EXPONENT_HEAD_BYTES) :
    iterations fork expLen expHead = max (Nat.log2 expHead) 1 := by
  simp [iterations, h]

/-- From Fusaka, a long exponent costs 16 per byte beyond 32, plus the top bit of its head.

EIP-7883 scales the 8 of EIP-198 to 16. -/
theorem iterations_long {fork : Fork} (hfork : fork ≥ .fusaka) {expLen : Nat} (expHead : Nat)
    (h : EXPONENT_HEAD_BYTES < expLen) :
    iterations fork expLen expHead
      = ITERATIONS_PER_EXTRA_EXPONENT_BYTE * (expLen - EXPONENT_HEAD_BYTES) + Nat.log2 expHead := by
  have h1 : ¬ expLen ≤ EXPONENT_HEAD_BYTES := Nat.not_le.mpr h
  have h2 : 1 ≤ ITERATIONS_PER_EXTRA_EXPONENT_BYTE * (expLen - EXPONENT_HEAD_BYTES) := by
    have : 0 < expLen - EXPONENT_HEAD_BYTES := Nat.sub_pos_of_lt h
    unfold ITERATIONS_PER_EXTRA_EXPONENT_BYTE
    omega
  simp only [iterations, ite_eq_right h1, hfork, ite_true]
  exact Nat.max_eq_left (by omega)

/-- From Fusaka, a long exponent with a zero head is charged exactly 16 per byte beyond 32.

EIP-198 says to return exactly `8 * (length_of_EXPONENT - 32)` here.
EIP-7883 scales that 8 to 16.
Read literally, the EIP-7883 pseudocode would charge one iteration less.

It adds `(0).bit_length() - 1 = -1` for the zero head. -/
theorem iterations_long_zero_head {fork : Fork} (hfork : fork ≥ .fusaka) {expLen : Nat}
    (h : EXPONENT_HEAD_BYTES < expLen) :
    iterations fork expLen 0
      = ITERATIONS_PER_EXTRA_EXPONENT_BYTE * (expLen - EXPONENT_HEAD_BYTES) := by
  rw [iterations_long hfork 0 h]
  simp

/-- From Fusaka, the price is never below the minimum. -/
theorem min_gas_le_gasCost {fork : Fork} (hfork : fork ≥ .fusaka)
    (baseLen modLen expLen expHead : Nat) :
    MIN_GAS ≤ gasCost fork baseLen modLen expLen expHead := by
  simp only [gasCost, hfork, ite_true]
  exact Nat.le_max_left _ _

/-- From Fusaka, a longer base does not lower the complexity. -/
theorem complexity_mono_base {fork : Fork} (hfork : fork ≥ .fusaka) {b b' : Nat} (m : Nat)
    (h : b ≤ b') : complexity fork b m ≤ complexity fork b' m := by
  unfold complexity WORD_BYTES SMALL_LENGTH_BYTES MIN_COMPLEXITY
  simp only [hfork, ite_true]
  by_cases h1 : max b m > 32 <;> by_cases h2 : max b' m > 32
  · rw [ite_eq_left h1, ite_eq_left h2]
    -- Both operands are long: the word counts compare, and so do their squares.
    have : (max b m + 8 - 1) / 8 ≤ (max b' m + 8 - 1) / 8 := by omega
    exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left this 2)
  · -- A longer base cannot be short when the shorter one is long.
    omega
  · rw [ite_eq_right h1, ite_eq_left h2]
    -- The short side is 16.
    -- A long operand has at least 5 words, so its complexity is at least 50.
    have : 5 ≤ (max b' m + 8 - 1) / 8 := by omega
    have : 5 ^ 2 ≤ ((max b' m + 8 - 1) / 8) ^ 2 := Nat.pow_le_pow_left this 2
    omega
  · rw [ite_eq_right h1, ite_eq_right h2]
    -- Both operands are short: both cost 16.
    exact Nat.le_refl _

/-- From Fusaka, a longer modulus does not lower the complexity. -/
theorem complexity_mono_modulus {fork : Fork} (hfork : fork ≥ .fusaka) (b : Nat) {m m' : Nat}
    (h : m ≤ m') : complexity fork b m ≤ complexity fork b m' := by
  -- The complexity is symmetric, so swap the two lengths and reuse the base case.
  have e : ∀ x y, complexity fork x y = complexity fork y x := by
    intro x y
    simp [complexity, Nat.max_comm]
  rw [e b m, e b m']
  exact complexity_mono_base hfork b h

/-- A longer exponent does not lower the iteration count, for the same head, at every fork. -/
theorem iterations_mono (fork : Fork) {l l' : Nat} (expHead : Nat) (h : l ≤ l') :
    iterations fork l expHead ≤ iterations fork l' expHead := by
  unfold iterations ITERATIONS_PER_EXTRA_EXPONENT_BYTE EXPONENT_HEAD_BYTES
  by_cases hf : fork ≥ .fusaka <;> simp only [hf, ↓reduceIte] <;> split <;> split <;> omega

/-- From Fusaka, the price does not fall when the base grows longer. -/
theorem gasCost_mono_base {fork : Fork} (hfork : fork ≥ .fusaka) {b b' : Nat} (m e h : Nat)
    (hb : b ≤ b') : gasCost fork b m e h ≤ gasCost fork b' m e h := by
  simp only [gasCost, hfork, ite_true]
  exact Nat.max_le.mpr ⟨Nat.le_max_left _ _,
    Nat.le_trans (Nat.mul_le_mul_right _ (complexity_mono_base hfork m hb))
      (Nat.le_max_right _ _)⟩

/-- From Fusaka, the price does not fall when the modulus grows longer. -/
theorem gasCost_mono_modulus {fork : Fork} (hfork : fork ≥ .fusaka) (b : Nat) {m m' : Nat}
    (e h : Nat) (hm : m ≤ m') : gasCost fork b m e h ≤ gasCost fork b m' e h := by
  simp only [gasCost, hfork, ite_true]
  exact Nat.max_le.mpr ⟨Nat.le_max_left _ _,
    Nat.le_trans (Nat.mul_le_mul_right _ (complexity_mono_modulus hfork b hm))
      (Nat.le_max_right _ _)⟩

/-- From Fusaka, the price does not fall when the exponent grows longer, for the same head. -/
theorem gasCost_mono_exponent {fork : Fork} (hfork : fork ≥ .fusaka) (b m : Nat) {l l' : Nat}
    (h : Nat) (hl : l ≤ l') : gasCost fork b m l h ≤ gasCost fork b m l' h := by
  simp only [gasCost, hfork, ite_true]
  exact Nat.max_le.mpr ⟨Nat.le_max_left _ _,
    Nat.le_trans (Nat.mul_le_mul_left _ (iterations_mono fork h hl)) (Nat.le_max_right _ _)⟩

/-- From Fusaka, for lengths in bounds, the price is at most 528449536.

```text
    complexity  <= 2 * (1024 / 8)^2              = 32768
    iterations  <= 16 * (1024 - 32) + 255        = 16127
    price       <= 32768 * 16127                 = 528449536
```

The head holds 32 bytes, so its highest set bit has index at most 255. -/
theorem gasCost_le {fork : Fork} (hfork : fork ≥ .fusaka) {b m e h : Nat}
    (hb : b ≤ MAX_LENGTH_BYTES) (hm : m ≤ MAX_LENGTH_BYTES) (he : e ≤ MAX_LENGTH_BYTES)
    (hh : h < 2 ^ 256) : gasCost fork b m e h ≤ 528449536 := by
  unfold MAX_LENGTH_BYTES at hb hm he
  -- The complexity is largest at the longest lengths.
  have hc : complexity fork b m ≤ 32768 :=
    calc complexity fork b m ≤ complexity fork 1024 m := complexity_mono_base hfork m hb
      _ ≤ complexity fork 1024 1024 := complexity_mono_modulus hfork 1024 hm
      _ = 32768 := by simp [complexity, hfork, WORD_BYTES, SMALL_LENGTH_BYTES]
  -- The head has at most 256 bits, so the index of its highest bit is at most 255.
  have hlog : Nat.log2 h ≤ 255 := by
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · simp [h0]
    · exact Nat.le_of_lt_succ ((Nat.log2_lt (Nat.pos_iff_ne_zero.mp hpos)).mpr hh)
  -- The iteration count is largest at the longest exponent.
  have hi : iterations fork e h ≤ 16127 :=
    calc iterations fork e h ≤ iterations fork 1024 h := iterations_mono fork h he
      _ = ITERATIONS_PER_EXTRA_EXPONENT_BYTE * (1024 - EXPONENT_HEAD_BYTES) + Nat.log2 h :=
          iterations_long hfork h (by decide)
      _ ≤ 16127 := by unfold ITERATIONS_PER_EXTRA_EXPONENT_BYTE EXPONENT_HEAD_BYTES; omega
  simp only [gasCost, hfork, ite_true, MIN_GAS]
  exact Nat.max_le.mpr ⟨by decide, Nat.mul_le_mul hc hi⟩

/-- Before Berlin, the price is the one of EIP-198: complexity times iterations, over 20. -/
theorem gasCost_of_lt_berlin {fork : Fork} (h : fork < .berlin) (b m e head : Nat) :
    gasCost fork b m e head = complexity fork b m * iterations fork e head / 20 := by
  have hb : ¬fork ≥ .berlin := Nat.not_le.mpr h
  have hf : ¬fork ≥ .fusaka := fun hf => hb (Nat.le_trans (by decide) hf)
  simp [gasCost, hb, hf]

/-- From Berlin to Prague, the price is the one of EIP-2565.

It is the square of the words of the longer operand, times the iterations, over 3, at least 200. -/
theorem gasCost_of_berlin_le {fork : Fork} (h : fork ≥ .berlin) (before : fork < .fusaka)
    (b m e head : Nat) :
    gasCost fork b m e head =
      max 200 (((max b m + 7) / 8) ^ 2 * iterations fork e head / 3) := by
  have hf : ¬fork ≥ .fusaka := Nat.not_le.mpr before
  simp [gasCost, complexity, h, hf, WORD_BYTES]

end EthLib.Execution.Evm.Precompiles.Modexp
