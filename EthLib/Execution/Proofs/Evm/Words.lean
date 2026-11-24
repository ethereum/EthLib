module

public import EthLib.Execution.Evm.Words

/-!
# Proofs: `Evm.Words`

- `ceil32` is the least multiple of 32 at or above its argument.
- The word count is `ceil(size / 32)`: the least number of words that cover the bytes.
- A price per word grows with the size, and is at most its value at any covering word count.
-/

@[expose] public section

namespace EthLib.Execution.Evm

/-- `ceil32` is a multiple of 32. -/
theorem ceil32_mod (value : Nat) : ceil32 value % 32 = 0 := by
  unfold ceil32 WORD_BYTES
  split <;> omega

/-- `ceil32` is at least its argument. -/
theorem le_ceil32 (value : Nat) : value ≤ ceil32 value := by
  unfold ceil32 WORD_BYTES
  split <;> omega

/-- `ceil32` is at most any multiple of 32 at or above its argument. -/
theorem ceil32_le {value bound : Nat} (multiple : bound % 32 = 0) (above : value ≤ bound) :
    ceil32 value ≤ bound := by
  unfold ceil32 WORD_BYTES
  split <;> omega

/-- The words cover the bytes. -/
theorem le_wordCount (size : Nat) : size ≤ 32 * wordCount size := by
  have := ceil32_mod size
  have := le_ceil32 size
  unfold wordCount WORD_BYTES
  omega

/-- No fewer words cover the bytes. -/
theorem wordCount_le {size words : Nat} (covers : size ≤ 32 * words) : wordCount size ≤ words := by
  have := ceil32_le (value := size) (bound := 32 * words) (by omega) covers
  unfold wordCount WORD_BYTES
  omega

/-- The word count in closed form: `ceil(size / 32)`. -/
theorem wordCount_eq (size : Nat) : wordCount size = (size + 31) / 32 := by
  -- Both sides are the least `w` with `size ≤ 32 * w`.
  have covers := le_wordCount size
  have least := wordCount_le (size := size) (words := (size + 31) / 32) (by omega)
  omega

/-- A multiple of 32 is already rounded. -/
theorem ceil32_of_mod {value : Nat} (h : value % 32 = 0) : ceil32 value = value := by
  unfold ceil32 WORD_BYTES
  simp [h]

/-- More bytes need no fewer words. -/
theorem wordCount_mono {a b : Nat} (h : a ≤ b) : wordCount a ≤ wordCount b := by
  rw [wordCount_eq, wordCount_eq]
  omega

/-- Rounding up to whole words does not change the word count. -/
theorem wordCount_ceil32 (size : Nat) : wordCount (ceil32 size) = wordCount size := by
  rw [wordCount_eq, wordCount_eq]
  unfold ceil32 WORD_BYTES
  split <;> omega

/-- The word price in closed form, `base + perWord * ceil(size / 32)`. -/
theorem wordPrice_eq (base perWord size : Nat) :
    wordPrice base perWord size = base + perWord * ((size + 31) / 32) := by
  rw [wordPrice, wordCount_eq]

/-- More bytes never cost less. -/
theorem wordPrice_mono (base perWord : Nat) {short long : Nat} (le : short ≤ long) :
    wordPrice base perWord short ≤ wordPrice base perWord long :=
  Nat.add_le_add_left (Nat.mul_le_mul_left _ (wordCount_mono le)) _

/-- Bytes that fit in `words` words cost at most `base + perWord * words`. -/
theorem wordPrice_le (base perWord : Nat) {size words : Nat} (covers : size ≤ 32 * words) :
    wordPrice base perWord size ≤ base + perWord * words :=
  Nat.add_le_add_left (Nat.mul_le_mul_left _ (wordCount_le covers)) _

end EthLib.Execution.Evm
