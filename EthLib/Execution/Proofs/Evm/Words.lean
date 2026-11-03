module

public import EthLib.Execution.Evm.Words

/-!
# Proofs: `Evm.Words`

- `ceil32` is the least multiple of 32 at or above its argument.
- The word count is `ceil(size / 32)`: the least number of words that cover the bytes.
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

end EthLib.Execution.Evm
