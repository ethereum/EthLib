module

public import EthLib.Execution.Evm.Words

/-!
# Proofs: `Words`

`ceil32 value` is the least multiple of 32 that is at least `value`.
So `wordCount size` is the least number of 32-byte EVM words that covers `size` bytes, which is `ceil(size / 32)`.
-/

@[expose] public section

namespace EthLib.Execution.Evm

/-! ## `ceil32` -/

/-- `ceil32` is a multiple of 32. -/
theorem ceil32_mod (value : Nat) : ceil32 value % 32 = 0 := by
  unfold ceil32 WORD_BYTES
  split <;> omega

/-- `ceil32` is at least its argument. -/
theorem le_ceil32 (value : Nat) : value ≤ ceil32 value := by
  unfold ceil32 WORD_BYTES
  split <;> omega

/-- `ceil32` adds less than 32 to its argument. -/
theorem ceil32_lt (value : Nat) : ceil32 value < value + 32 := by
  unfold ceil32 WORD_BYTES
  split <;> omega

/-- `ceil32` is at most every multiple of 32 that is at least its argument. -/
theorem ceil32_le {value bound : Nat} (multiple : bound % 32 = 0) (above : value ≤ bound) :
    ceil32 value ≤ bound := by
  unfold ceil32 WORD_BYTES
  split <;> omega

/-- `ceil32` in closed form. -/
theorem ceil32_eq (value : Nat) : ceil32 value = 32 * ((value + 31) / 32) := by
  unfold ceil32 WORD_BYTES
  split <;> omega

/-! ## `wordCount` -/

/-- The EVM words cover the bytes. -/
theorem le_wordCount (size : Nat) : size ≤ 32 * wordCount size := by
  have := ceil32_mod size
  have := le_ceil32 size
  unfold wordCount WORD_BYTES
  omega

/-- No fewer EVM words cover the bytes. -/
theorem wordCount_le {size words : Nat} (covers : size ≤ 32 * words) : wordCount size ≤ words := by
  have := ceil32_le (value := size) (bound := 32 * words) (by omega) covers
  unfold wordCount WORD_BYTES
  omega

/-- The word count is at most `words` exactly when `words` EVM words cover the bytes. -/
theorem wordCount_le_iff (size words : Nat) : wordCount size ≤ words ↔ size ≤ 32 * words :=
  ⟨fun le => Nat.le_trans (le_wordCount size) (Nat.mul_le_mul_left 32 le), wordCount_le⟩

/-- The word count in closed form: `ceil(size / 32)`. -/
theorem wordCount_eq (size : Nat) : wordCount size = (size + 31) / 32 := by
  rw [wordCount, ceil32_eq, WORD_BYTES]
  omega

/-- More bytes never need fewer EVM words. -/
theorem wordCount_mono {short long : Nat} (le : short ≤ long) : wordCount short ≤ wordCount long := by
  rw [wordCount_eq, wordCount_eq]
  omega

/-- Zero bytes need no EVM word. -/
@[simp] theorem wordCount_zero : wordCount 0 = 0 := rfl

/-- `k` whole EVM words need exactly `k` EVM words. -/
theorem wordCount_mul (k : Nat) : wordCount (32 * k) = k := by
  rw [wordCount_eq]
  omega

/-- One byte past `k` whole EVM words starts EVM word `k + 1`. -/
theorem wordCount_mul_add_one (k : Nat) : wordCount (32 * k + 1) = k + 1 := by
  rw [wordCount_eq]
  omega

end EthLib.Execution.Evm
