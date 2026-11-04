module

public import EthLib.Execution.Evm.Gas
public import EthLib.Execution.Proofs.Evm.Words

/-!
# Proofs: `Evm.Gas`

The price of memory is `3 * w + w * w / 512` for `w` words, and it grows with the size.

The growth of memory pays the price of the new size minus the price of the old size.

A range of size 0 never grows memory, and nothing is paid when no range grows it.

A gas budget `g` bounds the words of memory by `w * w ≤ 512 * g`.

A call passes on at most the gas it has, and at least 63 64ths of it.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (U256)
open GasCosts

/-- The price of memory in closed form, for `w` words. -/
theorem memoryGasCost_eq (sizeInBytes : Nat) :
    memoryGasCost sizeInBytes =
      3 * wordCount sizeInBytes + wordCount sizeInBytes * wordCount sizeInBytes / 512 := by
  simp [memoryGasCost, MEMORY_PER_WORD, Nat.pow_two, Nat.mul_comm]

/-- The price of memory grows with its size. -/
theorem memoryGasCost_mono {a b : Nat} (h : a ≤ b) : memoryGasCost a ≤ memoryGasCost b := by
  have hw := wordCount_mono h
  have := Nat.div_le_div_right (c := 512) (Nat.mul_le_mul hw hw)
  rw [memoryGasCost_eq, memoryGasCost_eq]
  omega

/-- Rounding up to whole words does not change the price. -/
theorem memoryGasCost_ceil32 (size : Nat) : memoryGasCost (ceil32 size) = memoryGasCost size := by
  simp only [memoryGasCost, wordCount_ceil32]

/-- A range of size 0 never grows memory. -/
theorem extendMemory_cons_zero (currentSize : Nat) (start : U256)
    (extensions : List (U256 × U256)) :
    extendMemory currentSize ((start, 0) :: extensions) = extendMemory currentSize extensions := by
  simp [extendMemory]

/-- Nothing grows and nothing is paid when every range has size 0 or ends in the rounded memory. -/
theorem extendMemory_eq_zero (currentSize : Nat) (extensions : List (U256 × U256))
    (h : ∀ p ∈ extensions, p.2 = 0 ∨ ceil32 (p.1.toNat + p.2.toNat) ≤ ceil32 currentSize) :
    extendMemory currentSize extensions = ⟨0, 0⟩ := by
  induction extensions with
  | nil => rfl
  | cons p extensions ih =>
    obtain ⟨start, size⟩ := p
    have hp := h (start, size) List.mem_cons_self
    have ih := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    simp only at hp
    unfold extendMemory
    split
    · exact ih
    · simp [hp.resolve_left ‹_›, ih]

/-- The growth pays the price of the new size minus the price of the old size.

The new size is the rounded old size plus the growth. -/
theorem extendMemory_cost (currentSize : Nat) (extensions : List (U256 × U256)) :
    (extendMemory currentSize extensions).cost =
      memoryGasCost (ceil32 currentSize + (extendMemory currentSize extensions).expandBy) -
        memoryGasCost currentSize := by
  induction extensions generalizing currentSize with
  | nil => simp [extendMemory, memoryGasCost_ceil32]
  | cons p extensions ih =>
    obtain ⟨start, size⟩ := p
    unfold extendMemory
    split
    · exact ih currentSize
    · simp only
      split
      · exact ih currentSize
      · rename_i grows
        simp only at ⊢ ih
        -- The rest starts from the rounded end of the range, which is already rounded.
        rw [ih, ceil32_of_mod (ceil32_mod _)]
        have old := memoryGasCost_ceil32 currentSize
        generalize ceil32 (start.toNat + size.toNat) = after at grows ⊢
        generalize (extendMemory after extensions).expandBy = rest
        have up := memoryGasCost_mono (Nat.le_of_lt (Nat.lt_of_not_le grows))
        have further := memoryGasCost_mono (Nat.le_add_right after rest)
        rw [show ceil32 currentSize + (after - ceil32 currentSize + rest) = after + rest by omega]
        omega

/-- A call passes on at most the gas it has. -/
theorem maxMessageCallGas_le (gas : Nat) : maxMessageCallGas gas ≤ gas := by
  unfold maxMessageCallGas
  omega

/-- A call passes on at least 63 64ths of the gas it has. -/
theorem maxMessageCallGas_ge (gas : Nat) : 63 * gas ≤ 64 * maxMessageCallGas gas := by
  unfold maxMessageCallGas
  omega

/-- A gas budget bounds the words of memory: `w * w ≤ 512 * g`. -/
theorem wordCount_mul_self_le {sizeInBytes gas : Nat} (h : memoryGasCost sizeInBytes ≤ gas) :
    wordCount sizeInBytes * wordCount sizeInBytes ≤ 512 * gas := by
  rw [memoryGasCost_eq] at h
  -- The remainder of the square over 512 is below 512, and 3 gas per word pays for it.
  have zero : wordCount sizeInBytes = 0 → wordCount sizeInBytes * wordCount sizeInBytes = 0 :=
    fun hw => by simp [hw]
  generalize wordCount sizeInBytes * wordCount sizeInBytes = square at h zero ⊢
  omega

/-- The price of init code as 2 times the length rounded up to whole words, over 32. -/
theorem initCodeCost_eq (initCodeLength : Nat) :
    initCodeCost initCodeLength = CODE_INIT_PER_WORD * ceil32 initCodeLength / 32 := by
  have := ceil32_mod initCodeLength
  unfold initCodeCost wordCount WORD_BYTES CODE_INIT_PER_WORD
  omega

/-- 32 bytes of memory cost 3 gas. -/
example : memoryGasCost 32 = 3 := by decide

/-- 1024 words cost `3 * 1024 + 1024 * 1024 / 512 = 5120` gas. -/
example : memoryGasCost (32 * 1024) = 5120 := by decide

/-- One word written to empty memory grows it by 32 bytes, for 3 gas. -/
example : extendMemory 0 [(0, 32)] = ⟨3, 32⟩ := by decide

/-- A range of 1 byte at 32 grows 32 bytes of memory to 64 bytes, for `6 - 3 = 3` gas. -/
example : extendMemory 32 [(32, 1)] = ⟨3, 32⟩ := by decide

end EthLib.Execution.Evm
