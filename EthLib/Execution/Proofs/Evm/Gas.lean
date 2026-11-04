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

From Berlin, an access to an account or a slot pays the cold or the warm price.

The token prices of EIP-7623 and the refund of EIP-3529 agree with the prices they derive from.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256)
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

/-- From Berlin, SLOAD pays the price of a cold or a warm access to the slot. -/
theorem sloadCost_of_berlin_le {fork : Fork} (h : fork ≥ .berlin) (cold : Bool) :
    sloadCost fork cold = if cold then COLD_STORAGE_ACCESS else WARM_ACCESS := by
  simp [sloadCost, h]

/-- From Berlin, BALANCE pays the price of a cold or a warm access to the account. -/
theorem balanceCost_of_berlin_le {fork : Fork} (h : fork ≥ .berlin) (cold : Bool) :
    balanceCost fork cold = accountAccessCost cold := by
  simp [balanceCost, h]

/-- From Berlin, EXTCODESIZE and EXTCODECOPY pay the price of a cold or a warm access. -/
theorem externalBaseCost_of_berlin_le {fork : Fork} (h : fork ≥ .berlin) (cold : Bool) :
    externalBaseCost fork cold = accountAccessCost cold := by
  simp [externalBaseCost, h]

/-- From Berlin, EXTCODEHASH pays the price of a cold or a warm access to the account. -/
theorem extcodehashCost_of_berlin_le {fork : Fork} (h : fork ≥ .berlin) (cold : Bool) :
    extcodehashCost fork cold = accountAccessCost cold := by
  simp [extcodehashCost, h]

/-- From Berlin, the calls pay the price of a cold or a warm access to the account. -/
theorem callBaseCost_of_berlin_le {fork : Fork} (h : fork ≥ .berlin) (cold : Bool) :
    callBaseCost fork cold = accountAccessCost cold := by
  simp [callBaseCost, h]

/-- From Istanbul, a byte of call data costs the standard price of its tokens.

A zero byte is one token, and a nonzero byte is four, so EIP-7623 keeps the price of EIP-2028. -/
theorem txData_of_istanbul_le {fork : Fork} (h : fork ≥ .istanbul) :
    TX_DATA_PER_ZERO = TX_DATA_TOKEN_STANDARD ∧
      (gasSchedule fork).TX_DATA_PER_NON_ZERO = 4 * TX_DATA_TOKEN_STANDARD := by
  simp [gasSchedule, h, TX_DATA_PER_ZERO, TX_DATA_TOKEN_STANDARD]

/-- From London, the refund to clear a slot is the reset price plus the price of a listed key.

EIP-3529 defines it so, with the reset price of EIP-2929, which excludes the cold access. -/
theorem refundStorageClear_of_london_le {fork : Fork} (h : fork ≥ .london) :
    (gasSchedule fork).REFUND_STORAGE_CLEAR =
      COLD_STORAGE_WRITE - COLD_STORAGE_ACCESS + TX_ACCESS_LIST_STORAGE_KEY := by
  simp [gasSchedule, h, COLD_STORAGE_WRITE, COLD_STORAGE_ACCESS, TX_ACCESS_LIST_STORAGE_KEY]

end EthLib.Execution.Evm
