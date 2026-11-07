module

public import EthLib.Execution.Proofs.Evm.Logic.Copy

/-!
# Proofs: ranges of memory that hold known bytes

A specification often cares about a few ranges of memory, not about every byte of it.

A range holds known bytes when memory covers the whole range and the range reads as those bytes.

- A write within memory holds what it writes.
- A write within memory keeps every range that it does not touch.
- Growth keeps every range.
- Two adjacent ranges that hold bytes hold their concatenation, and a range splits the same way.
- A range that holds the bytes of a word reads as that word.

Memory grows in whole words, up to the greatest end of a range that an instruction touches.

- A range within memory grows nothing and costs nothing.
- A range of no bytes grows nothing and costs nothing.
- A range of some bytes past memory grows it to the rounded end of the range.
- That growth needs a size of memory that is a multiple of 32.
- The growth costs the price of the new size minus the price of the old size.

So a specification can track only the size of memory and the ranges it cares about.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (U256 byteAt byteAt_of_size_le eq_of_byteAt)

/-- Memory covers the range of `bytes` from `start`, and the range reads as `bytes`. -/
def Holds (memory : ByteArray) (start : Nat) (bytes : ByteArray) : Prop :=
  start + bytes.size ≤ memory.size ∧ memoryReadBytes memory start bytes.size = bytes

/-- A whole memory holds itself from offset 0. -/
theorem holds_self (memory : ByteArray) : Holds memory 0 memory :=
  ⟨by omega, memoryReadBytes_whole⟩

/-- A write within memory holds the written bytes. -/
theorem holds_memoryWrite {memory value : ByteArray} {start : Nat}
    (h : start + value.size ≤ memory.size) : Holds (memoryWrite memory start value) start value :=
  ⟨by rw [size_memoryWrite h]; exact h, memoryReadBytes_memoryWrite h⟩

namespace Holds

variable {memory bytes : ByteArray} {start : Nat}

/-- A write within memory keeps a range that it does not touch. -/
theorem memoryWrite_of_disjoint (h : Holds memory start bytes) {value : ByteArray} {s : Nat}
    (hw : s + value.size ≤ memory.size)
    (hd : start + bytes.size ≤ s ∨ s + value.size ≤ start) :
    Holds (memoryWrite memory s value) start bytes :=
  ⟨by rw [size_memoryWrite hw]; exact h.1, by
    rw [memoryReadBytes_memoryWrite_of_disjoint hw hd]; exact h.2⟩

/-- Each byte of the range is the byte of `bytes`. -/
theorem byteAt_eq (h : Holds memory start bytes) {i : Nat} (hi : i < bytes.size) :
    byteAt memory (start + i) = byteAt bytes i := by
  have := byteAt_memoryReadBytes h.1 i
  rw [h.2, ite_eq_left hi] at this
  exact this.symm

/-- A range holds bytes when each of its bytes in memory is the byte of `bytes`. -/
theorem of_byteAt (fit : start + bytes.size ≤ memory.size)
    (h : ∀ i < bytes.size, byteAt memory (start + i) = byteAt bytes i) :
    Holds memory start bytes := by
  refine ⟨fit, eq_of_byteAt (size_memoryReadBytes fit) fun i => ?_⟩
  rw [byteAt_memoryReadBytes fit]
  split
  · exact h i ‹_›
  · exact (byteAt_of_size_le (by omega)).symm

/-- Growth keeps every range. -/
theorem memoryExtend (h : Holds memory start bytes) (n : Nat) :
    Holds (memoryExtend memory n) start bytes :=
  of_byteAt (by rw [size_memoryExtend]; have := h.1; omega) fun i hi => by
    rw [byteAt_memoryExtend]
    exact h.byteAt_eq hi

/-- Two adjacent ranges hold their bytes in order. -/
theorem append (h₁ : Holds memory start bytes) {more : ByteArray}
    (h₂ : Holds memory (start + bytes.size) more) : Holds memory start (bytes ++ more) := by
  refine of_byteAt (by rw [ByteArray.size_append]; have := h₂.1; omega) fun i hi => ?_
  rw [EthLib.Base.byteAt_append]
  split
  · exact h₁.byteAt_eq ‹_›
  · rw [ByteArray.size_append] at hi
    have := h₂.byteAt_eq (i := i - bytes.size) (by omega)
    rwa [show start + bytes.size + (i - bytes.size) = start + i by omega] at this

/-- A range that holds two blocks of bytes holds the first one from its start. -/
theorem left {more : ByteArray} (h : Holds memory start (bytes ++ more)) :
    Holds memory start bytes := by
  have fit := h.1
  rw [ByteArray.size_append] at fit
  refine of_byteAt (by omega) fun i hi => ?_
  rw [h.byteAt_eq (by rw [ByteArray.size_append]; omega), EthLib.Base.byteAt_append, ite_eq_left hi]

/-- A range that holds two blocks of bytes holds the second one after the first. -/
theorem right {more : ByteArray} (h : Holds memory start (bytes ++ more)) :
    Holds memory (start + bytes.size) more := by
  have fit := h.1
  rw [ByteArray.size_append] at fit
  refine of_byteAt (by omega) fun i hi => ?_
  have := h.byteAt_eq (i := bytes.size + i) (by rw [ByteArray.size_append]; omega)
  rw [EthLib.Base.byteAt_append, ite_eq_right (by omega), Nat.add_sub_cancel_left] at this
  rwa [Nat.add_assoc]

/-- A range that holds the bytes of a word reads as that word. -/
theorem loadWord {word : U256} (h : Holds memory start (wordBytes word)) :
    loadWord (memoryReadBytes memory start 32) 0 32 = word := by
  have hsize := size_wordBytes word
  have h2 := h.2
  rw [hsize] at h2
  have hw := loadWord_memoryWrite_wordBytes (memory := wordBytes word) (start := 0) word
    (by simp [size_wordBytes])
  rwa [memoryWrite_whole rfl, ← hsize, memoryReadBytes_whole, hsize, ← h2] at hw

end Holds

/-! ## The growth of memory -/

/-- A range within memory grows nothing and costs nothing. -/
theorem extendMemory_of_le {size : Nat} {start length : U256}
    (h : start.toNat + length.toNat ≤ size) : extendMemory size [(start, length)] = ⟨0, 0⟩ :=
  extendMemory_eq_zero size _ fun p hp => by
    rw [List.mem_singleton.mp hp]
    exact .inr (ceil32_le (ceil32_mod size) (Nat.le_trans h (le_ceil32 size)))

/-- A range of no bytes grows nothing and costs nothing. -/
theorem extendMemory_of_length_eq_zero (size : Nat) (start : U256) :
    extendMemory size [(start, 0)] = ⟨0, 0⟩ :=
  extendMemory_cons_zero size start []

/-- A range of some bytes past memory grows it to the rounded end of the range.

The size of memory must be a multiple of 32.

The growth costs the price of the new size minus the price of the old size. -/
theorem extendMemory_of_lt {size : Nat} {start length : U256} (hmod : size % 32 = 0)
    (hz : length ≠ 0) (h : size < start.toNat + length.toNat) :
    extendMemory size [(start, length)] =
      ⟨memoryGasCost (ceil32 (start.toNat + length.toNat)) - memoryGasCost size,
        ceil32 (start.toNat + length.toNat) - size⟩ := by
  have hup := le_ceil32 (start.toNat + length.toNat)
  have hz' : ¬length = 0#256 := hz
  have grows : ¬ceil32 (start.toNat + length.toNat) ≤ size := by omega
  simp [extendMemory, hz', ceil32_of_mod hmod, grows]

/-- The size of memory after the growth for a range, from a size that is a multiple of 32.

It is the greater of the old size and the rounded end of a range that is not empty. -/
theorem size_memoryExtend_extendMemory {memory : ByteArray} {start length : U256}
    (hmod : memory.size % 32 = 0) (hz : length ≠ 0) :
    (memoryExtend memory (extendMemory memory.size [(start, length)]).expandBy).size =
      max memory.size (ceil32 (start.toNat + length.toNat)) := by
  rw [size_memoryExtend]
  by_cases h : memory.size < start.toNat + length.toNat
  · rw [extendMemory_of_lt hmod hz h]
    have := le_ceil32 (start.toNat + length.toNat)
    simp only
    omega
  · rw [extendMemory_of_le (by omega)]
    have := ceil32_le hmod (Nat.le_of_not_lt h)
    simp only
    omega

end EthLib.Execution.Evm.Logic
