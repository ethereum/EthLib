module

public import EthLib.Base.Proofs.Bytes
public import EthLib.Execution.Evm.Machine.Memory
public import EthLib.Execution.Proofs.Evm.Gas.Memory

/-!
# Proofs: `Evm.Machine.Memory`

- A read gives exactly the bytes asked for.
- A read of memory after a write of the same range gives the written bytes, and the size stays.
- Memory grows in whole words, so its size stays a multiple of 32.
- A write within memory sets each byte of its range and keeps every other byte.
- Growth keeps every byte, and a read gives the bytes of its range.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (U256 byteAt byteAt_append byteAt_append_zeros byteAt_extract byteAt_of_size_le)

/-- A read has exactly the `size` bytes asked for. -/
theorem bufferRead_length (data : ByteArray) (start size : Nat) :
    (bufferRead data start size).length = size := by
  simp [bufferRead]

/-- A write within memory keeps its size. -/
theorem size_memoryWrite {memory value : ByteArray} {start : Nat}
    (h : start + value.size ≤ memory.size) :
    (memoryWrite memory start value).size = memory.size := by
  unfold memoryWrite
  split
  · rfl
  · simp only [ByteArray.size_append, ByteArray.size_extract]
    omega

/-- A write keeps the size of memory when its value is empty or fits within memory. -/
theorem size_memoryWrite_of_fit {memory value : ByteArray} {start : Nat}
    (h : value.size ≠ 0 → start + value.size ≤ memory.size) :
    (memoryWrite memory start value).size = memory.size := by
  by_cases hz : value.size = 0
  · simp [memoryWrite, hz]
  · exact size_memoryWrite (h hz)

/-- A read within memory gives as many bytes as it asks for. -/
theorem size_memoryReadBytes {memory : ByteArray} {start size : Nat}
    (h : start + size ≤ memory.size) : (memoryReadBytes memory start size).size = size := by
  unfold memoryReadBytes
  split
  · simp_all
  · simp only [ByteArray.size_extract]
    omega

/-- A read of the range that a write covers gives the written bytes. -/
theorem memoryReadBytes_memoryWrite {memory value : ByteArray} {start : Nat}
    (h : start + value.size ≤ memory.size) :
    memoryReadBytes (memoryWrite memory start value) start value.size = value := by
  unfold memoryReadBytes memoryWrite
  split
  · rename_i empty
    exact (ByteArray.size_eq_zero_iff.mp empty).symm
  have prefix_size : (memory.extract 0 start).size = start := by
    simp only [ByteArray.size_extract]
    omega
  -- Skip the prefix of `start` bytes, then take the value from the front of the rest.
  have skip := ByteArray.extract_append_size_add' (i := 0) (j := value.size)
    (b := value ++ memory.extract (start + value.size) memory.size) prefix_size.symm
  rw [Nat.add_zero] at skip
  rw [ByteArray.append_assoc, skip, ByteArray.extract_append_eq_left rfl]

/-- Growth by `n` bytes adds `n` to the size. -/
theorem size_memoryExtend (memory : ByteArray) (n : Nat) :
    (memoryExtend memory n).size = memory.size + n := by
  rw [memoryExtend, ByteArray.size_append]
  simp only [← ByteArray.size_data, Array.size_replicate]

/-- The growth for a list of ranges ends on a multiple of 32. -/
theorem ceil32_add_expandBy_mod (currentSize : Nat) (extensions : List (U256 × U256)) :
    (ceil32 currentSize + (extendMemory currentSize extensions).expandBy) % 32 = 0 := by
  induction extensions generalizing currentSize with
  | nil => simpa [extendMemory] using ceil32_mod currentSize
  | cons p extensions ih =>
    obtain ⟨start, size⟩ := p
    unfold extendMemory
    split
    · exact ih currentSize
    · simp only
      split
      · exact ih currentSize
      · rename_i grows
        simp only
        -- The rest grows from the rounded end of the range, which is a multiple of 32.
        have rest := ih (ceil32 (start.toNat + size.toNat))
        rw [ceil32_of_mod (ceil32_mod _)] at rest
        omega

/-- Memory whose size is a multiple of 32 keeps that property when it grows for a list of ranges. -/
theorem size_memoryExtend_mod {memory : ByteArray} (h : memory.size % 32 = 0)
    (extensions : List (U256 × U256)) :
    (memoryExtend memory (extendMemory memory.size extensions).expandBy).size % 32 = 0 := by
  have := ceil32_add_expandBy_mod memory.size extensions
  rw [ceil32_of_mod h] at this
  rwa [size_memoryExtend]

/-! ## The bytes of memory -/

/-- A write within memory sets each byte of its range to the byte of the value.

It keeps every other byte. -/
theorem byteAt_memoryWrite {memory value : ByteArray} {start : Nat}
    (h : start + value.size ≤ memory.size) (i : Nat) :
    byteAt (memoryWrite memory start value) i =
      if start ≤ i ∧ i < start + value.size then byteAt value (i - start)
      else byteAt memory i := by
  unfold memoryWrite
  split
  · rw [ite_eq_right_iff.mpr (fun hc => absurd hc (by omega))]
  · have hp : (memory.extract 0 start).size = start := by simp; omega
    rw [byteAt_append, ByteArray.size_append, hp, byteAt_append, hp, byteAt_extract,
      byteAt_extract]
    by_cases h1 : i < start
    · simp [h1, show i < start + value.size by omega, show i < min start memory.size by omega,
        Nat.not_le.mpr h1]
    by_cases h2 : i < start + value.size
    · simp [h1, h2, show start ≤ i by omega]
    rw [ite_eq_right_of_eq_false _ _ (eq_false h2),
      ite_eq_right_of_eq_false _ _ (eq_false (show ¬(start ≤ i ∧ i < start + value.size) from
        fun hc => h2 hc.2)), Nat.min_self,
      show start + value.size + (i - (start + value.size)) = i by omega]
    split
    · rfl
    · exact (byteAt_of_size_le (by omega)).symm

/-- Growth keeps every byte of memory. -/
theorem byteAt_memoryExtend (memory : ByteArray) (n i : Nat) :
    byteAt (memoryExtend memory n) i = byteAt memory i :=
  byteAt_append_zeros memory n i

/-- A read within memory gives the bytes of memory from its start, and zero past its size. -/
theorem byteAt_memoryReadBytes {memory : ByteArray} {start size : Nat}
    (h : start + size ≤ memory.size) (i : Nat) :
    byteAt (memoryReadBytes memory start size) i =
      if i < size then byteAt memory (start + i) else 0 := by
  unfold memoryReadBytes
  split
  · rw [ite_eq_right_iff.mpr (fun hi => absurd hi (by omega))]
    exact byteAt_of_size_le (by simp)
  · rw [byteAt_extract, Nat.min_eq_left h]
    split <;> split <;> first | rfl | omega

/-- A buffer of a read holds the bytes of the read, and zero past its size. -/
theorem byteAt_bufferRead (data : ByteArray) (offset size j : Nat) :
    byteAt ⟨(bufferRead data offset size).toArray⟩ j =
      if j < size then byteAt data (offset + j) else 0 := by
  unfold byteAt
  by_cases hj : j < size
  · have hlen : j < (bufferRead data offset size).toArray.size := by simp [bufferRead_length, hj]
    rw [dite_eq_left_of_eq_true (eq_true (by simpa [ByteArray.size] using hlen)),
      ite_eq_left_of_eq_true _ _ (eq_true hj), ByteArray.getElem_eq_getElem_data]
    simp [bufferRead, byteAt]
  · rw [dite_eq_right_of_eq_false
      (eq_false (by simpa [ByteArray.size, bufferRead_length] using hj)),
      ite_eq_right_of_eq_false _ _ (eq_false hj)]

end EthLib.Execution.Evm
