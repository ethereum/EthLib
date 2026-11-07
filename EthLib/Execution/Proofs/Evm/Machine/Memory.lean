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
- Growth by no byte, and a write or a read of a whole memory from offset 0, give simple forms.
- A read of a range that a write does not touch gives the bytes before the write.
- A read across two adjacent writes gives the two values in order.
- A read that ends where a write ends gives the bytes before the write, then the value.
- Two writes to disjoint ranges commute.
- A read across two adjacent writes in either order gives the values in order.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (U256 byteAt byteAt_append byteAt_append_zeros byteAt_extract byteAt_of_size_le
  eq_of_byteAt)

/-- A read has exactly the `size` bytes asked for. -/
theorem bufferRead_length (data : ByteArray) (start size : Nat) :
    (bufferRead data start size).length = size := by
  simp [bufferRead]

/-- A read of a whole buffer from its start gives its bytes. -/
theorem bufferRead_zero_size (data : ByteArray) :
    bufferRead data 0 data.size = data.data.toList := by
  apply List.ext_getElem
  · simp [bufferRead]
  · intro i _ h
    have hi : i < data.data.size := by simpa using h
    simp [bufferRead, EthLib.Base.byteAt_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hi]

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

/-- Growth by no byte leaves memory as it is. -/
theorem memoryExtend_zero (memory : ByteArray) : memoryExtend memory 0 = memory := by
  apply eq_of_byteAt (by simp [size_memoryExtend])
  intro i
  exact byteAt_memoryExtend memory 0 i

/-- A write of a whole memory from offset 0 gives the written bytes. -/
theorem memoryWrite_whole {memory value : ByteArray} (h : memory.size = value.size) :
    memoryWrite memory 0 value = value := by
  have hs : (memoryWrite memory 0 value).size = value.size := by
    rw [size_memoryWrite (by omega)]
    omega
  apply eq_of_byteAt hs
  intro i
  rw [byteAt_memoryWrite (by omega)]
  split
  · simp
  · rename_i hi
    rw [Base.byteAt_of_size_le (by omega), Base.byteAt_of_size_le (by omega)]

/-- A write past the end of a memory, into bytes that it grew by, appends the written bytes. -/
theorem memoryWrite_extend_end {memory value : ByteArray} :
    memoryWrite (memoryExtend memory value.size) memory.size value = memory ++ value := by
  have hs : (memoryWrite (memoryExtend memory value.size) memory.size value).size =
      (memory ++ value).size := by
    rw [size_memoryWrite (by simp [size_memoryExtend])]
    simp [size_memoryExtend]
  apply eq_of_byteAt hs
  intro i
  rw [byteAt_memoryWrite (by simp [size_memoryExtend]), byteAt_append]
  split
  · rename_i hi
    rw [ite_eq_right (by omega)]
  · rename_i hi
    by_cases hlt : i < memory.size
    · rw [ite_eq_left hlt, byteAt_memoryExtend]
    · rw [ite_eq_right hlt]
      rw [Base.byteAt_of_size_le (by simp [size_memoryExtend]; omega),
        Base.byteAt_of_size_le (by omega)]

/-- A read of a whole memory from offset 0 gives the memory. -/
theorem memoryReadBytes_whole {memory : ByteArray} :
    memoryReadBytes memory 0 memory.size = memory := by
  apply eq_of_byteAt (by rw [size_memoryReadBytes (by omega)])
  intro i
  rw [byteAt_memoryReadBytes (by omega)]
  split
  · simp
  · rename_i hi
    rw [Base.byteAt_of_size_le (by omega)]

/-- A read of a range that a write within memory does not touch gives the bytes before the write.

The ranges are disjoint: the read ends before the write starts, or starts after it ends. -/
theorem memoryReadBytes_memoryWrite_of_disjoint {memory value : ByteArray} {start size s : Nat}
    (hw : s + value.size ≤ memory.size) (hd : start + size ≤ s ∨ s + value.size ≤ start) :
    memoryReadBytes (memoryWrite memory s value) start size =
      memoryReadBytes memory start size := by
  have hs : (memoryWrite memory s value).size = memory.size := size_memoryWrite hw
  unfold memoryReadBytes
  split
  · rfl
  apply eq_of_byteAt (by simp [hs])
  intro i
  rw [byteAt_extract, byteAt_extract, hs]
  split
  · rw [byteAt_memoryWrite hw, ite_eq_right (by omega)]
  · rfl

/-- A read across two adjacent writes within memory gives the two values in order. -/
theorem memoryReadBytes_memoryWrite_memoryWrite {memory a b : ByteArray} {s : Nat}
    (hw : s + a.size + b.size ≤ memory.size) :
    memoryReadBytes (memoryWrite (memoryWrite memory s a) (s + a.size) b) s (a.size + b.size) =
      a ++ b := by
  have h1 : (memoryWrite memory s a).size = memory.size := size_memoryWrite (by omega)
  have h2 : (memoryWrite (memoryWrite memory s a) (s + a.size) b).size = memory.size := by
    rw [size_memoryWrite (by omega), h1]
  apply eq_of_byteAt
  · rw [size_memoryReadBytes (by omega), ByteArray.size_append]
  intro i
  rw [byteAt_memoryReadBytes (by omega), byteAt_memoryWrite (by omega),
    byteAt_memoryWrite (by omega), byteAt_append]
  by_cases hi : i < a.size
  · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left hi]
    congr 1
    omega
  · by_cases hj : i < a.size + b.size
    · rw [ite_eq_left hj, ite_eq_left (by omega), ite_eq_right hi]
      congr 1
      omega
    · rw [ite_eq_right hj, ite_eq_right hi, byteAt_of_size_le (by omega)]

/-- A read from `k` bytes before a write to its end gives those bytes, then the value.

The write must lie within memory. -/
theorem memoryReadBytes_memoryWrite_eq_append {memory value : ByteArray} {s k : Nat}
    (hw : s + k + value.size ≤ memory.size) :
    memoryReadBytes (memoryWrite memory (s + k) value) s (k + value.size) =
      memoryReadBytes memory s k ++ value := by
  have hs : (memoryWrite memory (s + k) value).size = memory.size := size_memoryWrite hw
  apply eq_of_byteAt
  · rw [size_memoryReadBytes (by omega), ByteArray.size_append, size_memoryReadBytes (by omega)]
  · intro i
    rw [byteAt_memoryReadBytes (by omega), byteAt_memoryWrite hw, byteAt_append,
      size_memoryReadBytes (by omega)]
    by_cases hi : i < k
    · rw [ite_eq_left (by omega), ite_eq_left hi, byteAt_memoryReadBytes (by omega),
        ite_eq_right (by omega), ite_eq_left hi]
    · rw [ite_eq_right hi]
      by_cases hj : i < k + value.size
      · rw [ite_eq_left hj, ite_eq_left (by omega)]
        congr 1
        omega
      · rw [ite_eq_right hj, byteAt_of_size_le (by omega)]

/-- Two writes within memory to disjoint ranges give the same memory in either order. -/
theorem memoryWrite_comm_of_disjoint {memory a b : ByteArray} {s t : Nat}
    (ha : s + a.size ≤ memory.size) (hb : t + b.size ≤ memory.size)
    (hd : s + a.size ≤ t ∨ t + b.size ≤ s) :
    memoryWrite (memoryWrite memory s a) t b = memoryWrite (memoryWrite memory t b) s a := by
  have hsa : (memoryWrite memory s a).size = memory.size := size_memoryWrite ha
  have htb : (memoryWrite memory t b).size = memory.size := size_memoryWrite hb
  apply eq_of_byteAt
  · rw [size_memoryWrite (by omega), hsa, size_memoryWrite (by omega), htb]
  intro i
  rw [byteAt_memoryWrite (by omega), byteAt_memoryWrite ha, byteAt_memoryWrite (by omega),
    byteAt_memoryWrite hb]
  by_cases hi : t ≤ i ∧ i < t + b.size
  · rw [ite_eq_left hi, ite_eq_right (by omega), ite_eq_left hi]
  · rw [ite_eq_right hi, ite_eq_right hi]

/-- A read across two adjacent writes within memory, made from the higher one, gives both values.

The read gives the lower value, then the higher one. -/
theorem memoryReadBytes_memoryWrite_memoryWrite_rev {memory a b : ByteArray} {s : Nat}
    (hw : s + a.size + b.size ≤ memory.size) :
    memoryReadBytes (memoryWrite (memoryWrite memory (s + a.size) b) s a) s (a.size + b.size) =
      a ++ b := by
  rw [← memoryWrite_comm_of_disjoint (by omega) (by omega) (.inl (Nat.le_refl _))]
  exact memoryReadBytes_memoryWrite_memoryWrite hw

end EthLib.Execution.Evm
