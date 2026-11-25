module

public import EthLib.Base.Proofs.Bytes
public import EthLib.Execution.Evm.Machine.Memory
public import EthLib.Execution.Proofs.Evm.Gas.Memory

/-!
# Proofs: `Evm.Machine.Memory`

This file proves what reads, writes and growth of memory give, byte by byte.

It also proves how two of them combine.

Memory grows in whole words, so its size stays a multiple of 32.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (U256 byteAtOrZero byteAtOrZero_append byteAtOrZero_append_zeros byteAtOrZero_extract byteAtOrZero_of_size_le
  eq_of_byteAtOrZero)

/-- A read into a byte array is its block, then the zeros it lacks, which may be none. -/
private theorem bufferBytes_eq_append (data : ByteArray) (start size : Nat) :
    bufferBytes data start size =
      let inside := if start < data.size then data.extract start (min (start + size) data.size)
        else .empty
      inside ++ ByteArray.mk (Array.replicate (size - inside.size) 0) := by
  unfold bufferBytes
  dsimp only
  generalize (if start < data.size then data.extract start (min (start + size) data.size)
    else ByteArray.empty) = inside
  by_cases h : inside.size = size
  · simp only [h, ite_true, Nat.sub_self]
    exact ByteArray.append_empty.symm
  · simp only [h, ite_false]

/-- A read into a byte array has exactly the `size` bytes asked for. -/
theorem size_bufferBytes (data : ByteArray) (start size : Nat) :
    (bufferBytes data start size).size = size := by
  rw [bufferBytes_eq_append]
  dsimp only
  split <;>
    simp only [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_empty] <;>
    simp only [← ByteArray.size_data, Array.size_replicate] <;>
    omega

/-- A read into a byte array holds the bytes of the buffer, zero past its end and past `size`. -/
theorem byteAtOrZero_bufferBytes (data : ByteArray) (start size j : Nat) :
    byteAtOrZero (bufferBytes data start size) j =
      if j < size then byteAtOrZero data (start + j) else 0 := by
  rw [bufferBytes_eq_append]
  dsimp only
  -- A byte past the end of the buffer reads as zero on both sides.
  have past : data.size ≤ start + j → byteAtOrZero data (start + j) = 0 := byteAtOrZero_of_size_le
  split
  · rw [byteAtOrZero_append_zeros, byteAtOrZero_extract]
    by_cases hj : j < size
    · by_cases hd : start + j < data.size
      · simp [hj, hd, Nat.lt_min]
      · simp [hj, hd, Nat.lt_min, past (by omega)]
    · simp [hj, Nat.lt_min]
  · rw [byteAtOrZero_append_zeros, byteAtOrZero_of_size_le (by simp)]
    by_cases hj : j < size <;> simp [hj, past (by omega)]

/-- A read is the byte of the buffer at each position, zero past its end. -/
theorem bufferRead_eq (data : ByteArray) (start size : Nat) :
    bufferRead data start size = (List.range size).map fun i => byteAtOrZero data (start + i) := by
  apply List.ext_getElem
  · simp only [bufferRead, Array.length_toList, List.length_map, List.length_range]
    exact size_bufferBytes data start size
  · intro i h1 h2
    have hi : i < size := by simpa using h2
    have hb : i < (bufferBytes data start size).size := by rw [size_bufferBytes]; exact hi
    have h := byteAtOrZero_bufferBytes data start size i
    simp only [hi, ite_true] at h
    simp only [bufferRead, Array.getElem_toList, List.getElem_map, List.getElem_range]
    rw [← h]
    simp [byteAtOrZero, hb, ByteArray.getElem_eq_getElem_data]

/-- A read into a byte array is the bytes of the read as a list. -/
theorem bufferBytes_eq (data : ByteArray) (start size : Nat) :
    bufferBytes data start size = ⟨(bufferRead data start size).toArray⟩ := by
  simp [bufferRead]

/-- A read has exactly the `size` bytes asked for. -/
theorem bufferRead_length (data : ByteArray) (start size : Nat) :
    (bufferRead data start size).length = size := by
  simp [bufferRead_eq]

/-- A read of a whole buffer from its start gives its bytes. -/
theorem bufferRead_zero_size (data : ByteArray) :
    bufferRead data 0 data.size = data.data.toList := by
  apply List.ext_getElem
  · simp [bufferRead_eq]
  · intro i _ h
    have hi : i < data.data.size := by simpa using h
    simp [bufferRead_eq, EthLib.Base.byteAtOrZero_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hi]

/-- A write is the bytes before the range, then the value, then the bytes after the range. -/
theorem memoryWrite_eq (memory : ByteArray) (start : Nat) (value : ByteArray) :
    memoryWrite memory start value = if value.size = 0 then memory
      else memory.extract 0 start ++ value ++ memory.extract (start + value.size) memory.size := by
  unfold memoryWrite
  split
  · rfl
  · apply ByteArray.ext
    have hs : value.data.size = value.size := rfl
    -- The copy keeps the bytes of memory before and after the range, and all of the value.
    simp only [ByteArray.copySlice, ByteArray.data_extract, ByteArray.data_append, Nat.zero_add,
      Nat.sub_zero, hs, Nat.min_self,
      show value.data.extract 0 value.size = value.data from Array.extract_size,
      Array.append_assoc]
    rfl

/-- Growth appends that many zero bytes, also when it is none. -/
theorem memoryExtend_eq (memory : ByteArray) (n : Nat) :
    memoryExtend memory n = memory ++ ByteArray.mk (Array.replicate n 0) := by
  unfold memoryExtend
  split
  · subst n
    apply ByteArray.ext
    simp
  · rfl

/-- A write within memory keeps its size. -/
theorem size_memoryWrite {memory value : ByteArray} {start : Nat}
    (h : start + value.size ≤ memory.size) :
    (memoryWrite memory start value).size = memory.size := by
  rw [memoryWrite_eq]
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

/-- A range read from memory has at most the size it asks for. -/
theorem size_memoryReadBytes_le (memory : ByteArray) (start size : Nat) :
    (memoryReadBytes memory start size).size ≤ size := by
  unfold memoryReadBytes
  split
  · simp
  · simp only [ByteArray.size_extract]
    omega

/-- A read of the range that a write covers gives the written bytes. -/
theorem memoryReadBytes_memoryWrite {memory value : ByteArray} {start : Nat}
    (h : start + value.size ≤ memory.size) :
    memoryReadBytes (memoryWrite memory start value) start value.size = value := by
  unfold memoryReadBytes
  rw [memoryWrite_eq]
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
  rw [memoryExtend_eq, ByteArray.size_append]
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
theorem byteAtOrZero_memoryWrite {memory value : ByteArray} {start : Nat}
    (h : start + value.size ≤ memory.size) (i : Nat) :
    byteAtOrZero (memoryWrite memory start value) i =
      if start ≤ i ∧ i < start + value.size then byteAtOrZero value (i - start)
      else byteAtOrZero memory i := by
  rw [memoryWrite_eq]
  split
  · rw [ite_eq_right_iff.mpr (fun hc => absurd hc (by omega))]
  · have hp : (memory.extract 0 start).size = start := by simp; omega
    rw [byteAtOrZero_append, ByteArray.size_append, hp, byteAtOrZero_append, hp, byteAtOrZero_extract,
      byteAtOrZero_extract]
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
    · exact (byteAtOrZero_of_size_le (by omega)).symm

/-- Growth keeps every byte of memory. -/
theorem byteAtOrZero_memoryExtend (memory : ByteArray) (n i : Nat) :
    byteAtOrZero (memoryExtend memory n) i = byteAtOrZero memory i := by
  rw [memoryExtend_eq]
  exact byteAtOrZero_append_zeros memory n i

/-- A read within memory gives the bytes of memory from its start, and zero past its size. -/
theorem byteAtOrZero_memoryReadBytes {memory : ByteArray} {start size : Nat}
    (h : start + size ≤ memory.size) (i : Nat) :
    byteAtOrZero (memoryReadBytes memory start size) i =
      if i < size then byteAtOrZero memory (start + i) else 0 := by
  unfold memoryReadBytes
  split
  · rw [ite_eq_right_iff.mpr (fun hi => absurd hi (by omega))]
    exact byteAtOrZero_of_size_le (by simp)
  · rw [byteAtOrZero_extract, Nat.min_eq_left h]
    split <;> split <;> first | rfl | omega

/-- A buffer of a read holds the bytes of the read, and zero past its size. -/
theorem byteAtOrZero_bufferRead (data : ByteArray) (offset size j : Nat) :
    byteAtOrZero ⟨(bufferRead data offset size).toArray⟩ j =
      if j < size then byteAtOrZero data (offset + j) else 0 := by
  unfold byteAtOrZero
  by_cases hj : j < size
  · have hlen : j < (bufferRead data offset size).toArray.size := by simp [bufferRead_length, hj]
    rw [dite_eq_left_of_eq_true (eq_true (by simpa [ByteArray.size] using hlen)),
      ite_eq_left_of_eq_true _ _ (eq_true hj), ByteArray.getElem_eq_getElem_data]
    simp [bufferRead_eq, byteAtOrZero]
  · rw [dite_eq_right_of_eq_false
      (eq_false (by simpa [ByteArray.size, bufferRead_length] using hj)),
      ite_eq_right_of_eq_false _ _ (eq_false hj)]

/-- Growth by no byte leaves memory as it is. -/
theorem memoryExtend_zero (memory : ByteArray) : memoryExtend memory 0 = memory := by
  apply eq_of_byteAtOrZero (by simp [size_memoryExtend])
  intro i
  exact byteAtOrZero_memoryExtend memory 0 i

/-- A write of a whole memory from offset 0 gives the written bytes. -/
theorem memoryWrite_whole {memory value : ByteArray} (h : memory.size = value.size) :
    memoryWrite memory 0 value = value := by
  have hs : (memoryWrite memory 0 value).size = value.size := by
    rw [size_memoryWrite (by omega)]
    omega
  apply eq_of_byteAtOrZero hs
  intro i
  rw [byteAtOrZero_memoryWrite (by omega)]
  split
  · simp
  · rename_i hi
    rw [Base.byteAtOrZero_of_size_le (by omega), Base.byteAtOrZero_of_size_le (by omega)]

/-- A write past the end of a memory, into bytes that it grew by, appends the written bytes. -/
theorem memoryWrite_extend_end {memory value : ByteArray} :
    memoryWrite (memoryExtend memory value.size) memory.size value = memory ++ value := by
  have hs : (memoryWrite (memoryExtend memory value.size) memory.size value).size =
      (memory ++ value).size := by
    rw [size_memoryWrite (by simp [size_memoryExtend])]
    simp [size_memoryExtend]
  apply eq_of_byteAtOrZero hs
  intro i
  rw [byteAtOrZero_memoryWrite (by simp [size_memoryExtend]), byteAtOrZero_append]
  split
  · rename_i hi
    rw [ite_eq_right (by omega)]
  · rename_i hi
    by_cases hlt : i < memory.size
    · rw [ite_eq_left hlt, byteAtOrZero_memoryExtend]
    · rw [ite_eq_right hlt]
      rw [Base.byteAtOrZero_of_size_le (by simp [size_memoryExtend]; omega),
        Base.byteAtOrZero_of_size_le (by omega)]

/-- A read of a whole memory from offset 0 gives the memory. -/
theorem memoryReadBytes_whole {memory : ByteArray} :
    memoryReadBytes memory 0 memory.size = memory := by
  apply eq_of_byteAtOrZero (by rw [size_memoryReadBytes (by omega)])
  intro i
  rw [byteAtOrZero_memoryReadBytes (by omega)]
  split
  · simp
  · rename_i hi
    rw [Base.byteAtOrZero_of_size_le (by omega)]

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
  apply eq_of_byteAtOrZero (by simp [hs])
  intro i
  rw [byteAtOrZero_extract, byteAtOrZero_extract, hs]
  split
  · rw [byteAtOrZero_memoryWrite hw, ite_eq_right (by omega)]
  · rfl

/-- A read across two adjacent writes within memory gives the two values in order. -/
theorem memoryReadBytes_memoryWrite_memoryWrite {memory a b : ByteArray} {s : Nat}
    (hw : s + a.size + b.size ≤ memory.size) :
    memoryReadBytes (memoryWrite (memoryWrite memory s a) (s + a.size) b) s (a.size + b.size) =
      a ++ b := by
  have h1 : (memoryWrite memory s a).size = memory.size := size_memoryWrite (by omega)
  have h2 : (memoryWrite (memoryWrite memory s a) (s + a.size) b).size = memory.size := by
    rw [size_memoryWrite (by omega), h1]
  apply eq_of_byteAtOrZero
  · rw [size_memoryReadBytes (by omega), ByteArray.size_append]
  intro i
  rw [byteAtOrZero_memoryReadBytes (by omega), byteAtOrZero_memoryWrite (by omega),
    byteAtOrZero_memoryWrite (by omega), byteAtOrZero_append]
  by_cases hi : i < a.size
  · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left hi]
    congr 1
    omega
  · by_cases hj : i < a.size + b.size
    · rw [ite_eq_left hj, ite_eq_left (by omega), ite_eq_right hi]
      congr 1
      omega
    · rw [ite_eq_right hj, ite_eq_right hi, byteAtOrZero_of_size_le (by omega)]

/-- A read from `k` bytes before a write to its end gives those bytes, then the value.

The write must lie within memory. -/
theorem memoryReadBytes_memoryWrite_eq_append {memory value : ByteArray} {s k : Nat}
    (hw : s + k + value.size ≤ memory.size) :
    memoryReadBytes (memoryWrite memory (s + k) value) s (k + value.size) =
      memoryReadBytes memory s k ++ value := by
  have hs : (memoryWrite memory (s + k) value).size = memory.size := size_memoryWrite hw
  apply eq_of_byteAtOrZero
  · rw [size_memoryReadBytes (by omega), ByteArray.size_append, size_memoryReadBytes (by omega)]
  · intro i
    rw [byteAtOrZero_memoryReadBytes (by omega), byteAtOrZero_memoryWrite hw, byteAtOrZero_append,
      size_memoryReadBytes (by omega)]
    by_cases hi : i < k
    · rw [ite_eq_left (by omega), ite_eq_left hi, byteAtOrZero_memoryReadBytes (by omega),
        ite_eq_right (by omega), ite_eq_left hi]
    · rw [ite_eq_right hi]
      by_cases hj : i < k + value.size
      · rw [ite_eq_left hj, ite_eq_left (by omega)]
        congr 1
        omega
      · rw [ite_eq_right hj, byteAtOrZero_of_size_le (by omega)]

/-- Two writes within memory to disjoint ranges give the same memory in either order. -/
theorem memoryWrite_comm_of_disjoint {memory a b : ByteArray} {s t : Nat}
    (ha : s + a.size ≤ memory.size) (hb : t + b.size ≤ memory.size)
    (hd : s + a.size ≤ t ∨ t + b.size ≤ s) :
    memoryWrite (memoryWrite memory s a) t b = memoryWrite (memoryWrite memory t b) s a := by
  have hsa : (memoryWrite memory s a).size = memory.size := size_memoryWrite ha
  have htb : (memoryWrite memory t b).size = memory.size := size_memoryWrite hb
  apply eq_of_byteAtOrZero
  · rw [size_memoryWrite (by omega), hsa, size_memoryWrite (by omega), htb]
  intro i
  rw [byteAtOrZero_memoryWrite (by omega), byteAtOrZero_memoryWrite ha, byteAtOrZero_memoryWrite (by omega),
    byteAtOrZero_memoryWrite hb]
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
