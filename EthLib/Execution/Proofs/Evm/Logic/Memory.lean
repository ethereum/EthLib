module

public import EthLib.Execution.Proofs.Evm.Machine.Memory
public import EthLib.Base.Proofs.Bytes

/-!
# Proofs: memory of a whole number of words

A contract keeps words at the start of memory, and its memory then holds just those words.

A growth by no byte and a write over the whole memory each give a simple memory.

So do a write into the bytes that memory grew by, and a read of the whole memory.

The rules of the logic leave the growth of memory as it is.

A proof uses these facts to put each memory back into a simple form between two rules.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (byteAt byteAt_append eq_of_byteAt)

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

end EthLib.Execution.Evm.Logic
