module

public import EthLib.Execution.Evm.Memory

/-!
# Proofs: `Evm.Memory`

- A read gives exactly the bytes asked for.
- Past the end of the buffer every byte reads as zero.
- So padding the buffer with zeros changes no byte.
-/

@[expose] public section

namespace EthLib.Execution.Evm

/-- A read has exactly the `size` bytes asked for. -/
theorem bufferRead_length (data : ByteArray) (start size : Nat) :
    (bufferRead data start size).length = size := by
  simp [bufferRead]

/-- Past the end of the buffer every byte reads as zero. -/
theorem byteAt_of_size_le {data : ByteArray} {i : Nat} (h : data.size ≤ i) :
    byteAt data i = 0 := by
  simp [byteAt, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]

/-- Padding the buffer with zero bytes on the right changes no byte. -/
theorem byteAt_append_zeros (data : ByteArray) (n i : Nat) :
    byteAt (data ++ ByteArray.mk (Array.replicate n 0)) i = byteAt data i := by
  by_cases h : i < data.size
  · simp [byteAt, ByteArray.data_append, Array.getD_eq_getD_getElem?,
      Array.getElem?_append_left h]
  · have h' : data.size ≤ i := Nat.le_of_not_lt h
    rw [byteAt_of_size_le h']
    -- Past the end of the data, the padding is zeros and beyond it nothing.
    simp only [byteAt, ByteArray.data_append, Array.getD_eq_getD_getElem?]
    rw [Array.getElem?_append_right (by simpa using h'), Array.getElem?_replicate]
    split <;> simp

end EthLib.Execution.Evm
