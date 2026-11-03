module

public import EthLib.Base.Proofs.BigEndian
public import EthLib.Execution.Evm.Precompiles.Modexp.Bytes

/-!
# Proofs: `Bytes`

How the call data is read.

- Reading past the end of the call data gives zeros.
  So padding the call data with zeros changes no read.
- A read depends only on the bytes it covers.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Modexp

open EthLib.Base

/-- A window of the call data has exactly the `size` bytes asked for. -/
theorem bufferRead_length (data : ByteArray) (start size : Nat) :
    (bufferRead data start size).length = size := by
  simp [bufferRead]

/-- A read of `size` bytes is worth less than `256 ^ size`. -/
theorem readNat_lt (data : ByteArray) (start size : Nat) :
    readNat data start size < 256 ^ size := by
  have := bytesToNat_lt (bufferRead data start size)
  rwa [bufferRead_length] at this

/-- A read of no bytes is `0`. -/
theorem readNat_zero_size (data : ByteArray) (start : Nat) : readNat data start 0 = 0 := by
  simp [readNat, bufferRead, bytesToNat]

/-- Past the end of the call data every byte reads as zero. -/
theorem byteAt_of_size_le {data : ByteArray} {i : Nat} (h : data.size ≤ i) :
    byteAt data i = 0 := by
  simp [byteAt, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]

/-- Padding the call data with zero bytes on the right changes no byte. -/
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

/-- A read depends only on the bytes it covers. -/
theorem readNat_congr {d₁ d₂ : ByteArray} {start size : Nat}
    (h : ∀ i, start ≤ i → i < start + size → byteAt d₁ i = byteAt d₂ i) :
    readNat d₁ start size = readNat d₂ start size := by
  unfold readNat bufferRead
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  exact h _ (by omega) (by omega)

/-- Padding the call data with zero bytes changes no read. -/
theorem readNat_append_zeros (data : ByteArray) (n start size : Nat) :
    readNat (data ++ ByteArray.mk (Array.replicate n 0)) start size = readNat data start size :=
  readNat_congr fun i _ _ => byteAt_append_zeros data n i

end EthLib.Execution.Evm.Precompiles.Modexp
