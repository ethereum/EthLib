module

public import EthLib.Base.Proofs.BigEndian
public import EthLib.Execution.Evm.Precompiles.Modexp.Encoding
public import EthLib.Execution.Proofs.Evm.Memory

/-!
# Proofs: `Modexp.Encoding`

How the call data is read.

- A read of `size` bytes is below `256 ^ size`.
- A read depends only on the bytes it covers, so padding the call data with zeros changes no read.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Modexp

open EthLib.Base
open EthLib.Execution.Evm

/-- A read of `size` bytes is worth less than `256 ^ size`. -/
theorem readNat_lt (data : ByteArray) (start size : Nat) :
    readNat data start size < 256 ^ size := by
  have := bytesToNat_lt (bufferRead data start size)
  rwa [bufferRead_length] at this

/-- A read of no bytes is `0`. -/
theorem readNat_zero_size (data : ByteArray) (start : Nat) : readNat data start 0 = 0 := by
  simp [readNat, bufferRead, bytesToNat]

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
