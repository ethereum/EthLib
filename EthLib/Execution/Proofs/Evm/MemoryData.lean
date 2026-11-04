module

public import EthLib.Base.Proofs.BigEndian
public import EthLib.Base.Proofs.U256
public import EthLib.Execution.Evm.MemoryData
public import EthLib.Execution.Proofs.Evm.Memory
public import EthLib.Execution.Proofs.Evm.Step

/-!
# Proofs: `Evm.MemoryData`

A word that MSTORE writes reads back whole with MLOAD at the same offset.

MCOPY copies the old bytes of its source, also when the source and the destination overlap.

CALLDATALOAD reads the call data past its end as zeros.

RETURNDATACOPY that pays fails exactly when its range ends past the return data.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (U256 bytesToNat natToBytes)
open GasCosts

variable {Meter : Type} [GasMeter Meter]

/-- A word has 32 bytes. -/
theorem size_wordBytes (word : U256) : (wordBytes word).size = 32 := by
  simp [wordBytes, ← ByteArray.size_data]

/-- A read of a whole buffer from its start gives its bytes. -/
theorem bufferRead_zero_size (data : ByteArray) :
    bufferRead data 0 data.size = data.data.toList := by
  apply List.ext_getElem
  · simp [bufferRead]
  · intro i _ h
    have hi : i < data.data.size := by simpa using h
    simp [bufferRead, byteAt, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]

/-- The word of 32 bytes that a write of a word puts in memory is that word. -/
theorem loadWord_memoryWrite_wordBytes {memory : ByteArray} {start : Nat} (word : U256)
    (h : start + 32 ≤ memory.size) :
    loadWord (memoryReadBytes (memoryWrite memory start (wordBytes word)) start 32) 0 32 =
      word := by
  have hsize := size_wordBytes word
  rw [← hsize, memoryReadBytes_memoryWrite (by omega), loadWord, bufferRead_zero_size]
  have bytes : (wordBytes word).data.toList = natToBytes 32 word.toNat :=
    EthLib.Base.U256.toList_toBeBytes word
  have small : word.toNat < 256 ^ 32 := by
    have := word.isLt
    rwa [show (2 : Nat) ^ 256 = 256 ^ 32 by decide] at this
  rw [bytes, EthLib.Base.bytesToNat_natToBytes_of_lt small]
  apply BitVec.eq_of_toNat_eq
  simp

/-- MCOPY reads its source before it writes, so overlapping ranges copy the old bytes. -/
theorem memoryReadBytes_memoryWrite_memoryReadBytes {memory : ByteArray}
    {source destination length : Nat} (hs : source + length ≤ memory.size)
    (hd : destination + length ≤ memory.size) :
    memoryReadBytes (memoryWrite memory destination (memoryReadBytes memory source length))
        destination length =
      memoryReadBytes memory source length := by
  have hsize : (memoryReadBytes memory source length).size = length := by
    simp only [memoryReadBytes, ByteArray.size_extract]
    omega
  have := memoryReadBytes_memoryWrite (memory := memory) (start := destination)
    (value := memoryReadBytes memory source length) (by omega)
  rwa [hsize] at this

/-- CALLDATALOAD reads the call data past its end as zeros. -/
theorem loadWord_append_zeros (data : ByteArray) (start size k : Nat) :
    loadWord (data ++ ByteArray.mk (Array.replicate k 0)) start size =
      loadWord data start size := by
  simp only [loadWord, bufferRead, byteAt_append_zeros]

/-- RETURNDATACOPY that pays fails exactly when its range ends past the return data. -/
theorem returndatacopyStep_eq_error_iff {evm : Evm Meter} {start offset size : U256}
    {rest : List U256} {gas : Meter} (h : evm.stack.val = start :: offset :: size :: rest)
    (paid : GasMeter.charge evm.gas
      (OPCODE_RETURNDATACOPY_BASE + OPCODE_RETURNDATACOPY_PER_WORD * wordCount size.toNat +
        (extendMemory evm.memory.size [(start, size)]).cost) = .ok gas) :
    returndatacopyStep evm = .error .outOfBoundsRead ↔
      evm.returnData.size < offset.toNat + size.toNat := by
  have hstack : evm.stack = ⟨start :: offset :: size :: rest, h ▸ evm.stack.property⟩ :=
    Subtype.ext h
  simp only [returndatacopyStep, popWord, chargeGas, hstack, Stack.pop]
  by_cases past : evm.returnData.size < offset.toNat + size.toNat <;>
    simp [paid, past, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

end EthLib.Execution.Evm
