module

public import EthLib.Execution.Evm.Op
public import EthLib.Execution.Evm.Step

/-!
# `Evm.MemoryData`

The instructions that move bytes between the stack, memory, call data, code and return data.

An instruction that touches memory first grows it to hold its ranges, and pays for that growth.

A copy also pays 3 gas for each word that it copies.

Appendix H.2 of the Yellow Paper, Shanghai version, defines them, and EIP-5656 adds MCOPY.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (U256 bytesToNat)
open GasCosts

variable {Meter : Type} [GasMeter Meter]

/-- The word of `size` bytes of a buffer from `start`, big-endian, with zeros past its end. -/
def loadWord (data : ByteArray) (start size : Nat) : U256 :=
  BitVec.ofNat 256 (bytesToNat (bufferRead data start size))

/-- The 32 bytes of a word, most significant first. -/
def wordBytes (word : U256) : ByteArray :=
  ⟨(U256.toBeBytes word).toArray⟩

/-- MLOAD: push the word of memory at `start`. -/
def mloadStep (evm : Evm Meter) : Except EvmError (Evm Meter) := do
  let (start, evm) ← popWord evm
  let evm ← chargeGasAndMemory evm OPCODE_MLOAD_BASE [(start, 32)]
  let evm ← pushWord evm (loadWord (memoryReadBytes evm.memory start.toNat 32) 0 32)
  return advance evm

/-- MSTORE: write a word to memory at `start`. -/
def mstoreStep (evm : Evm Meter) : Except EvmError (Evm Meter) := do
  let (start, evm) ← popWord evm
  let (value, evm) ← popWord evm
  let evm ← chargeGasAndMemory evm OPCODE_MSTORE_BASE [(start, 32)]
  return advance { evm with memory := memoryWrite evm.memory start.toNat (wordBytes value) }

/-- MSTORE8: write the lowest byte of a word to memory at `start`. -/
def mstore8Step (evm : Evm Meter) : Except EvmError (Evm Meter) := do
  let (start, evm) ← popWord evm
  let (value, evm) ← popWord evm
  let evm ← chargeGasAndMemory evm OPCODE_MSTORE8_BASE [(start, 1)]
  let byte : ByteArray := ⟨#[UInt8.ofNat value.toNat]⟩
  return advance { evm with memory := memoryWrite evm.memory start.toNat byte }

/-- MCOPY: copy `length` bytes of memory from `source` to `destination`, by EIP-5656.

The copy reads the whole source before it writes, so overlapping ranges copy the old bytes. -/
def mcopyStep (evm : Evm Meter) : Except EvmError (Evm Meter) := do
  let (destination, evm) ← popWord evm
  let (source, evm) ← popWord evm
  let (length, evm) ← popWord evm
  let cost := OPCODE_MCOPY_BASE + OPCODE_COPY_PER_WORD * wordCount length.toNat
  let evm ← chargeGasAndMemory evm cost [(source, length), (destination, length)]
  let value := memoryReadBytes evm.memory source.toNat length.toNat
  return advance { evm with memory := memoryWrite evm.memory destination.toNat value }

/-- CALLDATALOAD: push the word of call data at `start`, with zeros past its end. -/
def calldataloadStep (evm : Evm Meter) : Except EvmError (Evm Meter) := do
  let (start, evm) ← popWord evm
  let evm ← chargeGas evm OPCODE_CALLDATALOAD
  let evm ← pushWord evm (loadWord evm.message.data start.toNat 32)
  return advance evm

/-- A copy of `size` bytes of `source` from `offset` to memory at `start`.

The source reads as zeros past its end. -/
def copyToMemory (base : Nat) (source : ByteArray) (evm : Evm Meter) :
    Except EvmError (Evm Meter) := do
  let (start, evm) ← popWord evm
  let (offset, evm) ← popWord evm
  let (size, evm) ← popWord evm
  let cost := base + OPCODE_COPY_PER_WORD * wordCount size.toNat
  let evm ← chargeGasAndMemory evm cost [(start, size)]
  let value : ByteArray := ⟨(bufferRead source offset.toNat size.toNat).toArray⟩
  return advance { evm with memory := memoryWrite evm.memory start.toNat value }

/-- RETURNDATACOPY: copy return data to memory, by EIP-211.

It fails when the range ends past the return data, after it pays. -/
def returndatacopyStep (evm : Evm Meter) : Except EvmError (Evm Meter) := do
  let (start, evm) ← popWord evm
  let (offset, evm) ← popWord evm
  let (size, evm) ← popWord evm
  let growth := extendMemory evm.memory.size [(start, size)]
  let cost := OPCODE_RETURNDATACOPY_BASE + OPCODE_RETURNDATACOPY_PER_WORD * wordCount size.toNat
  let evm ← chargeGas evm (cost + growth.cost)
  if evm.returnData.size < offset.toNat + size.toNat then
    throw .outOfBoundsRead
  let memory := memoryExtend evm.memory growth.expandBy
  let value := memoryReadBytes evm.returnData offset.toNat size.toNat
  return advance { evm with memory := memoryWrite memory start.toNat value }

/-- The instruction of an opcode that moves bytes to or from memory or a buffer.

Other opcodes give none. -/
def memoryDataStep : Op → Option (Evm Meter → Except EvmError (Evm Meter))
  | .mload => some mloadStep
  | .mstore => some mstoreStep
  | .mstore8 => some mstore8Step
  | .msize => some (readFrame OPCODE_MSIZE fun evm => BitVec.ofNat 256 evm.memory.size)
  | .mcopy => some mcopyStep
  | .calldataload => some calldataloadStep
  | .calldatasize =>
    some (readFrame OPCODE_CALLDATASIZE fun evm => BitVec.ofNat 256 evm.message.data.size)
  | .calldatacopy => some fun evm => copyToMemory OPCODE_CALLDATACOPY_BASE evm.message.data evm
  | .codesize => some (readFrame OPCODE_CODESIZE fun evm => BitVec.ofNat 256 evm.code.size)
  | .codecopy => some fun evm => copyToMemory OPCODE_CODECOPY_BASE evm.code evm
  | .returndatasize =>
    some (readFrame OPCODE_RETURNDATASIZE fun evm => BitVec.ofNat 256 evm.returnData.size)
  | .returndatacopy => some returndatacopyStep
  | _ => none

end EthLib.Execution.Evm
