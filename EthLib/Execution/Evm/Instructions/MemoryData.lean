module

public import EthLib.Execution.Evm.Op
public import EthLib.Execution.Evm.Step

/-!
# `Evm.Instructions.MemoryData`

The instructions that move bytes between the stack, memory, call data, code and return data.

An instruction that touches memory first grows it to hold its ranges, and pays for that growth.

A copy also pays 3 gas for each word that it copies.

Appendix H.2 of the Yellow Paper, Shanghai version, defines them, and EIP-5656 adds MCOPY.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256 ByteOrder.ofBE)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The word of `size` bytes of a buffer from `start`, big-endian, with zeros past its end. -/
def loadWord (data : ByteArray) (start size : Nat) : U256 :=
  BitVec.ofNat 256 (ByteOrder.ofBE (bufferRead data start size))

/-- The 32 bytes of a word, most significant first. -/
def wordBytes (word : U256) : ByteArray :=
  ⟨(U256.toBeBytes word).toArray⟩

/-- MLOAD: push the word of memory at `start`. -/
def mloadStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let (start, evm) ← popWord evm
  -- `G_verylow`, and `mu'_i = max(mu_i, ceil((mu_s[0] + 32) / 32))` with its cost.
  let evm ← chargeGasAndMemory evm OPCODE_MLOAD_BASE [(start, 32)]
  -- MLOAD: `mu'_s[0] = mu_m[mu_s[0] ... (mu_s[0] + 31)]`.
  let evm ← pushWord evm (loadWord (memoryReadBytes evm.memory start.toNat 32) 0 32)
  return advance evm

/-- MSTORE: write a word to memory at `start`. -/
def mstoreStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let (start, evm) ← popWord evm
  let (value, evm) ← popWord evm
  -- `G_verylow`, and `mu'_i = max(mu_i, ceil((mu_s[0] + 32) / 32))` with its cost.
  let evm ← chargeGasAndMemory evm OPCODE_MSTORE_BASE [(start, 32)]
  -- MSTORE: `mu'_m[mu_s[0] ... (mu_s[0] + 31)] = mu_s[1]`, big-endian.
  return advance { evm with memory := memoryWrite evm.memory start.toNat (wordBytes value) }

/-- MSTORE8: write the lowest byte of a word to memory at `start`. -/
def mstore8Step (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let (start, evm) ← popWord evm
  let (value, evm) ← popWord evm
  -- `G_verylow`, and `mu'_i = max(mu_i, ceil((mu_s[0] + 1) / 32))` with its cost.
  let evm ← chargeGasAndMemory evm OPCODE_MSTORE8_BASE [(start, 1)]
  -- MSTORE8: `mu'_m[mu_s[0]] = mu_s[1] mod 256`.
  let byte : ByteArray := ⟨#[UInt8.ofNat value.toNat]⟩
  return advance { evm with memory := memoryWrite evm.memory start.toNat byte }

/-- MCOPY: copy `length` bytes of memory from `source` to `destination`, by EIP-5656.

The copy reads the whole source before it writes, so overlapping ranges copy the old bytes. -/
def mcopyStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let (destination, evm) ← popWord evm
  let (source, evm) ← popWord evm
  let (length, evm) ← popWord evm
  -- EIP-5656: `Gverylow + Gcopy * ceil(length / 32)`, plus the cost of the memory growth.
  let cost := OPCODE_MCOPY_BASE + OPCODE_COPY_PER_WORD * wordCount length.toNat
  -- If `length > 0`, the memory grows to hold `src + length` and `dst + length`.
  let evm ← chargeGasAndMemory evm cost [(source, length), (destination, length)]
  -- EIP-5656: the copy acts as if through an intermediate buffer.
  let value := memoryReadBytes evm.memory source.toNat length.toNat
  return advance { evm with memory := memoryWrite evm.memory destination.toNat value }

/-- CALLDATALOAD: push the word of call data at `start`, with zeros past its end. -/
def calldataloadStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let (start, evm) ← popWord evm
  let evm ← chargeGas evm OPCODE_CALLDATALOAD
  -- CALLDATALOAD: `mu'_s[0] = I_d[mu_s[0] ... (mu_s[0] + 31)]`, with `I_d[x] = 0` past its end.
  let evm ← pushWord evm (loadWord evm.message.data start.toNat 32)
  return advance evm

/-- A copy of `size` bytes of `source` from `offset` to memory at `start`.

The source reads as zeros past its end. -/
def copyToMemory (base : Nat) (source : ByteArray) (evm : Evm fork Meter) :
    Except EvmError (Evm fork Meter) := do
  let (start, evm) ← popWord evm
  let (offset, evm) ← popWord evm
  let (size, evm) ← popWord evm
  -- Appendix H.1: `G_verylow + G_copy × ceil(mu_s[2] / 32)`, for CALLDATACOPY and CODECOPY.
  let cost := base + OPCODE_COPY_PER_WORD * wordCount size.toNat
  -- `mu'_i = M(mu_i, mu_s[0], mu_s[2])`, with its cost.
  let evm ← chargeGasAndMemory evm cost [(start, size)]
  -- `mu'_m[mu_s[0] + i] = I_d[mu_s[1] + i]` for `i < mu_s[2]`, or `I_b` for CODECOPY.
  --
  -- Past the end the byte is 0, which is STOP for CODECOPY.
  let value := bufferBytes source offset.toNat size.toNat
  return advance { evm with memory := memoryWrite evm.memory start.toNat value }

/-- RETURNDATACOPY: copy return data to memory, by EIP-211.

It fails when the range ends past the return data, after it pays. -/
def returndatacopyStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let (start, evm) ← popWord evm
  let (offset, evm) ← popWord evm
  let (size, evm) ← popWord evm
  -- `mu'_i = M(mu_i, mu_s[0], mu_s[2])`, priced with the copy.
  let growth := extendMemory evm.memory.size [(start, size)]
  -- `G_verylow + G_copy × ceil(mu_s[2] / 32)`, plus the growth of memory.
  let cost := OPCODE_RETURNDATACOPY_BASE + OPCODE_RETURNDATACOPY_PER_WORD * wordCount size.toNat
  let evm ← chargeGas evm (cost + growth.cost)
  -- §9.4.2: `Z` holds when `mu_s[1] + mu_s[2] > ||mu_o||`.
  --
  -- The source halts by `Z` before any charge; here the charge comes first.
  --
  -- Any exceptional halt consumes all of `mu_g`, so only the reported error can differ.
  if evm.returnData.size < offset.toNat + size.toNat then
    throw (.outOfBoundsRead offset.toNat size.toNat evm.returnData.size)
  -- The memory grows only after the bound holds.
  let memory := memoryExtend evm.memory growth.expandBy
  -- RETURNDATACOPY: `mu'_m[mu_s[0] + i] = mu_o[mu_s[1] + i]` for `i < mu_s[2]`.
  let value := memoryReadBytes evm.returnData offset.toNat size.toNat
  return advance { evm with memory := memoryWrite memory start.toNat value }

/-- The instruction of an opcode that moves bytes to or from memory or a buffer.

Other opcodes give none. -/
def memoryDataStep : Op → Option (Evm fork Meter → Except EvmError (Evm fork Meter))
  | .mload => some mloadStep
  | .mstore => some mstoreStep
  | .mstore8 => some mstore8Step
  -- MSIZE: `mu'_s[0] = 32 mu_i`, the size of the memory in bytes.
  | .msize => some (readFrame OPCODE_MSIZE fun evm => BitVec.ofNat 256 evm.memory.size)
  | .mcopy => some mcopyStep
  | .calldataload => some calldataloadStep
  -- CALLDATASIZE: `mu'_s[0] = ||I_d||`.
  | .calldatasize =>
    some (readFrame OPCODE_CALLDATASIZE fun evm => BitVec.ofNat 256 evm.message.data.size)
  | .calldatacopy => some fun evm => copyToMemory OPCODE_CALLDATACOPY_BASE evm.message.data evm
  -- CODESIZE: `mu'_s[0] = ||I_b||`.
  | .codesize => some (readFrame OPCODE_CODESIZE fun evm => BitVec.ofNat 256 evm.code.size)
  | .codecopy => some fun evm => copyToMemory OPCODE_CODECOPY_BASE evm.code evm
  -- RETURNDATASIZE: `mu'_s[0] = ||mu_o||`, by EIP-211.
  | .returndatasize =>
    some (readFrame OPCODE_RETURNDATASIZE fun evm => BitVec.ofNat 256 evm.returnData.size)
  | .returndatacopy => some returndatacopyStep
  | _ => none

end EthLib.Execution.Evm
