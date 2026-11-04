module

public import EthLib.Base.Exports
public import EthLib.Execution.Evm.ContractAddress
public import EthLib.Execution.Evm.Gas
public import EthLib.Execution.Evm.Op
public import EthLib.Execution.Evm.Instructions.Arithmetic
public import EthLib.Execution.Evm.Instructions.Bitwise
public import EthLib.Execution.Evm.Instructions.Comparison

/-!
# `Exports.Evm`

C-ABI exports of the word of a stack instruction, the price of memory and created addresses.

A word crosses the boundary as 32 big-endian bytes.

A size or a price crosses it as its shortest big-endian bytes, so no value is truncated.

An opcode outside the table of words fails with code 0.
-/

public section

namespace EthLib.Execution.Evm.Exports

open EthLib.Base (Address U256 bytesToNat natToBytes)
open EthLib.Exports (Result)
open EthLib.Execution.Evm.Instructions

/-- The word of big-endian bytes, reduced modulo `2^256`. -/
def wordOf (bytes : ByteArray) : U256 :=
  BitVec.ofNat 256 (bytesToNat bytes.toList)

/-- The 32 big-endian bytes of a word. -/
def bytesOfWord (w : U256) : ByteArray :=
  ⟨(U256.toBeBytes w).toArray⟩

/-- The shortest big-endian bytes of a number, with one byte for 0. -/
def bytesOfNat (n : Nat) : ByteArray :=
  ⟨(natToBytes (n.log2 / 8 + 1) n).toArray⟩

/-- The word that the instruction of an opcode pushes, for operands from the top of the stack.

The opcodes are those whose word depends only on their operands.

An instruction with fewer than three operands ignores the last ones. -/
def wordOp (op : Op) (a b c : U256) : Option U256 :=
  match op with
  | .add => some (add a b)
  | .mul => some (mul a b)
  | .sub => some (sub a b)
  | .div => some (div a b)
  | .sdiv => some (sdiv a b)
  | .mod => some (mod a b)
  | .smod => some (smod a b)
  | .addmod => some (addmod a b c)
  | .mulmod => some (mulmod a b c)
  | .exp => some (exp a b)
  | .signextend => some (signextend a b)
  | .lt => some (lessThan a b)
  | .gt => some (greaterThan a b)
  | .slt => some (signedLessThan a b)
  | .sgt => some (signedGreaterThan a b)
  | .eq => some (equal a b)
  | .iszero => some (isZero a)
  | .and => some (bitwiseAnd a b)
  | .or => some (bitwiseOr a b)
  | .xor => some (bitwiseXor a b)
  | .not => some (bitwiseNot a)
  | .byte => some (getByte a b)
  | .shl => some (bitwiseShl a b)
  | .shr => some (bitwiseShr a b)
  | .sar => some (bitwiseSar a b)
  | .clz => some (countLeadingZeros a)
  | _ => none

/-- The word that the instruction of an opcode pushes.

Each opcode is read at a fork that has it.

An opcode outside the table fails with code 0, since no Lean error type covers it. -/
@[export eth_evm_word_op]
def wordOpExport (opcode : UInt8) (a b c : ByteArray) : Result ByteArray :=
  match (Op.decode opcode).bind fun op => wordOp op (wordOf a) (wordOf b) (wordOf c) with
  | some w => .ok (bytesOfWord w)
  | none => .error (0, s!"opcode {opcode} does not push a word of its operands alone")

/-- The price of a memory of a given size in bytes. -/
@[export eth_evm_memory_gas_cost]
def memoryGasCostExport (size : ByteArray) : ByteArray :=
  bytesOfNat (memoryGasCost (bytesToNat size.toList))

/-- The ranges of a memory access: each 64 bytes are a start word, then a size word. -/
def rangesOf (ranges : ByteArray) : List (U256 × U256) :=
  (List.range (ranges.size / 64)).map fun i =>
    let start := ranges.extract (64 * i) (64 * i + 32)
    let size := ranges.extract (64 * i + 32) (64 * i + 64)
    (wordOf start, wordOf size)

/-- The price of growing a memory for a list of ranges. -/
@[export eth_evm_extend_memory_cost]
def extendMemoryCostExport (size ranges : ByteArray) : ByteArray :=
  bytesOfNat (extendMemory (bytesToNat size.toList) (rangesOf ranges)).cost

/-- The number of bytes that a memory grows by for a list of ranges. -/
@[export eth_evm_extend_memory_expand_by]
def extendMemoryExpandByExport (size ranges : ByteArray) : ByteArray :=
  bytesOfNat (extendMemory (bytesToNat size.toList) (rangesOf ranges)).expandBy

/-- The address in the first 20 bytes, with zeros past the end; the caller passes 20 bytes. -/
def addressOf (bytes : ByteArray) : Address :=
  Vector.ofFn fun i => bytes.get! i

/-- The address of the contract that a sender makes with CREATE at a big-endian nonce. -/
@[export eth_evm_create_address]
def createAddressExport (sender nonce : ByteArray) : Result ByteArray :=
  (createAddress (addressOf sender) (bytesToNat nonce.toList)).map (fun a => ⟨a.toArray⟩)
    |>.mapError fun e => (e.code, s!"create preimage rejected: {reprStr e}")

/-- The address of the contract that a sender makes with CREATE2, from a salt and init code. -/
@[export eth_evm_create2_address]
def create2AddressExport (sender salt initCode : ByteArray) : ByteArray :=
  ⟨(create2Address (addressOf sender) (wordOf salt) initCode).toArray⟩

end EthLib.Execution.Evm.Exports
