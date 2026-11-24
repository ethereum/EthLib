module

public import EthLib.Base.Bytes
public import EthLib.Base.Exports.PyValue
public import EthLib.Execution.Evm.Call.ContractAddress
public import EthLib.Execution.Evm.Gas.Memory
public import EthLib.Execution.Evm.Op
public import EthLib.Execution.Evm.Instructions.StackN
public import EthLib.Execution.Evm.Instructions.Arithmetic
public import EthLib.Execution.Evm.Instructions.Bitwise
public import EthLib.Execution.Evm.Instructions.Comparison
public import EthLib.Serialization.Exports.Rlp

/-!
# `Exports.Evm`

C-ABI exports of the word of a stack instruction, the price of memory and created addresses.

The word of an instruction, the price of memory and the CREATE address take typed Python values.

A word, a size or a price crosses as an `int`, so no value is truncated, and a word is below 2^256.

An argument that is not of its type fails with code 0.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Exports

open EthLib.Base (Address U256 ByteOrder.ofBE)
open EthLib.Exports (ExportError Result PyValue pyExport rejectArgument toResult)

/-- Why an export rejects an argument: the argument has the wrong length. -/
inductive ArgumentError where
  /-- A sender has `size` bytes, not the 20 bytes of an address. -/
  | senderLength (size : Nat)
  /-- A salt of CREATE2 has `size` bytes, not the 32 bytes of a word. -/
  | saltLength (size : Nat)
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor, for the C exports.

The codes are above every code of an RLP error, so that the two never meet.

A new constructor takes a new code, so that each code keeps its meaning.

Codes 101 and 102 stay unused, so that no code takes a second meaning. -/
def ArgumentError.code : ArgumentError → UInt32
  | .senderLength _ => 103
  | .saltLength _ => 104

/-- The message of an error, as the bindings raise it. -/
def ArgumentError.message : ArgumentError → String
  | .senderLength size => s!"the sender must be 20 bytes, not {size}"
  | .saltLength size => s!"the salt must be 32 bytes, not {size}"

/-- An argument of the wrong length reaches Python with its code and its message. -/
instance : ExportError ArgumentError where
  code := ArgumentError.code
  message := ArgumentError.message

/-- The code and the message of an error, as an export returns them. -/
def ArgumentError.toResult (e : ArgumentError) : UInt32 × String :=
  (e.code, e.message)

/-- The word of big-endian bytes, reduced modulo `2^256`. -/
def wordOf (bytes : ByteArray) : U256 :=
  BitVec.ofNat 256 (ByteOrder.ofBE bytes.toList)

/-- The word of exactly 32 big-endian bytes, or the given error for any other length. -/
def readWord (error : Nat → ArgumentError) (bytes : ByteArray) : Result U256 :=
  if bytes.size = 32 then .ok (wordOf bytes) else toResult none (.error (error bytes.size))

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

/-- The word that the instruction of an opcode pushes, for at most three operands.

Each opcode is read at a fork that has it, and a missing operand is 0.

An opcode outside the table fails with code 0, since no Lean error type covers it. -/
def wordOpOf (args : UInt8 × List U256) : Result U256 := do
  let (opcode, operands) := args
  -- More than three operands fail with code 0.
  --
  -- The count comes first, so too many operands fail even with an opcode outside the table.
  if operands.length > 3 then rejectArgument none "an instruction takes at most 3 operands"
  let operand (i : Nat) := operands.getD i 0
  match (Op.decode opcode).bind fun op => wordOp op (operand 0) (operand 1) (operand 2) with
  | some w => .ok w
  -- An opcode outside the table of words fails with code 0.
  | none => rejectArgument none s!"opcode {opcode} does not push a word of its operands alone"

/-- The word that the instruction of an opcode pushes, for at most three operands.

The arguments are the opcode and the list of the operands, each an `int` below 2^256.

A missing operand is 0, and an opcode outside the table fails with code 0. -/
@[export eth_evm_word_op]
def wordOpExport (args : PyValue) : Result PyValue :=
  pyExport wordOpOf args

/-- The depths, counted from 1 at the top, that the immediate byte of an opcode encodes.

DUPN and SWAPN give one depth, and EXCHANGE gives two, as EIP-8024 decodes them.

Another opcode, or a byte that encodes no depth, fails with code 0.

No Lean error type covers these failures. -/
@[export eth_evm_immediate_depths]
def immediateDepthsExport (opcode immediate : UInt8) : Result ByteArray :=
  -- The opcode and the immediate byte cross as integers, and the depths come back as bytes.
  let depths := match Op.decode opcode with
    | some .dupn | some .swapn => (decodeSingle immediate).map fun n => [n]
    | some .exchange => (decodePair immediate).map fun (n, m) => [n, m]
    | _ => none
  match depths with
  | some ds => .ok ⟨(ds.map Nat.toUInt8).toArray⟩
  -- An immediate byte that encodes no depth of DUPN, SWAPN or EXCHANGE fails with code 0.
  | none => rejectArgument none s!"byte {immediate} encodes no depth of opcode {opcode}"

/-- The price of a memory of a given size in bytes. -/
@[export eth_evm_memory_gas_cost]
def memoryGasCostExport (args : PyValue) : Result PyValue :=
  pyExport (fun size => pure (memoryGasCost size)) args

/-- The price of growing a memory for a list of ranges, and the bytes that it grows by.

The arguments are the size of the memory and the ranges, each a start word and a size word. -/
def extendMemoryOf (args : Nat × List (U256 × U256)) : Result (Nat × Nat) := do
  let (size, ranges) := args
  let extension := extendMemory size ranges
  return (extension.cost, extension.expandBy)

/-- The price of growing a memory for a list of ranges, and the bytes that it grows by.

The arguments are the size of the memory and the ranges, each a start word and a size word. -/
@[export eth_evm_extend_memory]
def extendMemoryExport (args : PyValue) : Result PyValue :=
  pyExport extendMemoryOf args

/-- The address of exactly 20 bytes, or the error for any other length. -/
def readAddress (bytes : ByteArray) : Result Address :=
  toResult none (Base.exactBytes 20 bytes ArgumentError.senderLength)

/-- The address of the contract that a sender makes with CREATE at a nonce.

The sender is an address of 20 bytes. -/
def createAddressOf (args : ByteArray × Nat) : Result ByteArray := do
  let (sender, nonce) := args
  let sender ← readAddress sender
  toResult "create preimage rejected" ((createAddress sender nonce).map fun a => ⟨a.toArray⟩)

/-- The address of the contract that a sender makes with CREATE at a nonce.

The arguments are the sender, an address of 20 bytes, and the nonce, an `int`. -/
@[export eth_evm_create_address]
def createAddressExport (args : PyValue) : Result PyValue :=
  pyExport createAddressOf args

/-- The address of the contract that a sender makes with CREATE2, from a salt and init code.

The sender is an address of 20 bytes, and the salt is a word of 32 bytes. -/
@[export eth_evm_create2_address]
def create2AddressExport (sender salt initCode : ByteArray) : Result ByteArray := do
  -- The sender crosses as bytes.
  --
  -- A sender of the wrong length fails with a code above every code of an RLP error.
  let sender ← readAddress sender
  -- The salt is 32 big-endian bytes, and a salt of the wrong length fails the same way.
  let salt ← readWord .saltLength salt
  return ⟨(create2Address sender salt initCode).toArray⟩

end EthLib.Execution.Evm.Exports
