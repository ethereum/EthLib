module

public import EthLib.Base.Bytes
public import EthLib.Base.Exports
public import EthLib.Execution.Evm.Call.ContractAddress
public import EthLib.Execution.Evm.Gas
public import EthLib.Execution.Evm.Op
public import EthLib.Execution.Evm.Instructions.StackN
public import EthLib.Execution.Evm.Instructions.Arithmetic
public import EthLib.Execution.Evm.Instructions.Bitwise
public import EthLib.Execution.Evm.Instructions.Comparison

/-!
# `Exports.Evm`

C-ABI exports of the word of a stack instruction, the price of memory and created addresses.

A word crosses the boundary as 32 big-endian bytes.

A size or a price crosses it as its shortest big-endian bytes, so no value is truncated.

An opcode outside the table of words fails with code 0.

So does an immediate byte that encodes no depth of DUPN, SWAPN or EXCHANGE.

An argument of the wrong length fails with a code from 101, above every code of an RLP error.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Exports

open EthLib.Base (Address U256 bytesToNat natToBytes readBytes)
open EthLib.Exports (Result)

/-- Why an export rejects an argument: the argument has the wrong length. -/
inductive ArgumentError where
  /-- An operand of an instruction is not a word of 32 bytes. -/
  | operandLength
  /-- A list of memory ranges is not a whole number of pairs of words, of 64 bytes each. -/
  | rangesLength
  /-- A sender is not an address of 20 bytes. -/
  | senderLength
  /-- A salt of CREATE2 is not a word of 32 bytes. -/
  | saltLength
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor, for the C exports.

The codes start at 101, above every code of an RLP error, so that the two never meet.

A new constructor takes a new code, so that each code keeps its meaning. -/
def ArgumentError.code : ArgumentError → UInt32
  | .operandLength => 101
  | .rangesLength => 102
  | .senderLength => 103
  | .saltLength => 104

/-- The message of an error, as the bindings raise it. -/
def ArgumentError.message : ArgumentError → String
  | .operandLength => "each operand must be 32 bytes"
  | .rangesLength => "the ranges must be a whole number of 64-byte pairs"
  | .senderLength => "the sender must be 20 bytes"
  | .saltLength => "the salt must be 32 bytes"

/-- The code and the message of an error, as an export returns them. -/
def ArgumentError.toResult (e : ArgumentError) : UInt32 × String :=
  (e.code, e.message)

/-- The word of big-endian bytes, reduced modulo `2^256`. -/
def wordOf (bytes : ByteArray) : U256 :=
  BitVec.ofNat 256 (bytesToNat bytes.toList)

/-- The word of exactly 32 big-endian bytes, or the given error for any other length. -/
def readWord (error : ArgumentError) (bytes : ByteArray) : Result U256 :=
  if bytes.size = 32 then .ok (wordOf bytes) else .error error.toResult

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

Each operand is a word of 32 bytes.

An opcode outside the table fails with code 0, since no Lean error type covers it. -/
@[export eth_evm_word_op]
def wordOpExport (opcode : UInt8) (a b c : ByteArray) : Result ByteArray := do
  -- The lengths come first, so a bad operand fails even with an opcode outside the table.
  let a ← readWord .operandLength a
  let b ← readWord .operandLength b
  let c ← readWord .operandLength c
  match (Op.decode opcode).bind fun op => wordOp op a b c with
  | some w => .ok (bytesOfWord w)
  | none => .error (0, s!"opcode {opcode} does not push a word of its operands alone")

/-- The depths, counted from 1 at the top, that the immediate byte of an opcode encodes.

DUPN and SWAPN give one depth, and EXCHANGE gives two, as EIP-8024 decodes them.

Another opcode, or a byte that encodes no depth, fails with code 0.

No Lean error type covers these failures. -/
@[export eth_evm_immediate_depths]
def immediateDepthsExport (opcode immediate : UInt8) : Result ByteArray :=
  let depths := match Op.decode opcode with
    | some .dupn | some .swapn => (decodeSingle immediate).map fun n => [n]
    | some .exchange => (decodePair immediate).map fun (n, m) => [n, m]
    | _ => none
  match depths with
  | some ds => .ok ⟨(ds.map Nat.toUInt8).toArray⟩
  | none => .error (0, s!"byte {immediate} encodes no depth of opcode {opcode}")

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

/-- The ranges of a memory access, or the error for a length that is not a multiple of 64. -/
def readRanges (ranges : ByteArray) : Result (List (U256 × U256)) :=
  if ranges.size % 64 = 0 then .ok (rangesOf ranges)
  else .error ArgumentError.rangesLength.toResult

/-- The price of growing a memory for a list of ranges.

Each range is a start word, then a size word, so the ranges are a multiple of 64 bytes. -/
@[export eth_evm_extend_memory_cost]
def extendMemoryCostExport (size ranges : ByteArray) : Result ByteArray := do
  return bytesOfNat (extendMemory (bytesToNat size.toList) (← readRanges ranges)).cost

/-- The number of bytes that a memory grows by for a list of ranges.

Each range is a start word, then a size word, so the ranges are a multiple of 64 bytes. -/
@[export eth_evm_extend_memory_expand_by]
def extendMemoryExpandByExport (size ranges : ByteArray) : Result ByteArray := do
  return bytesOfNat (extendMemory (bytesToNat size.toList) (← readRanges ranges)).expandBy

/-- The address of exactly 20 bytes, or the error for any other length. -/
def readAddress (bytes : ByteArray) : Result Address :=
  if h : bytes.size = 20 then .ok (readBytes bytes 0 20 (by omega))
  else .error ArgumentError.senderLength.toResult

/-- The address of the contract that a sender makes with CREATE at a big-endian nonce.

The sender is an address of 20 bytes. -/
@[export eth_evm_create_address]
def createAddressExport (sender nonce : ByteArray) : Result ByteArray := do
  let sender ← readAddress sender
  (createAddress sender (bytesToNat nonce.toList)).map (fun a => ⟨a.toArray⟩)
    |>.mapError fun e => (e.code, s!"create preimage rejected: {reprStr e}")

/-- The address of the contract that a sender makes with CREATE2, from a salt and init code.

The sender is an address of 20 bytes, and the salt is a word of 32 bytes. -/
@[export eth_evm_create2_address]
def create2AddressExport (sender salt initCode : ByteArray) : Result ByteArray := do
  let sender ← readAddress sender
  let salt ← readWord .saltLength salt
  return ⟨(create2Address sender salt initCode).toArray⟩

end EthLib.Execution.Evm.Exports
