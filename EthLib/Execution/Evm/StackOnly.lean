module

public import EthLib.Execution.Evm.Instructions.Arithmetic
public import EthLib.Execution.Evm.Instructions.Bitwise
public import EthLib.Execution.Evm.Instructions.Comparison
public import EthLib.Execution.Evm.Instructions.Keccak
public import EthLib.Execution.Evm.Op
public import EthLib.Execution.Evm.StackN
public import EthLib.Execution.Evm.Step

/-!
# `Evm.StackOnly`

The instructions that read and write only the stack, and KECCAK256.

Each one pops its operands, pays a price, pushes one word and moves to the next opcode.

The word it pushes is the pure function of the instruction.

KECCAK256 also reads memory, and it pays for each word it hashes and for the growth of memory.

DUPN, SWAPN and EXCHANGE, from Glamsterdam, read an immediate byte, so they move two bytes on.

Appendix H.2 of the Yellow Paper, Shanghai version, defines these instructions up to Shanghai.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256 bytesToNat)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- POP: drop the top word. -/
def popStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let (_, evm) ← popWord evm
  let evm ← chargeGas evm OPCODE_POP
  return advance evm

/-- The `n` bytes of code after the opcode at `pc`, read as a big-endian word.

The code reads as zeros past its end. -/
def pushData (code : ByteArray) (pc n : Nat) : U256 :=
  BitVec.ofNat 256 (bytesToNat (bufferRead code (pc + 1) n))

/-- PUSHn: push the next `n` bytes of code, then skip them.

PUSH0 costs the base price, by EIP-3855, and the other pushes the very low price. -/
def pushN (n : Fin 33) (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let evm ← chargeGas evm (if n.val = 0 then OPCODE_PUSH0 else OPCODE_PUSH)
  let evm ← pushWord evm (pushData evm.code evm.pc n)
  return advance evm (1 + n)

/-- DUP(n + 1): push a copy of the word at depth `n`. -/
def dupN (n : Fin 16) (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let evm ← chargeGas evm OPCODE_DUP
  match evm.stack.val[n.val]? with
  | none => .error .stackUnderflow
  | some x =>
    let evm ← pushWord evm x
    return advance evm

/-- SWAP(n + 1): exchange the top word with the word at depth `n + 1`. -/
def swapN (n : Fin 16) (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let evm ← chargeGas evm OPCODE_SWAP
  match evm.stack with
  | ⟨top :: rest, h⟩ =>
    match rest[n.val]? with
    | none => .error .stackUnderflow
    | some x =>
      -- The new list has the length of the old one, so it stays within the limit.
      let swapped : Stack := ⟨x :: rest.set n.val top, by simpa using h⟩
      return advance { evm with stack := swapped }
  | ⟨[], _⟩ => .error .stackUnderflow

/-- The number of bytes that the exponent of EXP takes, without leading zero bytes. -/
def exponentBytes (exponent : U256) : Nat :=
  (Instructions.bitLength exponent.toNat + 7) / 8

/-- EXP: the base price, plus a price per byte of the exponent that depends on the fork. -/
def expStep (fork : Fork) (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let (base, evm) ← popWord evm
  let (exponent, evm) ← popWord evm
  let cost := OPCODE_EXP_BASE + (gasSchedule fork).OPCODE_EXP_PER_BYTE * exponentBytes exponent
  let evm ← chargeGas evm cost
  let evm ← pushWord evm (Instructions.exp base exponent)
  return advance evm

/-- KECCAK256: hash `size` bytes of memory from `start`, after the memory grows to hold them. -/
def keccak256Step (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let (start, evm) ← popWord evm
  let (size, evm) ← popWord evm
  let cost := OPCODE_KECCAK256_BASE + OPCODE_KECCAK256_PER_WORD * wordCount size.toNat
  let evm ← chargeGasAndMemory evm cost [(start, size)]
  let data := memoryReadBytes evm.memory start.toNat size.toNat
  let evm ← pushWord evm (Instructions.keccak data)
  return advance evm

/-- The instruction of an opcode that reads and writes only the stack, or KECCAK256.

Other opcodes give none.

The fork sets the price of EXP, and DUPN, SWAPN and EXCHANGE exist from Glamsterdam. -/
def stackOnlyStep (fork : Fork) : Op → Option (Evm fork Meter → Except EvmError (Evm fork Meter))
  | .add => some (binaryOp OPCODE_ADD Instructions.add)
  | .mul => some (binaryOp OPCODE_MUL Instructions.mul)
  | .sub => some (binaryOp OPCODE_SUB Instructions.sub)
  | .div => some (binaryOp OPCODE_DIV Instructions.div)
  | .sdiv => some (binaryOp OPCODE_SDIV Instructions.sdiv)
  | .mod => some (binaryOp OPCODE_MOD Instructions.mod)
  | .smod => some (binaryOp OPCODE_SMOD Instructions.smod)
  | .addmod => some (ternaryOp OPCODE_ADDMOD Instructions.addmod)
  | .mulmod => some (ternaryOp OPCODE_MULMOD Instructions.mulmod)
  | .exp => some (expStep fork)
  | .signextend => some (binaryOp OPCODE_SIGNEXTEND Instructions.signextend)
  | .lt => some (binaryOp OPCODE_LT Instructions.lessThan)
  | .gt => some (binaryOp OPCODE_GT Instructions.greaterThan)
  | .slt => some (binaryOp OPCODE_SLT Instructions.signedLessThan)
  | .sgt => some (binaryOp OPCODE_SGT Instructions.signedGreaterThan)
  | .eq => some (binaryOp OPCODE_EQ Instructions.equal)
  | .iszero => some (unaryOp OPCODE_ISZERO Instructions.isZero)
  | .and => some (binaryOp OPCODE_AND Instructions.bitwiseAnd)
  | .or => some (binaryOp OPCODE_OR Instructions.bitwiseOr)
  | .xor => some (binaryOp OPCODE_XOR Instructions.bitwiseXor)
  | .not => some (unaryOp OPCODE_NOT Instructions.bitwiseNot)
  | .byte => some (binaryOp OPCODE_BYTE Instructions.getByte)
  | .shl => some (binaryOp OPCODE_SHL Instructions.bitwiseShl)
  | .shr => some (binaryOp OPCODE_SHR Instructions.bitwiseShr)
  | .sar => some (binaryOp OPCODE_SAR Instructions.bitwiseSar)
  | .clz => some (unaryOp OPCODE_CLZ Instructions.countLeadingZeros)
  | .keccak256 => some keccak256Step
  | .pop => some popStep
  | .push n => some (pushN n)
  | .dup n => some (dupN n)
  | .swap n => some (swapN n)
  | .dupn => if .glamsterdam ≤ fork then some dupnStep else none
  | .swapn => if .glamsterdam ≤ fork then some swapnStep else none
  | .exchange => if .glamsterdam ≤ fork then some exchangeStep else none
  | _ => none

end EthLib.Execution.Evm
