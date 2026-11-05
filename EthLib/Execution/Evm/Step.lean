module

public import EthLib.Base.BigEndian
public import EthLib.Base.Except
public import EthLib.Execution.Evm.Frame
public import EthLib.Execution.Evm.Gas
public import EthLib.Execution.Evm.Memory

/-!
# `Evm.Step`

The parts that every instruction is made of: pop words, charge gas, grow memory, push a word.

An instruction pops its operands first, then pays, then computes, then moves the program counter.

The gas meter is a parameter, so these parts serve every meter.

A step gives the next frame, or a message to run first, for a call.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256 bytesToNat)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The top word of the stack, and the frame without it. -/
def popWord (evm : Evm fork Meter) : Except EvmError (U256 × Evm fork Meter) := do
  let (x, stack) ← evm.stack.pop
  return (x, { evm with stack })

/-- The frame with a word on top of its stack. -/
def pushWord (evm : Evm fork Meter) (x : U256) : Except EvmError (Evm fork Meter) := do
  let stack ← evm.stack.push x
  return { evm with stack }

/-- The frame with its program counter moved by `n`. -/
def advance (evm : Evm fork Meter) (n : Nat := 1) : Evm fork Meter :=
  { evm with pc := evm.pc + n }

/-- The frame after it pays `cost` and the growth of memory for `ranges`, with memory grown.

Each range is a start and a size, as the instruction pops them. -/
def chargeGasAndMemory (evm : Evm fork Meter) (cost : Nat) (ranges : List (U256 × U256)) :
    Except EvmError (Evm fork Meter) := do
  let growth := extendMemory evm.memory.size ranges
  let evm ← chargeGas evm (cost + growth.cost)
  return { evm with memory := memoryExtend evm.memory growth.expandBy }

/-- An instruction that pays `cost`, then pushes a word that it reads from the frame. -/
def readFrame (cost : Nat) (value : Evm fork Meter → U256) (evm : Evm fork Meter) :
    Except EvmError (Evm fork Meter) := do
  let evm ← chargeGas evm cost
  let evm ← pushWord evm (value evm)
  return advance evm

/-- An instruction that pops `x`, pays `cost` and pushes `f x`. -/
def unaryOp (cost : Nat) (f : U256 → U256) (evm : Evm fork Meter) :
    Except EvmError (Evm fork Meter) := do
  let (x, evm) ← popWord evm
  let evm ← chargeGas evm cost
  let evm ← pushWord evm (f x)
  return advance evm

/-- An instruction that pops `x` then `y`, pays `cost` and pushes `f x y`. -/
def binaryOp (cost : Nat) (f : U256 → U256 → U256) (evm : Evm fork Meter) :
    Except EvmError (Evm fork Meter) := do
  let (x, evm) ← popWord evm
  let (y, evm) ← popWord evm
  let evm ← chargeGas evm cost
  let evm ← pushWord evm (f x y)
  return advance evm

/-- An instruction that pops `x`, `y` then `z`, pays `cost` and pushes `f x y z`. -/
def ternaryOp (cost : Nat) (f : U256 → U256 → U256 → U256) (evm : Evm fork Meter) :
    Except EvmError (Evm fork Meter) := do
  let (x, evm) ← popWord evm
  let (y, evm) ← popWord evm
  let (z, evm) ← popWord evm
  let evm ← chargeGas evm cost
  let evm ← pushWord evm (f x y z)
  return advance evm

/-- What one step of a frame gives. -/
inductive StepResult (fork : Fork) (Meter : Type) where
  /-- The frame after the step. -/
  | next (evm : Evm fork Meter)
  /-- A message to run first, from the frame `caller`.

  The frame goes on with `resume` applied to the frame that ends the message. -/
  | child (caller : Evm fork Meter) (message : Message fork)
      (resume : Evm fork Meter → Except EvmError (Evm fork Meter))

end EthLib.Execution.Evm
