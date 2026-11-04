module

public import EthLib.Execution.Evm.JumpDest
public import EthLib.Execution.Evm.Op
public import EthLib.Execution.Evm.Step

/-!
# `Evm.ControlFlow`

The instructions that move the program counter or read it, and STOP.

A jump goes only to a valid jump destination, and fails otherwise.

JUMPI jumps only when its condition is not zero, and goes to the next opcode otherwise.

Appendix H.2 of the Yellow Paper, Shanghai version, defines these instructions.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (U256)
open GasCosts

variable {Meter : Type} [GasMeter Meter]

/-- STOP: halt the frame, with no output and at no price. -/
def stopStep (evm : Evm Meter) : Except EvmError (Evm Meter) :=
  .ok (advance { evm with running := false })

/-- JUMP: move to `destination`, which must be a valid jump destination. -/
def jumpStep (evm : Evm Meter) : Except EvmError (Evm Meter) := do
  let (destination, evm) ← popWord evm
  let evm ← chargeGas evm OPCODE_JUMP
  if isValidJumpDest evm.validJumpDestinations destination.toNat then
    return { evm with pc := destination.toNat }
  else
    throw .invalidJumpDest

/-- JUMPI: jump to `destination` when the condition is not zero, else go to the next opcode. -/
def jumpiStep (evm : Evm Meter) : Except EvmError (Evm Meter) := do
  let (destination, evm) ← popWord evm
  let (condition, evm) ← popWord evm
  let evm ← chargeGas evm OPCODE_JUMPI
  if condition = 0 then
    return advance evm
  else if isValidJumpDest evm.validJumpDestinations destination.toNat then
    return { evm with pc := destination.toNat }
  else
    throw .invalidJumpDest

/-- JUMPDEST: mark a jump destination, and do nothing else. -/
def jumpdestStep (evm : Evm Meter) : Except EvmError (Evm Meter) := do
  let evm ← chargeGas evm OPCODE_JUMPDEST
  return advance evm

/-- The instruction of an opcode that moves or reads the program counter, or STOP.

GAS reads the gas left after its own price.

Other opcodes give none. -/
def controlFlowStep : Op → Option (Evm Meter → Except EvmError (Evm Meter))
  | .stop => some stopStep
  | .jump => some jumpStep
  | .jumpi => some jumpiStep
  | .pc => some (readFrame OPCODE_PC fun evm => BitVec.ofNat 256 evm.pc)
  | .gas => some (readFrame OPCODE_GAS fun evm => BitVec.ofNat 256 (GasMeter.gasLeft evm.gas))
  | .jumpdest => some jumpdestStep
  | _ => none

end EthLib.Execution.Evm
