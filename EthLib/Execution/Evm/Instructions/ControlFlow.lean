module

public import EthLib.Execution.Evm.Machine.JumpDest
public import EthLib.Execution.Evm.Op
public import EthLib.Execution.Evm.Step

/-!
# `Evm.Instructions.ControlFlow`

The instructions that move the program counter or read it, and STOP.

A jump goes only to a valid jump destination, and fails otherwise.

JUMPI jumps only when its condition is not zero, and goes to the next opcode otherwise.

Appendix H.2 of the Yellow Paper, Shanghai version, defines these instructions.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- STOP: halt the frame, with no output and at no price. -/
def stopStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) :=
  -- §9.4.4: `H(mu, I) = ()` for STOP, an empty output that halts the frame.
  --
  -- Appendix H.1: STOP is in `W_zero`, so it costs `G_zero = 0` and nothing is charged.
  .ok (advance { evm with running := false })

/-- JUMP: move to `destination`, which must be a valid jump destination. -/
def jumpStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let (destination, evm) ← popWord evm
  -- Appendix H.1: JUMP is in `W_mid`, so `C = G_mid`.
  let evm ← chargeGas evm OPCODE_JUMP
  -- Appendix H.2, JUMP: `J_JUMP(mu) = mu_s[0]`, written to `mu'_{pc}`.
  if isValidJumpDest evm.validJumpDestinations destination.toNat then
    return { evm with pc := destination.toNat }
  -- §9.4.2: `Z` holds for `mu_s[0] ∉ D(I_b)`.
  --
  -- §9.5 evaluates `Z` before the charge of `C`; any exceptional halt consumes all of `mu_g`.
  --
  -- So charging first changes neither the state nor the gas; only the reported error can differ.
  else
    throw (.invalidJumpDest destination.toNat)

/-- JUMPI: jump to `destination` when the condition is not zero, else go to the next opcode. -/
def jumpiStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let (destination, evm) ← popWord evm
  let (condition, evm) ← popWord evm
  -- Appendix H.1: JUMPI is in `W_high`, so `C = G_high`.
  let evm ← chargeGas evm OPCODE_JUMPI
  -- Appendix H.2, JUMPI: `J_JUMPI(mu) = mu_{pc} + 1` for `mu_s[1] = 0`.
  if condition = 0 then
    return advance evm
  -- And `J_JUMPI(mu) = mu_s[0]` for `mu_s[1] ≠ 0`.
  else if isValidJumpDest evm.validJumpDestinations destination.toNat then
    return { evm with pc := destination.toNat }
  -- §9.4.2: `Z` holds for `mu_s[1] ≠ 0` and `mu_s[0] ∉ D(I_b)`.
  --
  -- The charge comes first, as for JUMP.
  else
    throw (.invalidJumpDest destination.toNat)

/-- JUMPDEST: mark a jump destination, and do nothing else. -/
def jumpdestStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  -- Appendix H.2: JUMPDEST has no effect on the machine state but its price `G_jumpdest`.
  --
  -- Then the step to the next opcode.
  let evm ← chargeGas evm OPCODE_JUMPDEST
  return advance evm

/-- The instruction of an opcode that moves or reads the program counter, or STOP.

GAS reads the gas left after its own price.

Other opcodes give none. -/
def controlFlowStep : Op → Option (Evm fork Meter → Except EvmError (Evm fork Meter))
  | .stop => some stopStep
  | .jump => some jumpStep
  | .jumpi => some jumpiStep
  -- PC: `mu'_s[0] = mu_{pc}`, before the increment.
  | .pc => some (readFrame OPCODE_PC fun evm => BitVec.ofNat 256 evm.pc)
  -- GAS: `mu'_s[0] = mu_g - G_base`, the gas after its own price, as the text of Appendix H.2 says.
  --
  -- Its formula `mu'_s[0] = mu_g` reads the gas before that price.
  --
  -- From Glamsterdam, the reservoir of EIP-8037 is left out.
  | .gas => some (readFrame OPCODE_GAS fun evm => BitVec.ofNat 256 (GasMeter.gasLeft evm.gas))
  | .jumpdest => some jumpdestStep
  | _ => none

end EthLib.Execution.Evm
