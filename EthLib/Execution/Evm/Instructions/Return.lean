module

public import EthLib.Execution.Evm.Op
public import EthLib.Execution.Evm.Step

/-!
# `Evm.Instructions.Return`

RETURN and REVERT: stop the frame and give back a range of memory as its output.

Each pays only for the growth of memory.

RETURN ends the frame normally.

REVERT ends it with the revert error, so its changes roll back but it keeps its gas left.

[EIP-140][eip140] adds REVERT at Byzantium.

Appendix H.2 of the Yellow Paper, Shanghai version, defines both.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip140]: https://eips.ethereum.org/EIPS/eip-140#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The frame stopped, with `size` bytes of memory from `start` as output, once it pays. -/
def haltWithOutput (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let (start, evm) ← popWord evm
  let (size, evm) ← popWord evm
  let evm ← chargeGasAndMemory evm 0 [(start, size)]
  return { evm with
    output := memoryReadBytes evm.memory start.toNat size.toNat
    running := false }

/-- RETURN: stop the frame, with a range of memory as its output. -/
def returnStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) :=
  haltWithOutput evm

/-- REVERT: stop the frame with the revert error, with a range of memory as its output.

The frame keeps its gas left, unlike an exceptional halt. -/
def revertStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let evm ← haltWithOutput evm
  return { evm with error := some .revert }

/-- The instruction of RETURN or REVERT, at fork `fork`.

Other opcodes give none, and so does REVERT before Byzantium. -/
def returnOpStep (fork : Fork) : Op → Option (Evm fork Meter → Except EvmError (Evm fork Meter))
  | .«return» => some returnStep
  | .revert => if .byzantium ≤ fork then some revertStep else none
  | _ => none

end EthLib.Execution.Evm
