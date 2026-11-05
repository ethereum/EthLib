module

public import EthLib.Execution.Evm.Op
public import EthLib.Execution.Evm.Step

/-!
# `Evm.Instructions.LogData`

LOG0 to LOG4: append a log of a range of memory and up to four topics to the substate.

The log holds the address of the account whose code runs.

A log costs 375, 8 per byte of data, 375 per topic, and the growth of memory.

A log fails in a static frame.

Appendix H.2 of the Yellow Paper, Shanghai version, defines these instructions.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork Hash32 U256)
open EthLib.Execution.Blocks (Log)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The top `n` words of the stack as topics, the top word first, and the frame without them. -/
def popTopics (evm : Evm fork Meter) : Nat → Except EvmError (List Hash32 × Evm fork Meter)
  | 0 => .ok ([], evm)
  | k + 1 => do
    let (word, evm) ← popWord evm
    let (topics, evm) ← popTopics evm k
    return (U256.toBeBytes word :: topics, evm)

/-- LOGn: append a log of `size` bytes of memory from `start`, with `n` topics. -/
def logStep (n : Nat) (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let (start, evm) ← popWord evm
  let (size, evm) ← popWord evm
  let (topics, evm) ← popTopics evm n
  let cost := OPCODE_LOG_BASE + OPCODE_LOG_DATA_PER_BYTE * size.toNat + OPCODE_LOG_TOPIC * n
  let evm ← chargeGasAndMemory evm cost [(start, size)]
  if evm.message.isStatic then
    throw .writeInStaticContext
  else
    let log : Log := {
      address := evm.message.currentTarget
      topics
      data := memoryReadBytes evm.memory start.toNat size.toNat }
    return advance { evm with substate := { evm.substate with logs := evm.substate.logs.push log } }

/-- The instruction of a LOG opcode, or none for another opcode. -/
def logOpStep : Op → Option (Evm fork Meter → Except EvmError (Evm fork Meter))
  | .log n => some (logStep n.val)
  | _ => none

end EthLib.Execution.Evm
