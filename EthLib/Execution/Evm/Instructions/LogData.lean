module

public import EthLib.Execution.Evm.Op
public import EthLib.Execution.Evm.Step

/-!
# `Evm.Instructions.LogData`

LOG0 to LOG4: append a log of a range of memory and up to four topics to the substate.

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
  -- The topics of LOGn, `mu_s[2]`, ..., `mu_s[n + 1]`, top first, each word as 32 bytes.
  | k + 1 => do
    let (word, evm) ← popWord evm
    let (topics, evm) ← popTopics evm k
    return (U256.toBeBytes word :: topics, evm)

/-- The price of LOGn with `size` bytes of data: 375, 8 for each byte, and 375 for each topic. -/
def logCost (n : Nat) (size : U256) : Nat :=
  -- Appendix H.1: `G_log + G_logdata × mu_s[1] + n G_logtopic`.
  OPCODE_LOG_BASE + OPCODE_LOG_DATA_PER_BYTE * size.toNat + OPCODE_LOG_TOPIC * n

/-- LOGn: append a log of `size` bytes of memory from `start`, with `n` topics. -/
def logStep (n : Nat) (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let (start, evm) ← popWord evm
  let (size, evm) ← popWord evm
  let (topics, evm) ← popTopics evm n
  -- The price, and `mu'_i = M(mu_i, mu_s[0], mu_s[1])` with its cost.
  --
  -- It also pays the growth of memory.
  let evm ← chargeGasAndMemory evm (logCost n size) [(start, size)]
  -- A log fails in a static frame.
  --
  -- §9.4.2: `Z` holds for `¬I_w ∧ W(w, mu)`, and W holds for every LOG.
  --
  -- The source halts by `Z` before any charge; here the charge comes first.
  --
  -- Any exceptional halt consumes all of `mu_g`, so only the reported error can differ.
  if evm.message.isStatic then
    throw .writeInStaticContext
  else
    -- LOGn: `A'_l = A_l · (I_a, t, mu_m[mu_s[0] ... (mu_s[0] + mu_s[1] - 1)])`.
    --
    -- Here `t = (mu_s[2], ..., mu_s[n + 1])`, the topics.
    let log : Log := {
      -- The log holds the address of the account whose code runs.
      address := evm.message.currentTarget
      topics
      data := memoryReadBytes evm.memory start.toNat size.toNat }
    -- The record of logs for a simulation takes the log too; the source has no such record.
    return advance { evm with
      substate := { evm.substate with
        logs := evm.substate.logs.push log
        simulatedLogs := evm.substate.simulatedLogs.push log } }

/-- The instruction of a LOG opcode, or none for another opcode. -/
def logOpStep : Op → Option (Evm fork Meter → Except EvmError (Evm fork Meter))
  | .log n => some (logStep n.val)
  | _ => none

end EthLib.Execution.Evm
