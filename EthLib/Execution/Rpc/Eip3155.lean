module

public import EthLib.Execution.Rpc.TraceView

/-!
# `Execution.Rpc.Eip3155`

The trace of a transaction in the lines of [EIP-3155][eip-3155], which EVM test tools compare.

Each step of the opcode logger gives one line, a JSON object, and a summary line ends the trace.

The lines write the same records as the debug methods, in a second form.

The fields of a step come in the order of the EIP, as it asks.

So a line is a list of fields in order, since a JSON object of Lean sorts its keys.

The export writes each list as one line of JSON.

[eip-3155]: https://github.com/ethereum/EIPs/blob/b055feec322fbc37e9d77a393a50b3ff56b31c92/EIPS/eip-3155.md#specification
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Serialization.JsonRpc

/-- What the logger records for the lines: the stack, the return data and the storage.

The lines require the return data, which the logger records only on request. -/
def eip3155Config : TraceConfig := { enableReturnData := true }

/-- The fields of the line of one step, in the order of the EIP.

The required fields come first: the position, the opcode byte, the gas and its cost in hex.

Then the memory size, the stack, the depth, the return data and the refund counter.

The memory size is there at every step, whatever the logger records.

The stack and the return data are those that the logger recorded, or empty when it did not.

So a trace for these lines runs the logger with the configuration above.

The name of the opcode follows, then the error, the memory and the storage when they are there. -/
def eip3155Fields (e : StructLog) : List (String × Json) :=
  [("pc", Json.num e.pc), ("op", Json.num e.opcode), ("gas", quantityJson e.gas),
    ("gasCost", quantityJson e.gasCost), ("memSize", Json.num e.memSize),
    ("stack", listJson (quantityJson ·.toNat) (e.stack.getD [])), ("depth", Json.num e.depth),
    ("returnData", dataJson (e.returnData.getD .empty).toList), ("refund", Json.num e.refund),
    ("opName", .str e.op)] ++
  (e.error.map fun err => [("error", Json.str (stepErrorText err))]).getD [] ++
  (e.memory.map fun m => [("memory", Json.arr (memoryWords m).toArray)]).getD [] ++
  (e.storage.map fun slots =>
    [("storage", Json.mkObj (slots.map fun (k, v) => (hexString k.toList, wordJson v)))]).getD []

/-- The fields of the summary line of a transaction.

They are the state root after it, its output, the gas it used in hex, its success and the fork.

The output is its bytes in hex behind `0x`, as the test case of the EIP writes `0x40`.

The gas is that of the whole transaction, its intrinsic gas included and its refund taken off. -/
def eip3155SummaryFields (fork : Fork) (trace : TransactionTrace) (stateRoot : Hash32) :
    List (String × Json) :=
  [("stateRoot", dataJson stateRoot.toList),
    ("output", dataJson trace.returnValue.toList),
    ("gasUsed", quantityJson trace.gas), ("pass", .bool !trace.failed), ("fork", .str fork.name)]

/-- The lines of the trace of a transaction, each as its fields: one per step, then the summary. -/
def eip3155Lines (fork : Fork) (trace : TransactionTrace) (stateRoot : Hash32) :
    List (List (String × Json)) :=
  trace.structLogs.toList.map eip3155Fields ++ [eip3155SummaryFields fork trace stateRoot]

end EthLib.Execution.Rpc
