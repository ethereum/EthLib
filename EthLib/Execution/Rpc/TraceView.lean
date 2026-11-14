module

public import EthLib.Execution.Rpc.Account
public import EthLib.Execution.Rpc.Block
public import EthLib.Execution.Rpc.Trace
public import EthLib.Execution.Rpc.TransactionInfo

/-!
# `Execution.Rpc.TraceView`

The debug methods that trace transactions with the opcode logger, and the JSON of their answers.

A block is traced on the state of its parent, so the node must hold the parent.

Block 0 has no parent, and the methods answer it with an error, as [`trace.yaml`][methods] asks.

The text of the error of a step is a choice of this specification, since the source fixes none.

[`opcode-tracer.yaml`][schema] defines the answers.

[methods]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/debug/trace.yaml
[schema]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/opcode-tracer.yaml
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.Evm (EvmError)
open EthLib.Serialization.JsonRpc

/-! ## The configuration -/

/-- The configuration of the opcode logger in a request.

A named tracer is out of the scope of the source, so a request for one fails.

The timeout, the debug flag and the configuration of a named tracer change no answer.

They are read and left aside. -/
def traceConfig (j : Json) : Read TraceConfig := do
  let fs ← fields "trace config" j
  let flag (name : String) : Read Bool :=
    match fs.lookup name with
    | some v => bool name v
    | none => pure false
  if let some t := fs.lookup "tracer" then
    unless (← string "tracer" t).isEmpty do reject "tracer: named tracers are not supported"
  if let some t := fs.lookup "timeout" then discard <| string "timeout" t
  if let some d := fs.lookup "debug" then discard <| bool "debug" d
  if let some c := fs.lookup "tracerConfig" then discard <| fields "tracerConfig" c
  let limit ← match fs.lookup "limit" with
    | some v => do
      let n ← integer "limit" v
      if n < 0 then reject "limit: negative" else pure n.toNat
    | none => pure 0
  return { disableStack := ← flag "disableStack", enableMemory := ← flag "enableMemory"
           enableReturnData := ← flag "enableReturnData", disableStorage := ← flag "disableStorage"
           limit }

/-! ## The JSON of the answers -/

/-- The text of the error of a step. -/
def stepErrorText : EvmError → String
  | .stackUnderflow => "stack underflow"
  | .stackOverflow => "stack overflow"
  | .outOfGas => "out of gas"
  | .invalidOpcode _ => "invalid opcode"
  | .invalidJumpDest => "invalid jump destination"
  | .writeInStaticContext => "write protection"
  | .outOfBoundsRead => "return data out of bounds"
  | .invalidParameter => "invalid parameter"
  | .invalidContractPrefix => "invalid code: must not begin with 0xef"
  | .addressCollision => "contract address collision"
  | .precompile => "precompile failed"
  | .revert => "execution reverted"
  | .state _ => "state error"
  | .unspecifiedOpcode _ => "unspecified opcode"
  | .encoding _ => "encoding error"
  | .forkNotYetSpecified _ => "fork not yet specified"

/-- Memory as words of 32 bytes, the last one padded with zeros. -/
def memoryWords (memory : ByteArray) : List Json :=
  (List.range ((memory.size + 31) / 32)).map fun i =>
    dataJson ((List.range 32).map fun j => byteAt memory (32 * i + j))

/-- The JSON of an entry of the opcode logger.

The refund counter is always given, as the source recommends.

Empty memory and empty return data are left out.

The fixtures leave them out, and they match this form field for field. -/
def structLogJson (e : StructLog) : Json :=
  Json.mkObj <|
    [("pc", Json.num e.pc), ("op", .str e.op), ("gas", Json.num e.gas),
      ("gasCost", Json.num e.gasCost), ("depth", Json.num e.depth)] ++
    (e.error.map fun err => [("error", Json.str (stepErrorText err))]).getD [] ++
    [("refund", Json.num e.refund)] ++
    (e.stack.map fun s => [("stack", listJson (quantityJson ·.toNat) s)]).getD [] ++
    ((e.memory.filter (·.size ≠ 0)).map fun m =>
      [("memory", Json.arr (memoryWords m).toArray)]).getD [] ++
    ((e.returnData.filter (·.size ≠ 0)).map fun d => [("returnData", dataJson d.toList)]).getD [] ++
    (e.storage.map fun slots =>
      [("storage", Json.mkObj (slots.map fun (k, v) => (hexString k.toList, wordJson v)))]).getD []

/-- The JSON of the opcode trace of a transaction. -/
def transactionTraceJson (t : TransactionTrace) : Json :=
  Json.mkObj
    [("gas", Json.num t.gas), ("failed", .bool t.failed),
      ("returnValue", dataJson t.returnValue.toList),
      ("structLogs", Json.arr (t.structLogs.map structLogJson))]

/-- The JSON of the traces of a block, each with the hash of its transaction. -/
def blockTraceJson (traces : List (Hash32 × TransactionTrace)) : Json :=
  listJson (fun (h, t) => Json.mkObj [("txHash", hash32Json h), ("result", transactionTraceJson t)])
    traces

/-! ## The methods -/

namespace ChainView

/-- The chain that a block runs on, when the node holds its parent on the canonical chain.

A parent off the canonical chain has no chain in the view, so its child is not traced. -/
def parentChain (v : ChainView) (r : BlockRecord) : Option BlockChain :=
  (List.finRange v.canonical.length).findSome? fun (i : Fin v.canonical.length) =>
    if v.canonical[i.val].hash == r.block.header.parentHash then some (v.chainAt i.val i.isLt)
    else none

/-- The error for block 0, with the code and the message of the official genesis fixture. -/
def genesisNotTraceable : RpcError :=
  invalidInput.toRpcError (some (.str "genesis is not traceable"))

/-- The chain that a block runs on, or the error when it cannot be traced.

Block 0 fails, and so does a block whose parent the node does not hold. -/
def traceChain (v : ChainView) (r : BlockRecord) : Except RpcError BlockChain :=
  if r.block.header.number = 0 then .error genesisNotTraceable
  else match v.parentChain r with
    | some chain => .ok chain
    | none => .error (prunedHistoryUnavailable.toRpcError none)

/-- The error of a block that fails to run.

A valid view never gives it for a canonical block. -/
def runFailed : RpcError :=
  internalError.toRpcError (some (.str "the block fails to run"))

/-- The traces of the transactions of a block, each with its hash. -/
def traceBlockRecord (v : ChainView) (config : TraceConfig) (r : BlockRecord) :
    Except RpcError (List (Hash32 × TransactionTrace)) := do
  let chain ← v.traceChain r
  let traces ← (traceBlock config chain r.block).mapError fun _ => runFailed
  return (← r.transactionHashes).zip traces

/-- The error for a block that the node does not hold. -/
def blockNotFound : RpcError :=
  invalidInput.toRpcError (some (.str "block not found"))

/-- The traces of the block that a parameter names.

A number below the lowest block of the node names pruned history. -/
def traceBlockByParam (v : ChainView) (config : TraceConfig) (p : BlockParam) :
    Except RpcError (List (Hash32 × TransactionTrace)) := do
  match ← v.resolve p with
  | some r => v.traceBlockRecord config r
  | none =>
    match p with
    | .number 0 => .error genesisNotTraceable
    | .number n =>
      if n < v.lowest.block.header.number then .error (prunedHistoryUnavailable.toRpcError none)
      else .error blockNotFound
    | _ => .error blockNotFound

/-- The trace of the transaction with a hash, in the first block that holds it, canonical first. -/
def traceTransactionByHash (v : ChainView) (config : TraceConfig) (hash : Hash32) :
    Except RpcError TransactionTrace := do
  match v.findTransaction hash with
  | none => .error (invalidInput.toRpcError (some (.str "transaction not found")))
  | some (r, _, index) =>
    let chain ← v.traceChain r
    match ← (traceTransactionAt config chain r.block index).mapError fun _ => runFailed with
    | some trace => return trace
    | none => .error runFailed

end ChainView

end EthLib.Execution.Rpc
