module

public import EthLib.Base.Exports
public import EthLib.Base.Exports.ChainConfig
public import EthLib.Base.Hex
public import EthLib.Engine.Capabilities
public import EthLib.Engine.Exports.Errors
public import EthLib.Engine.NewPayload
public import EthLib.Execution.Exports.Transition

/-!
# `Exports.NewPayload`

The C export of `engine_newPayload`, for an execution layer without the parent's state.

The chain configuration and the request cross the boundary as typed Python values.

Each is the value of its JSON, as `json.loads` gives it.

Python refuses a value that cannot cross, such as a `float`, before Lean runs.

The configuration is an object with the chain ID and the activations.

Each activation is a list of a fork name, `block` or `time`, and a number.

The request is a JSON-RPC request object, with its method and its parameters.

The result is the value of the JSON of the payload status.

Its validation error starts with the code of the reason, then a colon.

From version 6 the status has version 2, with a `null` inclusion list verdict.

A JSON-RPC error has the code of its Engine API error: 32602 or 38005.

An unknown method, or an argument that Lean cannot read, has code 0.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result PyValue UnreadArgument pyExport rejectArgument toResult)
open EthLib.Base
open EthLib.Base.ChainConfig.Exports (configOfJson)

/-- Hashes in hex, between brackets and separated by commas. -/
def hashList (hashes : List Hash32) : String :=
  "[" ++ ", ".intercalate (hashes.map fun hash => hexString hash.toList) ++ "]"

/-- A message for the reason of an invalid payload, on one line. -/
def reasonMessage : PayloadError → String
  | .invalidTransaction index e => s!"transaction {index} does not decode: {reprStr e}"
  | .noEncoding => "a field of the block has no RLP encoding"
  | .wrongBlockHash expected computed =>
    s!"block hash {hexString expected.toList}, header hash {hexString computed.toList}"
  | .wrongVersionedHashes expected actual =>
    s!"the expected versioned hashes are not those of the block: " ++
      s!"expected {hashList expected}, got {hashList actual}"
  | .invalidBlock e => s!"{e.code}: {Execution.Blocks.Exports.blockErrorMessage e}"
  | .invalidBlockAccessList => "the block access list is not the RLP form of one"
  | .invalidTerminalBlock parent =>
    s!"the parent {hexString parent.toList} is a block of proof of work that is not terminal"

/-- The JSON of a payload status at a version, with the code of its reason first in the error.

From version 6 the status has version 2, and its inclusion list verdict is `null`.

The verdict of a valid payload needs the execution rules of Bogota, so that case raises code 0.

No payload of Hegotá is valid here yet, since its block does not run. -/
def statusJson (version : Nat) (status : PayloadStatus) (reason : Option PayloadError) :
    Result Json := do
  let error := reason.map fun e => s!"{e.code}: {reasonMessage e}"
  if version < 6 then return Json.payloadStatusJson status error
  if status.status = .valid then
    rejectArgument none "no inclusion list verdict: Bogota does not run here"
  return Json.payloadStatusV2Json status error none

/-- A payload status read from its JSON: the name of the status, the latest valid hash, the error.

The hash and the error are `None` in Python when the JSON has no value for them. -/
def readPayloadStatusOf (status : PyValue) :
    Result (String × Option ByteArray × Option String) := do
  let (s, e) ← toResult "engine error" (Json.payloadStatusOfJson status.toJson)
  return (s.status.name, s.latestValidHash.map (⟨·.toArray⟩), e)

/-- A payload status read from its JSON, as `json.loads` gives it.

The result is the name of the status, the latest valid hash and the validation error.

A status that does not decode is an invalid parameter, with code 32602. -/
@[export eth_engine_read_payload_status]
def readPayloadStatusExport (args : PyValue) : Result PyValue := pyExport readPayloadStatusOf args

/-- The version of a method name `engine_newPayloadV1` to `engine_newPayloadV6`. -/
def newPayloadVersion (method : String) : Option Nat := methodVersion "newPayload" method

/-- The payload status of an `engine_newPayload` request, without the parent's state.

The arguments are the chain configuration and the request. -/
def newPayloadOf (args : PyValue × PyValue) : Result PyValue := do
  let (config, request) := args
  let config ← configOfJson config.toJson
  let request := request.toJson
  let some method := (request.getObjValAs? String "method").toOption
    | rejectArgument none "request: no method"
  let some version := newPayloadVersion method | rejectArgument none s!"no method {method}"
  let params := request.getObjValD "params"
  let (status, reason) ← toResult "engine error" (newPayloadWithoutState config version params)
  return .ofJson (← statusJson version status reason)

/-- The payload status of an `engine_newPayload` request, without the parent's state.

The arguments are the chain configuration and the request. -/
@[export eth_engine_new_payload]
def newPayloadExport (args : PyValue) : Result PyValue :=
  pyExport newPayloadOf args

/-- The payload status of an `engine_newPayload` request, on a chain that holds the parent.

The arguments are the chain configuration, the state, the recent blocks, two totals and the request.

The state takes the form of the state root export.

The recent blocks are a list, each the fork name, the header and its ommers.

The header and each ommer are in RLP form.

The totals are the terminal total difficulty, and the total difficulty of the last recent block.

The terminal total difficulty must be below `2^256`, or the export raises with code 0.

The terminal block hash and number are zero, since the check of the method does not read them.

A valid payload also gives the RLP forms of its header and of the accounts after it. -/
def newPayloadOnChainOf
    (args : PyValue × ByteArray × List (String × ByteArray × List ByteArray) × Nat × Nat ×
      PyValue) :
    Result (PyValue × Option ByteArray × Option ByteArray) := do
  let (config, state, recent, terminalTotalDifficulty, totalDifficulty, request) := args
  unless terminalTotalDifficulty < 2 ^ 256 do
    rejectArgument none
      s!"config: a terminal total difficulty of {terminalTotalDifficulty}, not below 2^256"
  let transition : TransitionConfiguration := {
    terminalTotalDifficulty := BitVec.ofNat 256 terminalTotalDifficulty
    terminalBlockHash := 0
    terminalBlockNumber := 0 }
  let chain ← Execution.Blocks.Exports.chainOf config state recent
  let request := request.toJson
  let some method := (request.getObjValAs? String "method").toOption
    | rejectArgument none "request: no method"
  let some version := newPayloadVersion method | rejectArgument none s!"no method {method}"
  let params := request.getObjValD "params"
  let (status, reason, next) ← toResult "engine error"
    (newPayloadOnChain transition totalDifficulty chain version params)
  let status := PyValue.ofJson (← statusJson version status reason)
  match next with
  | none => return (status, none, none)
  | some (block, post) =>
    let encoded : Except _ (ByteArray × ByteArray) := do
      let header ← Serialization.Rlp.encode (Serialization.Rlp.Codec.toItem block.header)
      let accounts ← Serialization.Rlp.encode (Execution.Blocks.Exports.accountsItem post)
      return (header, accounts)
    let (header, accounts) ← toResult none
      (encoded.mapError fun e => UnreadArgument.mk s!"result: {reprStr e}")
    return (status, some header, some accounts)

/-- The payload status of an `engine_newPayload` request, on a chain that holds the parent.

The arguments are the chain configuration, the state, the recent blocks, two totals and the request.

The totals are the terminal total difficulty, and the total difficulty of the last recent block.

The terminal total difficulty must be below `2^256`, or the export raises with code 0.

A valid payload also gives the RLP forms of its header and of the accounts after it.

Otherwise both are `None`. -/
@[export eth_engine_new_payload_on_chain]
def newPayloadOnChainExport (args : PyValue) : Result PyValue :=
  pyExport newPayloadOnChainOf args

end EthLib.Engine.Exports
