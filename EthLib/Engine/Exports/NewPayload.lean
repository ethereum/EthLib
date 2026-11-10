module

public import EthLib.Base.Exports
public import EthLib.Base.Exports.ChainConfig
public import EthLib.Base.Hex
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

A JSON-RPC error has the code of its Engine API error: 32602 or 38005.

An unknown method, or an argument that Lean cannot read, has code 0.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result PyValue pyExport)
open EthLib.Base
open EthLib.Base.ChainConfig.Exports (configOfJson)

/-- A message for the reason of an invalid payload, on one line. -/
def reasonMessage : PayloadError → String
  | .invalidTransaction index e => s!"transaction {index} does not decode: {reprStr e}"
  | .noEncoding => "a field of the block has no RLP encoding"
  | .wrongBlockHash expected computed =>
    s!"block hash {hexString expected.toList}, header hash {hexString computed.toList}"
  | .wrongVersionedHashes => "the expected versioned hashes are not those of the block"
  | .invalidBlock e => s!"{e.code}: {Execution.Blocks.Exports.blockErrorMessage e}"
  | .invalidBlockAccessList => "the block access list is not the RLP form of one"

/-- The JSON of a payload status, with the code of its reason first in the error. -/
def statusJson (status : PayloadStatus) (reason : Option PayloadError) : Json :=
  let latest := match status.latestValidHash with
    | some h => Json.str (hexString h.toList)
    | none => .null
  let error := match reason with
    | some e => Json.str s!"{e.code}: {reasonMessage e}"
    | none => .null
  (Json.mkObj [("status", status.status.name), ("latestValidHash", latest),
    ("validationError", error)])

/-- The version of a method name `engine_newPayloadV1` to `engine_newPayloadV5`. -/
def newPayloadVersion (method : String) : Option Nat :=
  ["engine_newPayloadV1", "engine_newPayloadV2", "engine_newPayloadV3",
    "engine_newPayloadV4", "engine_newPayloadV5"].idxOf? method |>.map (· + 1)

/-- The payload status of an `engine_newPayload` request, without the parent's state.

The arguments are the chain configuration and the request. -/
def newPayloadOf (args : PyValue × PyValue) : Result PyValue := do
  let (config, request) := args
  let config ← configOfJson config.toJson
  let request := request.toJson
  let some method := (request.getObjValAs? String "method").toOption
    | throw (0, "request: no method")
  let some version := newPayloadVersion method | throw (0, s!"no method {method}")
  let params := request.getObjValD "params"
  match newPayloadWithoutState config version params with
  | .ok (status, reason) => return .ofJson (statusJson status reason)
  | .error e => throw (e.code, s!"engine error: {reprStr e}")

/-- The payload status of an `engine_newPayload` request, without the parent's state.

The arguments are the chain configuration and the request. -/
@[export eth_engine_new_payload]
def newPayloadExport (args : PyValue) : Result PyValue :=
  pyExport newPayloadOf args

/-- The payload status of an `engine_newPayload` request, on a chain that holds the parent.

The arguments are the chain configuration, the state, the recent blocks and the request.

The state takes the form of the state root export.

The recent blocks are a list, each the fork name, the header and its ommers.

The header and each ommer are in RLP form.

A valid payload also gives the RLP forms of its header and of the accounts after it. -/
def newPayloadOnChainOf
    (args : PyValue × ByteArray × List (String × ByteArray × List ByteArray) × PyValue) :
    Result (PyValue × Option ByteArray × Option ByteArray) := do
  let (config, state, recent, request) := args
  let chain ← Execution.Blocks.Exports.chainOf config state recent
  let request := request.toJson
  let some method := (request.getObjValAs? String "method").toOption
    | throw (0, "request: no method")
  let some version := newPayloadVersion method | throw (0, s!"no method {method}")
  match newPayloadOnChain chain version (request.getObjValD "params") with
  | .error e => throw (e.code, s!"engine error: {reprStr e}")
  | .ok (status, reason, next) =>
    let status := PyValue.ofJson (statusJson status reason)
    match next with
    | none => return (status, none, none)
    | some (block, post) =>
      let encoded : Except _ (ByteArray × ByteArray) := do
        let header ← Serialization.Rlp.encode (Serialization.Rlp.Codec.toItem block.header)
        let accounts ← Serialization.Rlp.encode (Execution.Blocks.Exports.accountsItem post)
        return (header, accounts)
      let (header, accounts) ← encoded.mapError fun e => (0, s!"result: {reprStr e}")
      return (status, some header, some accounts)

/-- The payload status of an `engine_newPayload` request, on a chain that holds the parent.

The arguments are the chain configuration, the state, the recent blocks and the request.

A valid payload also gives the RLP forms of its header and of the accounts after it.

Otherwise both are `None`. -/
@[export eth_engine_new_payload_on_chain]
def newPayloadOnChainExport (args : PyValue) : Result PyValue :=
  pyExport newPayloadOnChainOf args

end EthLib.Engine.Exports
