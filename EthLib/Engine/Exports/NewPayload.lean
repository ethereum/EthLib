module

public import EthLib.Base.Exports
public import EthLib.Base.Exports.ChainConfig
public import EthLib.Base.Hex
public import EthLib.Engine.NewPayload
public import EthLib.Execution.Exports.Transition

/-!
# `Exports.NewPayload`

The C export of `engine_newPayload`, for an execution layer without the parent's state.

The chain configuration and the request cross the boundary as JSON text in UTF-8.

The configuration is an object with the chain ID and the activations.

Each activation is a list of a fork name, `block` or `time`, and a number.

The request is a JSON-RPC request object, with its method and its parameters.

The result is the JSON text of the payload status.

Its validation error starts with the code of the reason, then a colon.

A JSON-RPC error has the code of its Engine API error: 32602 or 38005.

An unknown method, or input that is not JSON, has code 0.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result)
open EthLib.Base
open EthLib.Base.ChainConfig.Exports (configOfJson parseJson)

/-- Bytes as lowercase hex behind `0x`. -/
def hex (bytes : List UInt8) : String :=
  bytes.foldl (init := "0x") fun s b =>
    (s.push hexAlphabet[b.toNat >>> 4]!).push hexAlphabet[b.toNat &&& 15]!

/-- A message for the reason of an invalid payload, on one line. -/
def reasonMessage : PayloadError → String
  | .invalidTransaction index e => s!"transaction {index} does not decode: {reprStr e}"
  | .noEncoding => "a field of the block has no RLP encoding"
  | .wrongBlockHash expected computed =>
    s!"block hash {hex expected.toList}, header hash {hex computed.toList}"
  | .wrongVersionedHashes => "the expected versioned hashes are not those of the block"
  | .invalidBlock e => s!"{e.code}: {Execution.Blocks.Exports.blockErrorMessage e}"

/-- The JSON of a payload status, with the code of its reason first in the error. -/
def statusJson (status : PayloadStatus) (reason : Option PayloadError) : Json :=
  let latest := match status.latestValidHash with
    | some h => Json.str (hex h.toList)
    | none => .null
  let error := match reason with
    | some e => Json.str s!"{e.code}: {reasonMessage e}"
    | none => .null
  (Json.mkObj [("status", status.status.name), ("latestValidHash", latest),
    ("validationError", error)])

/-- The version of a method name `engine_newPayloadV1` to `engine_newPayloadV4`. -/
def newPayloadVersion (method : String) : Option Nat :=
  ["engine_newPayloadV1", "engine_newPayloadV2", "engine_newPayloadV3",
    "engine_newPayloadV4"].idxOf? method |>.map (· + 1)

/-- The payload status of an `engine_newPayload` request, without the parent's state. -/
@[export eth_engine_new_payload]
def newPayloadExport (config request : ByteArray) : Result ByteArray := do
  let config ← configOfJson (← parseJson "config" config)
  let request ← parseJson "request" request
  let some method := (request.getObjValAs? String "method").toOption
    | throw (0, "request: no method")
  let some version := newPayloadVersion method | throw (0, s!"no method {method}")
  let params := request.getObjValD "params"
  match newPayloadWithoutState config version params with
  | .ok (status, reason) => return (statusJson status reason).compress.toUTF8
  | .error e => throw (e.code, s!"engine error: {reprStr e}")

/-- The payload status of an `engine_newPayload` request, on a chain that holds the parent.

The chain has the inputs of the state transition export: configuration, state, recent blocks.

It returns an RLP list of three items, the status as JSON first.

For a valid payload, the RLP form of its header and the accounts of the state after it follow.

For any other payload, two empty lists follow. -/
@[export eth_engine_new_payload_on_chain]
def newPayloadOnChainExport (config state recent request : ByteArray) : Result ByteArray := do
  let config ← configOfJson (← parseJson "config" config)
  -- The chain is an input that the export reads itself, so its errors have code 0.
  let pre ← (Execution.State.Exports.ofInput state).mapError fun e => (0, e.message)
  let recentItems : List Serialization.Rlp.Item ← (Serialization.Rlp.Codec.decode recent).mapError
    fun e => (0, s!"recent blocks rejected: {reprStr e}")
  let recent ← (recentItems.mapM (Execution.Blocks.Exports.recentOfItem config)).mapError
    fun (_, m) => (0, m)
  let request ← parseJson "request" request
  let some method := (request.getObjValAs? String "method").toOption
    | throw (0, "request: no method")
  let some version := newPayloadVersion method | throw (0, s!"no method {method}")
  match newPayloadOnChain ⟨config, pre, recent⟩ version (request.getObjValD "params") with
  | .error e => throw (e.code, s!"engine error: {reprStr e}")
  | .ok (status, reason, next) =>
    let json := Serialization.Rlp.Item.bytes (statusJson status reason).compress.toUTF8
    let (header, accounts) := match next with
      | some (block, post) =>
        (Serialization.Rlp.Codec.toItem block.header,
          Serialization.Rlp.Item.list (post.accounts.toList.map fun (address, account) =>
            Execution.Transactions.Exports.stateEntryItem post address account))
      | none => (.list [], .list [])
    (Serialization.Rlp.encode (.list [json, header, accounts])).mapError
      fun e => (0, s!"result: {reprStr e}")

end EthLib.Engine.Exports
