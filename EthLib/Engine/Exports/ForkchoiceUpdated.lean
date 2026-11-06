module

public import EthLib.Engine.Exports.NewPayload
public import EthLib.Engine.ForkchoiceUpdated

/-!
# `Exports.ForkchoiceUpdated`

The C export of `engine_forkchoiceUpdated`, versions 1 to 3, without payload attributes.

The payload tree and the request cross the boundary as JSON text in UTF-8.

The tree is a list of objects, each with a block hash, a parent hash and a validity flag.

The finalized block that the execution layer knows is a block hash, or `null` for none.

The request is a JSON-RPC request object, with its method and its parameters.

The result is the JSON text of the response: the payload status, and no payload ID.

A JSON-RPC error has the code of its Engine API error: 32602 or 38002.

An unknown method, payload attributes, or input that is not JSON, has code 0.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result)
open EthLib.Base.ChainConfig.Exports (parseJson)
open EthLib.Base

/-- One payload of the tree: its block hash, its parent hash and whether it is valid. -/
def knownOfJson (j : Json) : Result (Hash32 × KnownPayload) := do
  let some valid := (j.getObjValAs? Bool "valid").toOption | throw (0, "tree: no validity")
  let hash (name : String) : Result Hash32 :=
    (Json.fixed name 32 (j.getObjValD name)).mapError fun e => (0, s!"tree: {reprStr e}")
  return (← hash "blockHash", ⟨← hash "parentHash", valid⟩)

/-- The version of a method name `engine_forkchoiceUpdatedV1` to `engine_forkchoiceUpdatedV3`. -/
def forkchoiceUpdatedVersion (method : String) : Option Nat :=
  ["engine_forkchoiceUpdatedV1", "engine_forkchoiceUpdatedV2",
    "engine_forkchoiceUpdatedV3"].idxOf? method |>.map (· + 1)

/-- The response to an `engine_forkchoiceUpdated` request, against a tree of payloads.

The execution layer may know a finalized block, from an earlier update. -/
@[export eth_engine_forkchoice_updated]
def forkchoiceUpdatedExport (tree finalized request : ByteArray) : Result ByteArray := do
  let .arr tree ← parseJson "tree" tree | throw (0, "tree: not an array")
  let tree ← tree.toList.mapM knownOfJson
  let finalized ← parseJson "finalized" finalized
  -- The known finalized block is an input that the export reads itself, so its errors have code 0.
  let finalized : Option Hash32 ← if finalized.isNull then pure none else
    some <$> (Json.fixed "finalized" 32 finalized).mapError fun e => (0, s!"finalized: {reprStr e}")
  let request ← parseJson "request" request
  let some method := (request.getObjValAs? String "method").toOption
    | throw (0, "request: no method")
  let some _ := forkchoiceUpdatedVersion method | throw (0, s!"no method {method}")
  let engine {α : Type} (act : Except EngineError α) : Result α :=
    act.mapError fun e => (e.code, s!"engine error: {reprStr e}")
  let some state ← engine (forkchoiceUpdatedParams (request.getObjValD "params"))
    | throw (0, "payload attributes: building a payload is not specified")
  let (status, _) ← engine (forkchoiceUpdated tree finalized state)
  let response := Json.mkObj [
    ("payloadStatus", statusJson status none),
    ("payloadId", .null)]
  return response.compress.toUTF8

end EthLib.Engine.Exports
