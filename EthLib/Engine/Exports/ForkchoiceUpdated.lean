module

public import EthLib.Engine.Exports.NewPayload
public import EthLib.Engine.ForkchoiceUpdated

/-!
# `Exports.ForkchoiceUpdated`

The C export of `engine_forkchoiceUpdated`, versions 1 to 4, without a payload build.

The payload tree, the finalized block and the request cross as typed Python values.

Each is the value of its JSON.

The tree is a list of objects, each with a block hash, a parent hash and a validity flag.

No two of them have the same block hash.

The finalized block that the execution layer knows is a block hash, or `null` for none.

The request is a JSON-RPC request object, with its method and its parameters.

The result is the value of the JSON of the response: the payload status, and no payload ID.

A JSON-RPC error has the code of its Engine API error: 32602, 38002 or 38003.

Payload attributes on an applied valid head that fit the version have code 0.

They ask for a build, which is not specified.

So do an unknown method and an argument that Lean cannot read.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result PyValue pyExport)
open EthLib.Base

/-- One payload of the tree: its block hash, its parent hash and whether it is valid. -/
def knownOfJson (j : Json) : Result (Hash32 × KnownPayload) := do
  let some valid := (j.getObjValAs? Bool "valid").toOption | throw (0, "tree: no validity")
  let hash (name : String) : Result Hash32 :=
    (Json.fixed name 32 (j.getObjValD name)).mapError fun e => (0, s!"tree: {reprStr e}")
  return (← hash "blockHash", ⟨← hash "parentHash", valid⟩)

/-- The version of a method name `engine_forkchoiceUpdatedV1` to `engine_forkchoiceUpdatedV4`. -/
def forkchoiceUpdatedVersion (method : String) : Option Nat :=
  ["engine_forkchoiceUpdatedV1", "engine_forkchoiceUpdatedV2",
    "engine_forkchoiceUpdatedV3", "engine_forkchoiceUpdatedV4"].idxOf? method |>.map (· + 1)

/-- The response to an `engine_forkchoiceUpdated` request, against a tree of payloads.

The execution layer may know a finalized block, from an earlier update. -/
def forkchoiceUpdatedOf (args : PyValue × PyValue × PyValue) : Result PyValue := do
  let (tree, finalized, request) := args
  let .arr tree := tree.toJson | throw (0, "tree: not an array")
  let tree ← tree.toList.mapM knownOfJson
  -- A tree holds each block once, so two payloads with one block hash are malformed input.
  unless (tree.map (·.1)).Nodup do throw (0, "tree: two payloads with one block hash")
  let finalized := finalized.toJson
  -- The known finalized block is an input that the export reads itself, so its errors have code 0.
  let finalized : Option Hash32 ← if finalized.isNull then pure none else
    some <$> (Json.fixed "finalized" 32 finalized).mapError fun e => (0, s!"finalized: {reprStr e}")
  let request := request.toJson
  let some method := (request.getObjValAs? String "method").toOption
    | throw (0, "request: no method")
  let some version := forkchoiceUpdatedVersion method | throw (0, s!"no method {method}")
  let answer := forkchoiceUpdatedCall version tree finalized (request.getObjValD "params")
  let (status, _, attributes) ← answer.mapError fun e => (e.code, s!"engine error: {reprStr e}")
  -- Step 8: valid attributes on an applied valid head start a build, which is not specified.
  if attributes.isSome then
    throw (0, "payload attributes: building a payload is not specified")
  let response := Json.mkObj [
    ("payloadStatus", statusJson status none),
    ("payloadId", .null)]
  return .ofJson response

/-- The response to an `engine_forkchoiceUpdated` request, against a tree of payloads.

The arguments are the tree, the finalized block that the execution layer knows, and the request. -/
@[export eth_engine_forkchoice_updated]
def forkchoiceUpdatedExport (args : PyValue) : Result PyValue :=
  pyExport forkchoiceUpdatedOf args

end EthLib.Engine.Exports
