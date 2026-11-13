module

public import EthLib.Engine.Exports.NewPayload
public import EthLib.Engine.ForkchoiceUpdated

/-!
# `Exports.ForkchoiceUpdated`

The C export of `engine_forkchoiceUpdated`, versions 1 to 4.

The configuration, the payload tree, the finalized block and the request cross as Python values.

Each is the value of its JSON.

The configuration is an object as for `engine_newPayload`.

It holds the chain ID, the deposit contract address and the activations.

The tree is a list of objects, each with a block hash, a parent hash and a validity flag.

Each also has the number and the timestamp of its block, as quantities.

A block of proof of work also has its total difficulty and that of its parent, as quantities.

They are the fields `totalDifficulty` and `parentTotalDifficulty`, both present or both absent.

Give no totals for a genesis block of a chain that starts at Paris.

The model then treats it as a payload, so its descendants pass the terminal block check.

No two of them have the same block hash.

The finalized block that the execution layer knows is a block hash, or `null` for none.

The terminal total difficulty is a Python integer below `2^256`.

The request is a JSON-RPC request object, with its method and its parameters.

The result is the value of the JSON of the response: the payload status and the payload ID.

A JSON-RPC error has the code of its Engine API error: 32602, 38002, 38003 or 38005.

Payload attributes on an applied valid head that pass every check start a build.

The payload ID is then the ID of that build, from the head and the attributes, and else `null`.

An unknown method and an argument that Lean cannot read have code 0.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result PyValue pyExport)
open EthLib.Base
open EthLib.Base.ChainConfig.Exports (configOfJson)
open EthLib.Serialization.JsonRpc (dataJson fixed uint uint64)

/-- One block of the tree: its block hash, parent hash, validity, number and timestamp.

A block of proof of work also has its total difficulty and that of its parent. -/
def knownOfJson (j : Json) : Result (Hash32 × KnownPayload) := do
  let some valid := (j.getObjValAs? Bool "valid").toOption | throw (0, "tree: no validity")
  let hash (name : String) : Result Hash32 :=
    (fixed name 32 (j.getObjValD name)).mapError fun e =>
      (0, s!"tree: {reprStr (EngineError.invalidParams e)}")
  let number (name : String) : Result UInt64 :=
    (uint64 name (j.getObjValD name)).mapError fun e =>
      (0, s!"tree: {reprStr (EngineError.invalidParams e)}")
  let total (name : String) (v : Json) : Result Nat :=
    (uint name v).mapError fun e => (0, s!"tree: {reprStr (EngineError.invalidParams e)}")
  let pow ← match (j.getObjVal? "totalDifficulty").toOption,
      (j.getObjVal? "parentTotalDifficulty").toOption with
    | some t, some p => pure (some (← total "totalDifficulty" t, ← total "parentTotalDifficulty" p))
    | none, none => pure none
    | _, _ => throw (0, "tree: one total difficulty without the other")
  return (← hash "blockHash",
    ⟨← hash "parentHash", valid, ← number "number", ← number "timestamp", pow⟩)

/-- The version of a method name `engine_forkchoiceUpdatedV1` to `engine_forkchoiceUpdatedV4`. -/
def forkchoiceUpdatedVersion (method : String) : Option Nat :=
  methodVersion "forkchoiceUpdated" method

/-- The response to an `engine_forkchoiceUpdated` request, against a tree of known blocks.

The execution layer may know a finalized block, from an earlier update.

The terminal block hash and number are zero, since the check of the method does not read them. -/
def forkchoiceUpdatedOf (args : PyValue × PyValue × PyValue × Nat × PyValue) :
    Result PyValue := do
  let (config, tree, finalized, terminalTotalDifficulty, request) := args
  unless terminalTotalDifficulty < 2 ^ 256 do
    throw (0, s!"config: a terminal total difficulty of {terminalTotalDifficulty}, not below 2^256")
  let transition : TransitionConfiguration := {
    terminalTotalDifficulty := BitVec.ofNat 256 terminalTotalDifficulty
    terminalBlockHash := 0
    terminalBlockNumber := 0 }
  let config ← configOfJson config.toJson
  let .arr tree := tree.toJson | throw (0, "tree: not an array")
  let tree ← tree.toList.mapM knownOfJson
  -- A tree holds each block once, so two payloads with one block hash are malformed input.
  unless (tree.map (·.1)).Nodup do throw (0, "tree: two payloads with one block hash")
  let finalized := finalized.toJson
  -- The known finalized block is an input that the export reads itself, so its errors have code 0.
  let finalized : Option Hash32 ← if finalized.isNull then pure none else
    some <$> (fixed "finalized" 32 finalized).mapError fun e =>
      (0, s!"finalized: {reprStr (EngineError.invalidParams e)}")
  let request := request.toJson
  let some method := (request.getObjValAs? String "method").toOption
    | throw (0, "request: no method")
  let some version := forkchoiceUpdatedVersion method | throw (0, s!"no method {method}")
  let params := request.getObjValD "params"
  let answer := forkchoiceUpdatedCall config transition version tree finalized params
  let result ← answer.mapError fun e => (e.code, s!"engine error: {reprStr e}")
  -- Step 8: valid attributes on an applied valid head start a build, named by its ID.
  let (status, id) := forkchoiceUpdatedResponse result
  return .ofJson (forkchoiceUpdatedResponseJson status none id)

/-- A forkchoice response read from its JSON: the status name, the hash, the error, the ID.

The hash, the error and the ID are `None` in Python when the JSON has no value for them. -/
def readForkchoiceResponseOf (response : PyValue) :
    Result (String × Option ByteArray × Option String × Option ByteArray) := do
  let (s, e, id) ← (forkchoiceUpdatedResponseOfJson response.toJson).mapError
    fun e => (e.code, s!"engine error: {reprStr e}")
  return (s.status.name, s.latestValidHash.map (⟨·.toArray⟩), e, id.map (⟨·.toArray⟩))

/-- A forkchoice response read from its JSON, as `json.loads` gives it.

The result is the status name, the latest valid hash, the validation error and the payload ID.

A response that does not decode is an invalid parameter, with code 32602. -/
@[export eth_engine_read_forkchoice_response]
def readForkchoiceResponseExport (args : PyValue) : Result PyValue :=
  pyExport readForkchoiceResponseOf args

/-- The response to an `engine_forkchoiceUpdated` request, against a tree of known blocks.

The arguments are the configuration, the tree and the known finalized block.

The terminal total difficulty and the request follow.

The terminal total difficulty must be below `2^256`, or the export raises with code 0. -/
@[export eth_engine_forkchoice_updated]
def forkchoiceUpdatedExport (args : PyValue) : Result PyValue :=
  pyExport forkchoiceUpdatedOf args

end EthLib.Engine.Exports
