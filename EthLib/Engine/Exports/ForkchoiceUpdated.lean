module

public import EthLib.Engine.Exports.NewPayload
public import EthLib.Engine.ForkchoiceUpdated

/-!
# `Exports.ForkchoiceUpdated`

The C export of `engine_forkchoiceUpdated`, versions 1 to 5.

The configuration, the payload tree, the finalized block and the request cross as Python values.

Each is the value of its JSON.

The result is the value of the JSON of the response: the payload status and the payload ID.

An argument that Lean cannot read has code 0.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result PyValue UnreadArgument pyExport rejectArgument toResult)
open EthLib.Base
open EthLib.Base.ChainConfig.Exports (configOfJson)
open EthLib.Serialization.JsonRpc (dataJson fixed uint)

/-- One block of the tree: its block hash, parent hash, validity, number and timestamp.

A block of proof of work also has its total difficulty and that of its parent. -/
def knownOfJson (j : Json) : Result (Hash32 × KnownPayload) := do
  -- The validity flag is a boolean.
  let some valid := (j.getObjValAs? Bool "valid").toOption
    | rejectArgument none "tree: no validity"
  -- The tree is an input that the export reads itself, so its errors have code 0.
  let unread (e : String) : UnreadArgument :=
    ⟨s!"tree: {reprStr (EngineError.invalidParams e)}"⟩
  let hash (name : String) : Result Hash32 :=
    toResult none ((fixed name 32 (j.getObjValD name)).mapError unread)
  -- The number and the timestamp of the block are quantities.
  let number (name : String) : Result Nat :=
    toResult none ((uint name (j.getObjValD name)).mapError unread)
  let total (name : String) (v : Json) : Result Nat :=
    toResult none ((uint name v).mapError unread)
  -- A block of proof of work also has its total difficulty and that of its parent, as quantities.
  --
  -- They are both present or both absent.
  --
  -- Give no totals for a genesis block of a chain that starts at Paris.
  --
  -- The model then treats it as a payload, so its descendants pass the terminal block check.
  let pow ← match (j.getObjVal? "totalDifficulty").toOption,
      (j.getObjVal? "parentTotalDifficulty").toOption with
    | some t, some p => pure (some (← total "totalDifficulty" t, ← total "parentTotalDifficulty" p))
    | none, none => pure none
    | _, _ => rejectArgument none "tree: one total difficulty without the other"
  return (← hash "blockHash",
    ⟨← hash "parentHash", valid, ← number "number", ← number "timestamp", pow⟩)

/-- The version of a method name `engine_forkchoiceUpdatedV1` to `engine_forkchoiceUpdatedV5`. -/
def forkchoiceUpdatedVersion (method : String) : Option Nat :=
  methodVersion "forkchoiceUpdated" method

/-- The response to an `engine_forkchoiceUpdated` request, against a tree of known blocks.

The execution layer may know a finalized block, from an earlier update.

The terminal block hash and number are zero, since the check of the method does not read them. -/
def forkchoiceUpdatedOf (args : PyValue × PyValue × PyValue × Nat × PyValue) :
    Result PyValue := do
  let (config, tree, finalized, terminalTotalDifficulty, request) := args
  -- The terminal total difficulty is a Python integer below `2^256`.
  unless terminalTotalDifficulty < 2 ^ 256 do
    rejectArgument none
      s!"config: a terminal total difficulty of {terminalTotalDifficulty}, not below 2^256"
  let transition : TransitionConfiguration := {
    terminalTotalDifficulty := BitVec.ofNat 256 terminalTotalDifficulty
    terminalBlockHash := 0
    terminalBlockNumber := 0 }
  -- The configuration is an object as for `engine_newPayload`.
  --
  -- It holds the chain ID, the deposit contract address and the activations.
  let config ← configOfJson config.toJson
  -- The tree is a list of objects, one per block.
  let .arr entries := tree.toJson | rejectArgument none "tree: not an array"
  let tree ← entries.toList.mapM knownOfJson
  -- A tree holds each block once, so two payloads with one block hash are malformed input.
  unless (tree.map (·.1)).Nodup do rejectArgument none "tree: two payloads with one block hash"
  -- The finalized block that the execution layer knows is a block hash, or `null` for none.
  let finalized := finalized.toJson
  -- The known finalized block is an input that the export reads itself, so its errors have code 0.
  let finalized : Option Hash32 ← if finalized.isNull then pure none else
    some <$> toResult none ((fixed "finalized" 32 finalized).mapError fun e =>
      UnreadArgument.mk s!"finalized: {reprStr (EngineError.invalidParams e)}")
  -- The request is a JSON-RPC request object, with its method and its parameters.
  let request := request.toJson
  let some method := (request.getObjValAs? String "method").toOption
    | rejectArgument none "request: no method"
  -- An unknown method has code 0.
  let some version := forkchoiceUpdatedVersion method
    | rejectArgument none s!"no method {method}"
  let params := request.getObjValD "params"
  let answer := forkchoiceUpdatedCall config transition version tree finalized params
  -- A JSON-RPC error has the code of its Engine API error: 32602, 38002, 38003 or 38005.
  let result ← toResult "engine error" answer
  -- Step 8: valid attributes on an applied valid head start a build, named by its ID.
  --
  -- The payload ID is that of the build, from the head and the attributes, and else `null`.
  let (status, id) := forkchoiceUpdatedResponse result
  if version < 5 then return .ofJson (forkchoiceUpdatedResponseJson status none id)
  -- Step 2 of version 5: a valid head carries its inclusion list verdict, read from the tree.
  --
  -- That verdict is the boolean `inclusionListSatisfied`, which a valid head must give.
  --
  -- The verdict is an input, since the execution rules of Bogota are not in this library yet.
  --
  -- From version 5 the payload status has version 2, with the verdict of the head or `null`.
  let satisfied ← if status.status = .valid then do
      let head := (forkchoiceUpdatedParams version params).toOption.map (·.1.headBlockHash)
      let entry := (entries.toList.zip tree).find? fun (_, (hash, _)) => some hash = head
      let some verdict :=
          entry.bind fun (j, _) => (j.getObjValAs? Bool "inclusionListSatisfied").toOption
        | rejectArgument none "tree: no inclusion list verdict for the valid head"
      pure verdict
    else pure false
  return .ofJson (forkchoiceUpdatedResponseV2Json status none
    (inclusionListVerdict status satisfied) id)

/-- A forkchoice response read from its JSON: the status name, the hash, the error, the ID.

The hash, the error and the ID are `None` in Python when the JSON has no value for them. -/
def readForkchoiceResponseOf (response : PyValue) :
    Result (String × Option ByteArray × Option String × Option ByteArray) := do
  let (s, e, id) ← toResult "engine error" (forkchoiceUpdatedResponseOfJson response.toJson)
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
