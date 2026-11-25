module

public import EthLib.Engine.Exports.ForkchoiceUpdated
public import EthLib.Engine.Exports.GetPayload
public import EthLib.Engine.Node.View
public import EthLib.Execution.Rpc.Methods

/-!
# `Exports.Node`

The C export of an execution node that runs a script of Engine API requests.

The node starts from one block, valid, as its head, with the state after it.

The result has one object per request, with the response and the forkchoice state of the node.

An unknown Engine API method, an argument that Lean cannot read, or an answer with no JSON, raises.

Its code is then 0, as for a JSON-RPC request with no ID.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result PyValue UnreadArgument pyExport rejectArgument toResult)
open EthLib.Base
open EthLib.Cryptography.Kzg (TrustedSetup)
open EthLib.Serialization.JsonRpc (rpcErrorJson)

/-- The response to a request: its result, or the error object of its Engine API error. -/
def responseJson (answer : Except EngineError Json) : Json :=
  match answer with
  | .ok result => Json.mkObj [("result", result)]
  | .error e => Json.mkObj [("error", rpcErrorJson e.toRpcError)]

/-- The builder of this export: the suggested fee recipient, no extra data and no transaction.

Its target gas limit, which counts only before Glamsterdam, is 30000000, a choice of this export.
-/
def exportBuilder : Node.Builder := fun attributes =>
  (⟨attributes.2.suggestedFeeRecipient, ByteArray.empty, 30000000⟩, [])

/-- The response to a request on a node, and the node after it.

The result of the method is written as its export writes it. -/
def nodeCall (setup : TrustedSetup) (node : Node) (request : Json) : Result (Json × Node) := do
  let some method := (request.getObjValAs? String "method").toOption
    | rejectArgument none "request: no method"
  let params := request.getObjValD "params"
  -- The methods are `engine_newPayload`, `engine_forkchoiceUpdated` and `engine_getPayload`.
  --
  -- A valid status of version 6 has no JSON here, so it raises.
  --
  -- It needs the inclusion list verdict of Bogota, whose execution rules are not here yet.
  if let some version := newPayloadVersion method then
    let (answer, next) := node.newPayloadStep version params
    let answer ← match answer with
      | .ok (status, reason) => .ok <$> statusJson version status reason
      | .error e => pure (.error e)
    return (responseJson answer, next)
  -- An update that starts a build stores it, and a request for its ID returns it.
  if let some version := forkchoiceUpdatedVersion method then
    let (answer, next) := node.forkchoiceUpdatedBuildStep exportBuilder version params
    let answer ← match answer with
      | .ok (status, id) =>
        if version < 5 then pure (.ok (forkchoiceUpdatedResponseJson status none id))
        -- A valid head at version 5 also needs that verdict, so it raises.
        else if status.status = .valid then
          rejectArgument none "no inclusion list verdict: Bogota does not run here"
        else pure (.ok (forkchoiceUpdatedResponseV2Json status none none id))
      | .error e => pure (.error e)
    return (responseJson answer, next)
  if let some version := getPayloadVersion method then
    let answer ← match getPayloadParams params with
      | .error e => pure (.error e)
      | .ok id =>
        match (node.getPayloadStep setup version id).1 with
        | .ok r => pure (.ok (getPayloadResultJson (r.result version)))
        | .error (.engine e) => pure (.error e)
        | .error e => toResult none (.error e)
    return (responseJson answer, node)
  -- A request whose method starts with `eth_` goes to the JSON-RPC API, on the chain view.
  --
  -- Its network ID is the chain ID, and a node that gives no chain view raises.
  if method.startsWith "eth_" then
    let some view := node.view node.config.chainId.toNat setup
      | rejectArgument none "the node gives no chain view"
    -- Its response is the whole response object of that API.
    --
    -- An unknown method of the JSON-RPC API gets the error object of that API.
    let some response := view.serve (.ok request)
      | rejectArgument none "request: a notification"
    return (response, node)
  rejectArgument none s!"no method {method}"

/-- The responses to a script of requests, from a node that knows one block.

The arguments are the chain configuration, the state after the block, and the block.

The block is the fork name, the header and its ommers, the header and each ommer in RLP form.

Then come the terminal total difficulty, the total difficulty of the block and the requests. -/
def runNodeOf (args : PyValue × ByteArray × (String × ByteArray × List ByteArray) × Nat × Nat ×
    PyValue) : Result PyValue := do
  let (config, state, anchor, terminalTotalDifficulty, totalDifficulty, requests) := args
  -- A block of proof of work also takes its total difficulty, and the terminal one.
  let transition ← transitionOf terminalTotalDifficulty
  -- The configuration, the state and the block take the forms of the export on a chain.
  let chain ← Execution.Blocks.Exports.chainOf config state [anchor]
  let some block := chain.recent.head? | rejectArgument none "anchor: no block"
  -- The block crosses without its body, so its header must commit to an empty body.
  --
  -- Its header must also commit to its ommers.
  --
  -- An empty body is no transaction and, from Shapella, no withdrawal.
  let some node := Node.start chain.config transition block chain.state totalDifficulty
    | rejectArgument none
        "anchor: no hash, a body that is not empty, or a total below the difficulty"
  let .arr requests := requests.toJson | rejectArgument none "requests: not an array"
  let setup ← toResult none ((Cryptography.Kzg.Exports.embeddedSetup ()).mapError
    fun e => UnreadArgument.mk s!"setup: {e.message}")
  -- Each request is a JSON-RPC request object.
  --
  -- The requests run in order, each on the node that the requests before it left.
  let (_, out) ← requests.toList.foldlM (init := (node, #[])) fun (node, out) request => do
    let (response, next) ← nodeCall setup node request
    -- The response has the result of the method, or its error object with the negative code.
    --
    -- The forkchoice state is that of the node after the request.
    return (next, out.push (Json.mkObj [("response", response),
      ("forkchoice", forkchoiceStateJson next.forkchoice)]))
  return .ofJson (.arr out)

/-- The responses to a script of Engine API requests, from a node that knows one block.

The arguments are the configuration, the state after the block and the block.

Then come the two totals and the requests.

The result has the response and the forkchoice state of the node after each request. -/
@[export eth_engine_run_node]
def runNodeExport (args : PyValue) : Result PyValue := pyExport runNodeOf args

end EthLib.Engine.Exports
