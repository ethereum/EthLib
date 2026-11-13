module

public import EthLib.Execution.Rpc.Header
public import EthLib.Execution.Rpc.Request
public import EthLib.Execution.Rpc.TransactionInfo

/-!
# `Execution.Rpc.Methods`

The methods of the execution JSON-RPC API that the node serves, each a function of its chain view.

The node answers a request by the method that it names, with the parameters by position.

A method that the node does not serve has the error `-32601` of [JSON-RPC 2.0][rpc].

A method takes the parameters that its schema in [`src/eth`][eth] lists.

The source does not say what a method does with more, and here a method rejects them with `-32602`.

A text that is not JSON has the error `-32700`, and a value that is not a request `-32600`.

Parameters by name are a request of JSON-RPC 2.0 that this API never uses, and get `-32600`.

The response to an invalid request carries its identifier if it can be read, else `null`.

A notification, a request without an identifier, gets no response, as section 4.1 says.

A batch, an array of requests, gets the array of the responses to its requests, as section 6 says.

An empty batch is an invalid request, and a batch of notifications gets no response.

A missing parameter, or a parameter that its reader rejects, also gets `-32602`.

A transaction whose sender or hash the node cannot compute gets `-32603`.

[rpc]: https://www.jsonrpc.org/specification#error_object
[eth]: https://github.com/ethereum/execution-apis/tree/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/eth
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base (Hash32)
open EthLib.Serialization.JsonRpc

namespace ChainView

/-- The number of the head, as `eth_blockNumber` returns it. -/
def blockNumber (v : ChainView) : Json :=
  quantityJson v.head.block.header.number

/-- The chain ID of the configuration, as `eth_chainId` returns it. -/
def chainId (v : ChainView) : Json :=
  quantityJson v.config.chainId.toNat

/-- The network ID, as `net_version` returns it, in decimal.

The schema of the method says that it is usually the chain ID, but may differ from it. -/
def netVersion (v : ChainView) : Json :=
  uintDecimalJson v.networkId

/-- The result of a method with no parameter, or the error of extra parameters. -/
def noParams (params : List Json) (result : Json) : Except RpcError Json :=
  if params.isEmpty then .ok result
  else .error (RpcError.invalidParams "the method takes no parameter")

/-- A parameter that a reader reads, or the error of invalid parameters. -/
def readParam {α : Type} (reader : Json → Read α) (j : Json) : Except RpcError α :=
  (reader j).mapError RpcError.invalidParams

/-- The result of a method with one parameter, or the error of a missing or extra parameter. -/
def oneParam (params : List Json) (f : Json → Except RpcError Json) : Except RpcError Json :=
  match params with
  | [a] => f a
  | [] => .error (RpcError.invalidParams "missing parameter")
  | _ => .error (RpcError.invalidParams "the method takes one parameter")

/-- The result of a method with two parameters, or the error of a missing or extra parameter. -/
def twoParams (params : List Json) (f : Json → Json → Except RpcError Json) :
    Except RpcError Json :=
  match params with
  | [a, b] => f a b
  | [] | [_] => .error (RpcError.invalidParams "missing parameter")
  | _ => .error (RpcError.invalidParams "the method takes two parameters")

/-- A transaction of a block as JSON, or `null` when there is none. -/
def transactionResult (r : Except RpcError (Option TransactionInfo)) : Except RpcError Json :=
  optionJson transactionInfoJson <$> r

/-- The header object of a block that the node holds, with the hash that the node keeps for it. -/
def headerObject (r : BlockRecord) : Json :=
  Json.mkObj (headerFields r.hash r.block.header)

/-- The header of the block of a hash, canonical or not, or `null` when the node holds none. -/
def headerByHash (v : ChainView) (hash : Hash32) : Json :=
  optionJson headerObject (v.byHash hash)

/-- The header of the block that a number or a tag names, or `null` when there is none.

The tag `pending` gives `null`, as the method says. -/
def headerByNumber (v : ChainView) : BlockParam → Except RpcError Json
  | .tag .pending => .ok notFound
  | p => optionJson headerObject <$> v.resolve p

/-- The outcome of a method of the view, with its parameters by position. -/
def call (v : ChainView) (method : String) (params : List Json) : Except RpcError Json :=
  match method with
  | "eth_blockNumber" => noParams params v.blockNumber
  | "eth_chainId" => noParams params v.chainId
  | "net_version" => noParams params v.netVersion
  | "eth_getTransactionByHash" => oneParam params fun h => do
    transactionResult (v.transactionByHash (← readParam (hash32 "transaction hash") h))
  | "eth_getTransactionByBlockHashAndIndex" => twoParams params fun h i => do
    let block := BlockParam.hash (← readParam (hash32 "block hash") h) false
    transactionResult (v.transactionByBlockAndIndex block (← readParam (uint "index") i))
  | "eth_getTransactionByBlockNumberAndIndex" => twoParams params fun b i => do
    let block ← readParam (blockNumberOrTag "block") b
    transactionResult (v.transactionByBlockAndIndex block (← readParam (uint "index") i))
  | "eth_getHeaderByHash" => oneParam params fun h => do
    return v.headerByHash (← readParam (hash32 "block hash") h)
  | "eth_getHeaderByNumber" => oneParam params fun b => do
    v.headerByNumber (← readParam (blockNumberOrTag "block") b)
  | _ => .error (methodNotFound.toRpcError (some (.str method)))

/-- The response of the view to a request. -/
def answer (v : ChainView) (r : Request) : Response :=
  { id := r.id, outcome := v.call r.method r.params }

/-- The identifier of a JSON value that is not a valid request, if it has one, else `null`. -/
def idOf : Json → RequestId
  | .obj kvs => match kvs.toList.lookup "id" with
    | some j => (requestId j).toOption.getD .null
    | none => .null
  | _ => .null

/-- Whether a JSON value is a notification: an object of version `2.0` with a method, no id. -/
def isNotification : Json → Bool
  | .obj kvs =>
    let members := kvs.toList
    (members.lookup "id").isNone && jsonrpcVersion members &&
      match members.lookup "method" with
      | some (.str _) => true
      | _ => false
  | _ => false

/-- The response of the view to one JSON value, or none for a notification. -/
def answerJson (v : ChainView) (j : Json) : Option Json :=
  if isNotification j then none
  else some <| responseJson <| match request j with
    | .error reason => { id := idOf j, outcome := .error (RpcError.invalidRequest reason) }
    | .ok r => v.answer r

/-- The response of the view to the text of a request or a batch, as JSON, or none.

A batch gets the array of the responses to its requests, and none when all are notifications. -/
def serve (v : ChainView) (text : String) : Option Json :=
  match Json.parse text with
  | .error reason => some <| responseJson
      { id := .null, outcome := .error (parseError.toRpcError (some (.str reason))) }
  | .ok (.arr items) =>
    if items.isEmpty then
      some <| responseJson
        { id := .null, outcome := .error (RpcError.invalidRequest "batch: empty array") }
    else
      let responses := items.toList.filterMap v.answerJson
      if responses.isEmpty then none else some (.arr responses.toArray)
  | .ok j => v.answerJson j

end ChainView

end EthLib.Execution.Rpc
