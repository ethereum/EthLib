module

public import EthLib.Serialization.JsonRpc

/-!
# `Execution.Rpc.Request`

The request and response objects of [JSON-RPC 2.0][rpc], as the execution JSON-RPC API uses them.

A request holds the version `2.0`, the name of a method, its parameters and an identifier.

The identifier is a string, a number or `null`; the response carries the same one back.

A request without an identifier is a notification, which gets no response.

The reader rejects a request without an identifier.

A server tells a notification apart before it reads a request.

The execution API passes the parameters by position, as an array.

Its fixtures leave out `params` when the array is empty, and the writer does the same.

The reader rejects parameters given by name, a form of JSON-RPC 2.0 that this API never uses.

A response holds either the result of the method or an error object, never both.

A result may be `null`, which a method returns for a block or transaction it does not find.

The readers reject any member that the objects do not define.

That rule is stricter than JSON-RPC 2.0, which does not say what to do with other members.

A request that is not a valid request object has the error `-32600`, as section 5.1 says.

A parameter that breaks its schema has the error `-32602`.

[rpc]: https://www.jsonrpc.org/specification#request_object
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json JsonNumber)
open EthLib.Serialization.JsonRpc

/-- The identifier of a request: a string, a number, or `null`. -/
inductive RequestId where
  /-- A number. -/
  | num (n : JsonNumber)
  /-- A string. -/
  | str (s : String)
  /-- The value `null`. -/
  | null
  deriving DecidableEq, Repr

/-- An identifier as JSON. -/
def requestIdJson : RequestId → Json
  | .num n => .num n
  | .str s => .str s
  | .null => .null

/-- An identifier: a string, a number or `null`. -/
def requestId : Json → Read RequestId
  | .num n => pure (.num n)
  | .str s => pure (.str s)
  | .null => pure .null
  | _ => reject "id: not a string, a number or null"

/-- Whether the member `jsonrpc` of an object is the string `2.0`. -/
def jsonrpcVersion (members : List (String × Json)) : Bool :=
  match members.lookup "jsonrpc" with
  | some (.str v) => v == "2.0"
  | _ => false

/-- A request: a method, its parameters by position, and the identifier of the request. -/
structure Request where
  /-- The identifier, which the response carries back. -/
  id : RequestId
  /-- The name of the method. -/
  method : String
  /-- The parameters, by position. -/
  params : List Json := []

/-- A request as JSON, without `params` when there are none. -/
def requestJson (r : Request) : Json :=
  Json.mkObj ([("jsonrpc", .str "2.0"), ("id", requestIdJson r.id), ("method", .str r.method)] ++
    if r.params.isEmpty then [] else [("params", .arr r.params.toArray)])

/-- A request object: the version `2.0`, an identifier, a method, and optional parameters. -/
def request : Json → Read Request
  | .obj kvs => do
    let members := kvs.toList
    unless members.all fun (k, _) => k == "jsonrpc" || k == "id" || k == "method" || k == "params"
      do reject "request: a member other than jsonrpc, id, method and params"
    unless jsonrpcVersion members do reject "request: jsonrpc is not 2.0"
    let id ← requestId (← field "request" members "id")
    let method ← string "method" (← field "request" members "method")
    let params ← match members.lookup "params" with
      | none => pure []
      | some (.arr items) => pure items.toList
      | some _ => reject "params: not an array"
    return { id, method, params }
  | _ => reject "request: not an object"

/-- A response: the identifier of its request, and the result or the error. -/
structure Response where
  /-- The identifier of the request. -/
  id : RequestId
  /-- The result of the method, or the error that it failed with. -/
  outcome : Except RpcError Json

/-- A response as JSON. -/
def responseJson (r : Response) : Json :=
  Json.mkObj [("jsonrpc", .str "2.0"), ("id", requestIdJson r.id),
    match r.outcome with
    | .ok result => ("result", result)
    | .error e => ("error", rpcErrorJson e)]

/-- A response object: the version `2.0`, an identifier, and exactly one of result and error. -/
def response : Json → Read Response
  | .obj kvs => do
    let members := kvs.toList
    unless members.length = 3 do reject "response: not exactly three members"
    unless jsonrpcVersion members do reject "response: jsonrpc is not 2.0"
    let id ← requestId (← field "response" members "id")
    match members.lookup "result", members.lookup "error" with
    | some result, none => return { id, outcome := .ok result }
    | none, some e => return { id, outcome := .error (← rpcErrorOfJson e) }
    | _, _ => reject "response: not exactly one of result and error"
  | _ => reject "response: not an object"

end EthLib.Execution.Rpc
