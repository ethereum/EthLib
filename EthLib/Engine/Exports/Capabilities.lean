module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Engine.Capabilities

/-!
# `Exports.Capabilities`

The C exports of `engine_exchangeCapabilities` and `engine_getClientVersionV1`.

Each request is a JSON-RPC request object, with its method and its parameters.

The result is the JSON answer, as a Python value.

An execution node built on EthLib answers the names of the methods that EthLib defines.

The version object of the execution node crosses as its four fields.

A JSON-RPC error has the code of its Engine API error, without the sign: 32602.

A request without a method, or with another method, has code 0.

So do a code of the node that is not two letters, and an argument that Lean cannot read.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result PyValue pyExport)
open EthLib.Base
open EthLib.Serialization.JsonRpc (listJson)

/-- The parameters of a request for a method, which the test must accept. -/
def paramsOfMethod (accepts : String → Bool) (request : PyValue) : Result Json := do
  let request := request.toJson
  let some method := (request.getObjValAs? String "method").toOption
    | throw (0, "request: no method")
  unless accepts method do throw (0, s!"no method {method}")
  return request.getObjValD "params"

/-- The answer to the request, at an execution node that supports the methods of EthLib. -/
def exchangeCapabilitiesOf (request : PyValue) : Result PyValue := do
  let params ← paramsOfMethod (· == "engine_exchangeCapabilities") request
  let answer ← (exchangeCapabilities specifiedMethods params).mapError
    fun e => (e.code, s!"engine error: {reprStr e}")
  return .ofJson (listJson .str answer)

/-- The answer to an `engine_exchangeCapabilities` request: the methods that EthLib defines.

The argument is the request. -/
@[export eth_engine_exchange_capabilities]
def exchangeCapabilitiesExport (args : PyValue) : Result PyValue :=
  pyExport exchangeCapabilitiesOf args

/-- The answer to the request, at an execution node with a version object.

The arguments are the four fields of the object and the request. -/
def getClientVersionOf (args : String × String × String × Vector UInt8 4 × PyValue) :
    Result PyValue := do
  let (code, name, version, commit, request) := args
  unless decide (IsClientCode code) do throw (0, s!"own: a code {code}, not two letters")
  let params ← paramsOfMethod (methodVersion "getClientVersion" · == some 1) request
  let answer ← (getClientVersion { code, name, version, commit } params).mapError
    fun e => (e.code, s!"engine error: {reprStr e}")
  return .ofJson (clientVersionsJson answer)

/-- The answer to an `engine_getClientVersionV1` request, from a version object.

The arguments are the code, name, version and commit of the object, and the request. -/
@[export eth_engine_get_client_version]
def getClientVersionExport (args : PyValue) : Result PyValue :=
  pyExport getClientVersionOf args

end EthLib.Engine.Exports
