module

public import EthLib.Base.Exports.PyValue
public import EthLib.Engine.Capabilities
public import EthLib.Engine.Exports.Errors

/-!
# `Exports.Capabilities`

The C exports of `engine_exchangeCapabilities` and `engine_getClientVersionV1`.

Each request is a JSON-RPC request object, with its method and its parameters.

The result is the JSON answer, as a Python value.

A JSON-RPC error has the code of its Engine API error, without the sign: 32602.

An argument that Lean cannot read has code 0.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result PyValue pyExport rejectArgument toResult)
open EthLib.Base
open EthLib.Serialization.JsonRpc (listJson)

/-- The parameters of a request for a method, which the test must accept. -/
def paramsOfMethod (accepts : String → Bool) (request : PyValue) : Result Json := do
  let request := request.toJson
  -- A request without a method, or with another method, has code 0.
  let some method := (request.getObjValAs? String "method").toOption
    | rejectArgument none "request: no method"
  unless accepts method do rejectArgument none s!"no method {method}"
  return request.getObjValD "params"

/-- The answer to the request, at an execution node that supports the methods of EthLib. -/
def exchangeCapabilitiesOf (request : PyValue) : Result PyValue := do
  let params ← paramsOfMethod (· == "engine_exchangeCapabilities") request
  -- An execution node built on EthLib answers the names of the methods that EthLib defines.
  let answer ← toResult "engine error" (exchangeCapabilities specifiedMethods params)
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
  -- The version object of the execution node crosses as its four fields.
  let (code, name, version, commit, request) := args
  -- A code of the node that is not two letters has code 0.
  unless decide (IsClientCode code) do
    rejectArgument none s!"own: a code {code}, not two letters"
  let params ← paramsOfMethod (methodVersion "getClientVersion" · == some 1) request
  let answer ← toResult "engine error" (getClientVersion { code, name, version, commit } params)
  return .ofJson (clientVersionsJson answer)

/-- The answer to an `engine_getClientVersionV1` request, from a version object.

The arguments are the code, name, version and commit of the object, and the request. -/
@[export eth_engine_get_client_version]
def getClientVersionExport (args : PyValue) : Result PyValue :=
  pyExport getClientVersionOf args

end EthLib.Engine.Exports
