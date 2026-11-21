module

public import EthLib.Engine.Exports.Capabilities
public import EthLib.Engine.GetInclusionList

/-!
# `Exports.GetInclusionList`

The C export of `engine_getInclusionListV1`.

The candidates of the node cross as a list of byte strings, in the order that the node prefers.

The request is a JSON-RPC request object, with its method and its parameters.

The result is the JSON answer, an array of byte strings, as a Python value.

A JSON-RPC error has the code of its Engine API error, without the sign: 32602.

A request without a method, or with another method, has code 0.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result PyValue pyExport toResult)

/-- The answer to the request, from the candidates of the node. -/
def getInclusionListOf (args : List ByteArray × PyValue) : Result PyValue := do
  let (candidates, request) := args
  let params ← paramsOfMethod (· == "engine_getInclusionListV1") request
  let answer ← toResult "engine error" (getInclusionList candidates params)
  return .ofJson (Json.inclusionListJson answer)

/-- The answer to an `engine_getInclusionListV1` request, from the candidates of the node.

The arguments are the candidates, in the order that the node prefers, and the request. -/
@[export eth_engine_get_inclusion_list]
def getInclusionListExport (args : PyValue) : Result PyValue :=
  pyExport getInclusionListOf args

end EthLib.Engine.Exports
