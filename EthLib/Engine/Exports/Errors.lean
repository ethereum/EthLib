module

public import EthLib.Base.Exports.PyValue
public import EthLib.Engine.Json

/-!
# `Exports.Errors`

The C export of the error object of each Engine API error, by its code.

The code crosses without its sign, as the codes of the Engine API errors do.
-/

public section

namespace EthLib.Engine.Exports

open EthLib.Exports (Result PyValue pyExport)
open EthLib.Serialization.JsonRpc (rpcErrorJson)

/-- One error of each constructor.

The fields of an error do not reach its error object, so any value of them serves. -/
def engineErrors : List EngineError :=
  [.invalidParams "", .unknownPayload (Vector.replicate 8 0),
    .invalidForkchoiceState (Vector.replicate 32 0) (Vector.replicate 32 0),
    .invalidPayloadAttributes, .tooLargeRequest 0 0, .unsupportedFork none, .tooDeepReorg]

/-- The error of a code, among one error of each constructor, or none for another code. -/
def engineErrorOfCode (code : UInt32) : Option EngineError :=
  engineErrors.find? (·.code == code)

/-- The error object of the Engine API error with a code, as JSON text. -/
def errorObjectOf (code : UInt32) : Result String := do
  let some e := engineErrorOfCode code | throw (0, s!"no Engine API error has the code {code}")
  return (rpcErrorJson e.toRpcError).compress

/-- The error object of the Engine API error with a code: its negative code, message and data.

The argument is the code without its sign, such as 38006.

The result is the JSON text of the object, as a response carries it.

The data is `null`, since only `-32000` carries data, and no Engine API error has that code.

A code of no Engine API error raises with code 0. -/
@[export eth_engine_error_object]
def errorObjectExport (args : PyValue) : Result PyValue :=
  pyExport errorObjectOf args

end EthLib.Engine.Exports
