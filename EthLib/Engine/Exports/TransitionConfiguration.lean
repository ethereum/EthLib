module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Engine.Capabilities
public import EthLib.Engine.TransitionConfiguration

/-!
# `Exports.TransitionConfiguration`

The C export of `engine_exchangeTransitionConfigurationV1`.

The configuration of the execution node crosses as its three values.

They are the terminal total difficulty, the terminal block hash and the terminal block number.

The request is a JSON-RPC request object, with its method and its parameters.

The result is the JSON answer, as a Python value.

A JSON-RPC error has the code of its Engine API error, without the sign: 32602.

A total difficulty of at least `2^256`, or a block number of at least `2^64`, has code 0.

A request without a method, or with another method, also has code 0.

So does an argument that Lean cannot read.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result PyValue pyExport)
open EthLib.Base

/-- The answer to the request, at an execution node with a configuration.

The arguments are the three values of the configuration and the request. -/
def exchangeTransitionConfigurationOf (args : Nat × Bytes32 × Nat × PyValue) :
    Result PyValue := do
  let (difficulty, hash, number, request) := args
  unless difficulty < 2 ^ 256 do
    throw (0, s!"config: a total difficulty of {difficulty}, not below 2^256")
  unless number < 2 ^ 64 do throw (0, s!"config: a block number of {number}, not below 2^64")
  let own : TransitionConfiguration := {
    terminalTotalDifficulty := BitVec.ofNat 256 difficulty
    terminalBlockHash := hash
    terminalBlockNumber := number.toUInt64 }
  let request := request.toJson
  let some method := (request.getObjValAs? String "method").toOption
    | throw (0, "request: no method")
  unless methodVersion "exchangeTransitionConfiguration" method = some 1 do
    throw (0, s!"no method {method}")
  let answer ← (exchangeTransitionConfiguration own (request.getObjValD "params")).mapError
    fun e => (e.code, s!"engine error: {reprStr e}")
  return .ofJson (transitionConfigurationJson answer)

/-- The answer to an `engine_exchangeTransitionConfigurationV1` request, from a configuration.

The arguments are the terminal total difficulty, block hash and block number, and the request. -/
@[export eth_engine_exchange_transition_configuration]
def exchangeTransitionConfigurationExport (args : PyValue) : Result PyValue :=
  pyExport exchangeTransitionConfigurationOf args

end EthLib.Engine.Exports
