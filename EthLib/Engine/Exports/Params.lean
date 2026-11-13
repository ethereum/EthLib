module

public import EthLib.Engine.Exports.ForkchoiceUpdated
public import EthLib.Engine.Exports.GetBlobs
public import EthLib.Engine.Exports.GetPayload
public import EthLib.Engine.Exports.NewPayload
public import EthLib.Engine.Exports.PayloadBodies

/-!
# `Exports.Params`

The C export that reads the parameters of an Engine API request, then writes them back.

It reads them with the decoder of the method, and writes them with the writer of the method.

So it shows in Python what a consensus node sends for the values that it means.

It takes `engine_newPayload`, `engine_forkchoiceUpdated`, `engine_getPayload` and `engine_getBlobs`.

It also takes the two methods of payload bodies, each at every version that EthLib reads.

A payload is written with the structure that it was read with.

An unknown method has code 0.

Parameters that the decoder rejects have the code of their Engine API error.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result PyValue pyExport)
open EthLib.Base
open EthLib.Engine.Json (AnyPayload)

/-- The fork whose payloads have the fields of a version of the structure, from 1 to 3.

Version 1 is that of Paris, 2 of Shapella, and 3 of Dencun. -/
def payloadStructureFork : Nat → Fork
  | 0 | 1 => .paris
  | 2 => .shapella
  | _ => .dencun

/-- The parameters of a version of `engine_newPayload`, read and written back.

A payload of version 4 of the structure is written at Glamsterdam. -/
def rewriteNewPayloadParams (version : Nat) (params : Json) : Except EngineError Json := do
  let (any, amsterdam, hashes, beaconRoot, requests) ← newPayloadParams version params
  let fork := if amsterdam.isSome then .glamsterdam else payloadStructureFork any.version
  let payload ← any.atFork fork
  -- Before version 3 the writer writes neither the hashes nor the root, so any value serves.
  return newPayloadParamsJson version payload amsterdam (hashes.getD [])
    (beaconRoot.getD ZERO_HASH) (requests.getD [])

/-- The parameters of a version of `engine_forkchoiceUpdated`, read and written back.

The attributes are written with the first structure of the version that they fit. -/
def rewriteForkchoiceUpdatedParams (version : Nat) (params : Json) : Except EngineError Json := do
  let (state, attributes) ← forkchoiceUpdatedParams version params
  -- The decoder checked the custody columns, the third value from version 4, then dropped them.
  let custody ← match params with
    | .arr items => custodyColumnsOfJson (items[2]?.getD .null)
    | _ => pure none
  match attributes with
  | none => return forkchoiceUpdatedParamsJson (fork := .paris) version state none custody
  | some j =>
    let ⟨_, attributes⟩ ← payloadAttributesOfVersion version j
    return forkchoiceUpdatedParamsJson version state (some attributes) custody

/-- The parameters of a request to an Engine API method, read and written back.

The method is named in full, such as `engine_newPayloadV3`. -/
def rewriteParamsOf (args : String × PyValue) : Result PyValue := do
  let (method, params) := args
  let params := params.toJson
  let engine (act : Except EngineError Json) : Result PyValue :=
    match act with
    | .ok j => pure (.ofJson j)
    | .error e => throw (e.code, s!"engine error: {reprStr e}")
  if let some version := newPayloadVersion method then
    engine (rewriteNewPayloadParams version params)
  else if let some version := forkchoiceUpdatedVersion method then
    engine (rewriteForkchoiceUpdatedParams version params)
  else if (getPayloadVersion method).isSome then
    engine (getPayloadParamsJson <$> getPayloadParams params)
  else if let some version := getBlobsVersion method then
    engine ((fun (hashes, bits) => getBlobsParamsJson hashes bits) <$>
      getBlobsParams version params)
  else match bodiesMethod method with
    | some (_, false) => engine (bodiesByHashParamsJson <$> bodiesByHashParams params)
    | some (_, true) =>
      engine ((fun (start, count) => bodiesByRangeParamsJson start count) <$>
        bodiesByRangeParams params)
    | none => throw (0, s!"no method {method}")

/-- The parameters of an Engine API request, read by the decoder and written back by the writer.

The arguments are the full name of the method and its parameters.

The parameters are the value of their JSON, as `json.loads` gives it. -/
@[export eth_engine_rewrite_params]
def rewriteParamsExport (args : PyValue) : Result PyValue := pyExport rewriteParamsOf args

end EthLib.Engine.Exports
