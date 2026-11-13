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

So Python can compare a request with the canonical JSON of the values that it holds.

A payload is written with the structure that it was read with.

An unknown method raises an error of code 0, and rejected parameters the code of their error.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result PyValue pyExport)
open EthLib.Base
open EthLib.Engine.Json (AnyPayload)

/-- A fork that a version of `engine_newPayload` takes, with payloads of a version of the structure.

Version 5 takes Glamsterdam, and version 4 Pectra, whose payloads have version 3 of the structure.

Below, version 1 of the structure is that of Paris, 2 of Shapella, and 3 of Dencun. -/
def payloadFork (version layout : Nat) : Fork :=
  if 5 ≤ version then .glamsterdam
  else if version = 4 then .pectra
  else match layout with
    | 0 | 1 => .paris
    | 2 => .shapella
    | _ => .dencun

/-- The parameters of a version of `engine_newPayload`, read and written back.

The payload is written with the structure it was read with, at a fork that the version takes. -/
def rewriteNewPayloadParams (version : Nat) (params : Json) : Except EngineError Json := do
  let (any, amsterdam, hashes, beaconRoot, requests) ← newPayloadParams version params
  let payload ← any.atFork (payloadFork version any.version)
  -- The writer leaves out the hashes and the root before version 3, and the requests before 4.
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

/-- The parameters of an Engine API request, read by the decoder and written by the writer.

The arguments are the full name of the method and its parameters.

The parameters are the value of their JSON, as `json.loads` gives it. -/
@[export eth_engine_rewrite_params]
def rewriteParamsExport (args : PyValue) : Result PyValue := pyExport rewriteParamsOf args

end EthLib.Engine.Exports
