module

public import EthLib.Base.Exports
public import EthLib.Base.Hex
public import EthLib.Engine.NewPayload

/-!
# `Exports.NewPayload`

The C export of `engine_newPayload`, for an execution layer without the parent's state.

The chain configuration and the request cross the boundary as JSON text in UTF-8.

The configuration is an object with the chain ID and the activations.

Each activation is a list of a fork name, `block` or `time`, and a number.

The request is a JSON-RPC request object, with its method and its parameters.

The result is the JSON text of the payload status.

Its validation error starts with the code of the reason, then a colon.

A JSON-RPC error has the code of its Engine API error: 32602 or 38005.

An unknown method, or input that is not JSON, has code 0.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result forkOfName)
open EthLib.Base

/-- The JSON value of some UTF-8 text. -/
def parseJson (what : String) (text : ByteArray) : Result Json := do
  let some text := String.fromUTF8? text | throw (0, s!"{what} is not UTF-8")
  match Json.parse text with
  | .ok j => pure j
  | .error e => throw (0, s!"{what} is not JSON: {e}")

/-- One activation of a configuration: a fork name, `block` or `time`, and a number. -/
def activationOfJson (j : Json) : Result (Fork × Activation) := do
  let .arr #[.str name, .str kind, n] := j | throw (0, "an activation is not [fork, kind, n]")
  let fork ← forkOfName name.toUTF8
  let some n := n.getNat?.toOption | throw (0, "an activation has no number")
  match kind with
  | "block" => pure (fork, .block n)
  | "time" => pure (fork, .time n)
  | _ => throw (0, s!"no activation kind {kind}")

/-- A chain configuration given as JSON. -/
def configOfJson (j : Json) : Result ChainConfig := do
  let some chainId := (j.getObjValAs? Nat "chainId").toOption | throw (0, "config: no chainId")
  let .arr activations := j.getObjValD "activations" | throw (0, "config: no activations")
  let activations ← activations.toList.mapM activationOfJson
  return ⟨BitVec.ofNat 256 chainId, activations⟩

/-- Bytes as lowercase hex behind `0x`. -/
def hex (bytes : List UInt8) : String :=
  bytes.foldl (init := "0x") fun s b =>
    (s.push hexAlphabet[b.toNat >>> 4]!).push hexAlphabet[b.toNat &&& 15]!

/-- A message for the reason of an invalid payload, on one line. -/
def reasonMessage : PayloadError → String
  | .invalidTransaction index e => s!"transaction {index} does not decode: {reprStr e}"
  | .noEncoding => "a field of the block has no RLP encoding"
  | .wrongBlockHash expected computed =>
    s!"block hash {hex expected.toList}, header hash {hex computed.toList}"
  | .wrongVersionedHashes => "the expected versioned hashes are not those of the block"

/-- The JSON of a payload status, with the code of its reason first in the error. -/
def statusJson (status : PayloadStatus) (reason : Option PayloadError) : Json :=
  let latest := match status.latestValidHash with
    | some h => Json.str (hex h.toList)
    | none => .null
  let error := match reason with
    | some e => Json.str s!"{e.code}: {reasonMessage e}"
    | none => .null
  (Json.mkObj [("status", status.status.name), ("latestValidHash", latest),
    ("validationError", error)])

/-- The version of a method name `engine_newPayloadV1` to `engine_newPayloadV4`. -/
def newPayloadVersion (method : String) : Option Nat :=
  ["engine_newPayloadV1", "engine_newPayloadV2", "engine_newPayloadV3",
    "engine_newPayloadV4"].idxOf? method |>.map (· + 1)

/-- The payload status of an `engine_newPayload` request, without the parent's state. -/
@[export eth_engine_new_payload]
def newPayloadExport (config request : ByteArray) : Result ByteArray := do
  let config ← configOfJson (← parseJson "config" config)
  let request ← parseJson "request" request
  let some method := (request.getObjValAs? String "method").toOption
    | throw (0, "request: no method")
  let some version := newPayloadVersion method | throw (0, s!"no method {method}")
  let params := request.getObjValD "params"
  match newPayloadWithoutState config version params with
  | .ok (status, reason) => return (statusJson status reason).compress.toUTF8
  | .error e => throw (e.code, s!"engine error: {reprStr e}")

end EthLib.Engine.Exports
