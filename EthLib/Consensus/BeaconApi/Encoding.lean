module

public import EthLib.Consensus.ConsensusVersion
public import EthLib.Consensus.Types
public import EthLib.Serialization.Ssz.Codec.Json
public import EthLib.Serialization.Ssz.Typed.Class

/-!
# `Consensus.BeaconApi.Encoding`

The shared encodings of the Beacon API: typed JSON, the response envelope and the error bodies.

The data of a response is a value of the consensus layer, written in the JSON mapping of SSZ.

All JSON responses return their data under a `data` key, with optional metadata beside it.

The API may add a key without a new version, so the envelope reader ignores unknown keys.

The reader of the data still refuses a key that its type does not declare.

The [root file] of the API fixes the envelope, and [`types/http.yaml`] fixes the error bodies.

[root file]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/beacon-node-oapi.yaml
[`types/http.yaml`]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/types/http.yaml
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Lean Serialization.Ssz

/-- Where the JSON of a type writes a one-byte integer as the byte alias.

Each type of the API declares its own, so no type falls back to a spelling that writes it wrong.

A participation flag, for one, is written as decimal digits, though its SSZ type is a byte list. -/
class ApiSpelling (α : Type) where
  /-- Where the type writes a one-byte integer as the byte alias. -/
  spelling : Spelling

/-- The JSON document of a value, as the API writes its data. -/
def toApiJson {α : Type} [SszType α] [ApiSpelling α] (x : α) : Except Err Json :=
  jsonOf (SszType.desc α) (ApiSpelling.spelling α) (SszType.toValue x)

/-- The value that a JSON document holds, read as the API writes its data. -/
def ofApiJson (α : Type) [SszType α] [ApiSpelling α] (document : Json) : Except Err α := do
  SszType.ofValue (← valueOf (SszType.desc α) (ApiSpelling.spelling α) document)

/-- The SSZ body of a response that carries a value. -/
def toApiSsz {α : Type} [SszType α] (x : α) : Except Err ByteArray :=
  SszType.encode x

/-- A response of the API: its data, with the metadata that the endpoint gives.

It holds the four metadata keys that many endpoints share.

An endpoint with other keys, such as the block values of block production, reads them itself. -/
structure ApiEnvelope where
  /-- The consensus version of the data. -/
  version : Option ConsensusVersion := none
  /-- Whether the response references an execution payload that is not yet verified.

  The source has a reader take an absent flag as false. -/
  executionOptimistic : Option Bool := none
  /-- Whether the response references the finalized history of the chain. -/
  finalized : Option Bool := none
  /-- The root of the block on which the data depends. -/
  dependentRoot : Option Root := none
  /-- The data. -/
  data : Json

/-- Why a JSON document is not an envelope, or not an envelope of the expected kind. -/
inductive EnvelopeError where
  /-- The document is not an object. -/
  | notAnObject
  /-- The object has no data. -/
  | missingData
  /-- A metadata key holds a value of the wrong form. -/
  | badField (key : String)
  /-- The envelope names another version than the one expected, or none. -/
  | wrongVersion (expected : ConsensusVersion) (found : Option ConsensusVersion)
  /-- The data does not hold a value of the expected type. -/
  | data (fault : Err)
  deriving DecidableEq, Repr

namespace ApiEnvelope

/-- The JSON object of an envelope, with each metadata field that is present. -/
def toJson (envelope : ApiEnvelope) : Json :=
  .mkObj <|
    (envelope.version.map fun v => ("version", Json.str v.name)).toList ++
    (envelope.executionOptimistic.map fun b => ("execution_optimistic", Json.bool b)).toList ++
    (envelope.finalized.map fun b => ("finalized", Json.bool b)).toList ++
    (envelope.dependentRoot.map fun r => ("dependent_root", Json.str (toHex r.toArray))).toList ++
    [("data", envelope.data)]

/-- The value of an optional metadata key, read when the key is present. -/
def readKey {β : Type} (document : Json) (key : String) (read : Json → Option β) :
    Except EnvelopeError (Option β) :=
  match document.getObjVal? key with
  | .error _ => .ok none
  | .ok value => match read value with
    | some b => .ok (some b)
    | none => .error (.badField key)

/-- A version, written as its exact name. -/
def readVersion : Json → Option ConsensusVersion
  | .str name => ConsensusVersion.ofName? name
  | _ => none

/-- A boolean. -/
def readBool : Json → Option Bool
  | .bool b => some b
  | _ => none

/-- A root of 32 bytes, written as hex after its `0x` marker, with digits in either case. -/
def readRoot : Json → Option Root
  | .str text => match ofHex text with
    | .ok data => if size : data.size = 32 then some ⟨data, size⟩ else none
    | .error _ => none
  | _ => none

/-- The envelope that a JSON document holds.

The document must be an object with data.

Each metadata key that is present must hold a value of its form.

Every other key is ignored. -/
def ofJson (document : Json) : Except EnvelopeError ApiEnvelope := do
  let .obj _ := document | throw .notAnObject
  let .ok data := document.getObjVal? "data" | throw .missingData
  return {
    version := ← readKey document "version" readVersion
    executionOptimistic := ← readKey document "execution_optimistic" readBool
    finalized := ← readKey document "finalized" readBool
    dependentRoot := ← readKey document "dependent_root" readRoot
    data }

end ApiEnvelope

/-- The value that a response of one version carries.

The envelope must name that version, and its data must hold a value of the type. -/
def readVersioned (α : Type) [SszType α] [ApiSpelling α] (expected : ConsensusVersion)
    (document : Json) : Except EnvelopeError α := do
  let envelope ← ApiEnvelope.ofJson document
  unless envelope.version = some expected do
    throw (.wrongVersion expected envelope.version)
  match ofApiJson α envelope.data with
  | .ok x => return x
  | .error fault => throw (.data fault)

/-- The body of an error response.

The source fixes the shape of the body, not the text of its message. -/
structure ErrorMessage where
  /-- The HTTP status code, or a more specific code for an invalid request. -/
  code : Nat
  /-- The message. -/
  message : String
  /-- Optional stack traces, for debugging. -/
  stacktraces : Option (List String) := none
  deriving DecidableEq, Repr

/-- The body of an error response to a request that lists items, with each item that failed.

Each failure gives the position of its item in the request, and a message. -/
structure IndexedErrorMessage where
  /-- The HTTP status code, or a more specific code for an invalid request. -/
  code : Nat
  /-- The message. -/
  message : String
  /-- The position and the message of each item that failed. -/
  failures : List (Nat × String)
  deriving DecidableEq, Repr

namespace ErrorMessage

/-- The JSON object of an error body. -/
def toJson (error : ErrorMessage) : Json :=
  .mkObj <| [("code", Json.num error.code), ("message", Json.str error.message)] ++
    (error.stacktraces.map fun lines => ("stacktraces", Json.arr (lines.map .str).toArray)).toList

/-- A list of strings. -/
def readStrings : Json → Option (List String)
  | .arr items => items.toList.mapM fun | .str s => some s | _ => none
  | _ => none

/-- A code: a JSON number whose value is a natural number, however it is written. -/
def readCode : Json → Option Nat
  | .num n =>
    if 0 ≤ n.mantissa ∧ (10 ^ n.exponent : Int) ∣ n.mantissa then
      some (n.mantissa / 10 ^ n.exponent).toNat
    else none
  | _ => none

/-- The error body that a JSON document holds. -/
def ofJson (document : Json) : Option ErrorMessage := do
  let code ← readCode (← (document.getObjVal? "code").toOption)
  let .str message ← (document.getObjVal? "message").toOption | none
  let stacktraces ← match document.getObjVal? "stacktraces" with
    | .error _ => some none
    | .ok lines => (readStrings lines).map some
  return { code, message, stacktraces }

end ErrorMessage

namespace IndexedErrorMessage

/-- The JSON object of an error body that lists the failed items. -/
def toJson (error : IndexedErrorMessage) : Json :=
  .mkObj [("code", Json.num error.code), ("message", Json.str error.message),
    ("failures", Json.arr (error.failures.map fun (index, message) =>
      Json.mkObj [("index", Json.num index), ("message", Json.str message)]).toArray)]

/-- One failure: the position of its item and a message. -/
def readFailure (document : Json) : Option (Nat × String) := do
  let index ← ErrorMessage.readCode (← (document.getObjVal? "index").toOption)
  let .str message ← (document.getObjVal? "message").toOption | none
  return (index, message)

/-- The error body that a JSON document holds. -/
def ofJson (document : Json) : Option IndexedErrorMessage := do
  let code ← ErrorMessage.readCode (← (document.getObjVal? "code").toOption)
  let .str message ← (document.getObjVal? "message").toOption | none
  let .arr failures ← (document.getObjVal? "failures").toOption | none
  return { code, message, failures := ← failures.toList.mapM readFailure }

end IndexedErrorMessage

end EthLib.Consensus.BeaconApi
