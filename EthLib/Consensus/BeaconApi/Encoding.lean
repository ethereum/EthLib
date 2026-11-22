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

[root file]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/beacon-node-oapi.yaml
[`types/http.yaml`]: https://github.com/ethereum/beacon-APIs/blob/0ed12552077c9927ba2599ee632e76b2caf021d7/types/http.yaml
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Lean Serialization.Ssz

/-- How the JSON of a type writes its bytes: where it uses the byte alias, and where digits.

Each type of the API declares its own, so no type falls back to a spelling that writes it wrong.

Before Gloas, participation flags are a byte list, and they are written as decimal digits. -/
class ApiSpelling (α : Type) where
  /-- How the type writes its bytes and its one-byte integers. -/
  spelling : Spelling

/-- The JSON document of a value, as the API writes its data. -/
def toApiJson {α : Type} [SszType α] [ApiSpelling α] (x : α) : Except Err Json :=
  -- The JSON mapping of SSZ, with the spelling that the type declares.
  jsonOf (SszType.desc α) (ApiSpelling.spelling α) (SszType.toValue x)

/-- The value that a JSON document holds, read as the API writes its data. -/
def ofApiJson (α : Type) [SszType α] [ApiSpelling α] (document : Json) : Except Err α := do
  -- The JSON mapping of SSZ read back with the spelling of the type, then the value it holds.
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
  -- The source: the data under a data key at the top level, and the metadata in other keys.
  --
  -- Each metadata key is written only when the endpoint gives it.
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
  -- An absent key gives no value.
  | .error _ => .ok none
  -- A present key must hold a value of its form.
  | .ok value => match read value with
    | some b => .ok (some b)
    | none => .error (.badField key)

/-- A version, written as its exact name. -/
def readVersion : Json → Option ConsensusVersion
  -- The source: a string among the names of the consensus versions.
  | .str name => ConsensusVersion.ofName? name
  | _ => none

/-- A boolean. -/
def readBool : Json → Option Bool
  | .bool b => some b
  | _ => none

/-- A root of 32 bytes, written as hex after its `0x` marker, with digits in either case. -/
def readRoot : Json → Option Root
  -- The source: a root is a string of `0x` and 64 hex digits, in either case, so 32 bytes.
  | .str text => match ofHex text with
    | .ok data => Base.exactBytes? 32 ⟨data⟩
    | .error _ => none
  | _ => none

/-- The envelope that a JSON document holds. -/
def ofJson (document : Json) : Except EnvelopeError ApiEnvelope := do
  -- The source: every JSON response is an object with its data under the data key.
  let .obj _ := document | throw .notAnObject
  let .ok data := document.getObjVal? "data" | throw .missingData
  -- Each metadata key that is present must hold a value of its form.
  --
  -- The source may add a key without a new version, so every other key is ignored.
  return {
    version := ← readKey document "version" readVersion
    executionOptimistic := ← readKey document "execution_optimistic" readBool
    finalized := ← readKey document "finalized" readBool
    dependentRoot := ← readKey document "dependent_root" readRoot
    data }

end ApiEnvelope

/-- The value that a response of one version carries. -/
def readVersioned (α : Type) [SszType α] [ApiSpelling α] (expected : ConsensusVersion)
    (document : Json) : Except EnvelopeError α := do
  let envelope ← ApiEnvelope.ofJson document
  -- The envelope must name that version: the version selects the type of the data.
  unless envelope.version = some expected do
    throw (.wrongVersion expected envelope.version)
  -- Its data must hold a value of the type.
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
  -- The source: the code and the message, and the stack traces only when there are some.
  .mkObj <| [("code", Json.num error.code), ("message", Json.str error.message)] ++
    (error.stacktraces.map fun lines => ("stacktraces", Json.arr (lines.map .str).toArray)).toList

/-- A list of strings. -/
def readStrings : Json → Option (List String)
  | .arr items => items.toList.mapM fun | .str s => some s | _ => none
  | _ => none

/-- A code: a JSON number whose value is a natural number, however it is written. -/
def readCode : Json → Option Nat
  -- The source types the code as a JSON number.
  --
  -- EthLib reads a code only when it is a natural number.
  --
  -- A number m * 10^-e is a natural number when m >= 0 and 10^e divides m.
  | .num n =>
    if 0 ≤ n.mantissa ∧ (10 ^ n.exponent : Int) ∣ n.mantissa then
      some (n.mantissa / 10 ^ n.exponent).toNat
    else none
  | _ => none

/-- The error body that a JSON document holds. -/
def ofJson (document : Json) : Option ErrorMessage := do
  -- The source: a code and a message are required.
  let code ← readCode (← (document.getObjVal? "code").toOption)
  let .str message ← (document.getObjVal? "message").toOption | none
  -- The source: the stack traces are optional, and present ones are a list of strings.
  let stacktraces ← match document.getObjVal? "stacktraces" with
    | .error _ => some none
    | .ok lines => (readStrings lines).map some
  return { code, message, stacktraces }

end ErrorMessage

namespace IndexedErrorMessage

/-- The JSON object of an error body that lists the failed items. -/
def toJson (error : IndexedErrorMessage) : Json :=
  -- The source: the code, the message, and each failure with its index and its message.
  .mkObj [("code", Json.num error.code), ("message", Json.str error.message),
    ("failures", Json.arr (error.failures.map fun (index, message) =>
      Json.mkObj [("index", Json.num index), ("message", Json.str message)]).toArray)]

/-- One failure: the position of its item and a message. -/
def readFailure (document : Json) : Option (Nat × String) := do
  -- The source: the index of the item in the request, a number, and a message, both required.
  let index ← ErrorMessage.readCode (← (document.getObjVal? "index").toOption)
  let .str message ← (document.getObjVal? "message").toOption | none
  return (index, message)

/-- The error body that a JSON document holds. -/
def ofJson (document : Json) : Option IndexedErrorMessage := do
  -- The source: a code, a message and a list of failures, all required.
  let code ← ErrorMessage.readCode (← (document.getObjVal? "code").toOption)
  let .str message ← (document.getObjVal? "message").toOption | none
  let .arr failures ← (document.getObjVal? "failures").toOption | none
  return { code, message, failures := ← failures.toList.mapM readFailure }

end IndexedErrorMessage

end EthLib.Consensus.BeaconApi
