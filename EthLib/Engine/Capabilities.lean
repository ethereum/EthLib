module

public import EthLib.Engine.Json

/-!
# `Engine.Capabilities`

The two methods by which the layers learn about each other.

`engine_exchangeCapabilities` exchanges the names of the methods that each layer supports.

Every execution node must support it, and each name must end with the version of its method.

The answer lists what the execution node supports, never this method, whatever the request holds.

The source does not say how to treat a request name without a version, so the decoder takes any.

This module also lists the methods that EthLib defines, with every version of each.

A real node answers its own list; this one states what the definitions of EthLib cover.

It keeps `engine_exchangeTransitionConfigurationV1`, which either layer may drop from Cancun.

`engine_getClientVersionV1` exchanges a version object of four fields.

Its code is two letters and its commit four bytes, so both fit in the graffiti of a block.

Every reserved code is uppercase, but the source states no rule on the case.

So the decoder takes two ASCII letters in either case, reserved or not.

The answer of one execution node is an array of one object, its own.

A multiplexer that joins the arrays of several execution nodes is not modelled here.

No rule says when the consensus node calls either method, so no definition models it.

The sources, at commit `3284ee8` of execution-apis:

- the section [Capabilities][caps] and the method [`engine_exchangeCapabilities`][xc]
- the method [`engine_getClientVersionV1`][cv]
- the structures [`ClientCode`][code] and [`ClientVersionV1`][cvs]
- the [deprecation][deprecate] of `engine_exchangeTransitionConfigurationV1` in Cancun

[caps]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/common.md#capabilities
[xc]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/common.md#engine_exchangecapabilities
[cv]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/identification.md#engine_getclientversionv1
[code]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/identification.md#clientcode
[cvs]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/identification.md#clientversionv1
[deprecate]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/cancun.md#deprecate-engine_exchangetransitionconfigurationv1
-/

@[expose] public section

namespace EthLib.Engine

open Lean (Json)
open EthLib.Base
open EthLib.Engine.Json
open EthLib.Serialization.JsonRpc

/-! ## Method names -/

/-- The full name of a method at a version: `engine_`, the method, `V` and the version. -/
def versionedMethod (method : String) (version : Nat) : String :=
  "engine_" ++ method ++ "V" ++ toString version

/-- Whether a name is a method with its version: `engine_`, a method, `V` and a version.

The method is one or more ASCII letters.

The version is a positive decimal number without leading zeros.

The test reads the name from its end: the digits, then `V`, then the letters. -/
def isVersionedMethod (name : String) : Bool :=
  match name.toList with
  | 'e' :: 'n' :: 'g' :: 'i' :: 'n' :: 'e' :: '_' :: rest =>
    match rest.reverse.span Char.isDigit with
    | (digits, 'V' :: method) =>
      !method.isEmpty && method.all Char.isAlpha && digits.getLast?.any (· ≠ '0')
    | _ => false
  | _ => false

/-- A name is a method with its version when the test above accepts it. -/
def IsVersionedMethod (name : String) : Prop := isVersionedMethod name = true

instance : DecidablePred IsVersionedMethod := fun name =>
  inferInstanceAs (Decidable (isVersionedMethod name = true))

/-- The methods that EthLib defines, each with the last version that it defines.

Each method has every version from 1 to that last one. -/
def methodVersions : List (String × Nat) := [
  ("newPayload", 5), ("forkchoiceUpdated", 4), ("getPayload", 6),
  ("getPayloadBodiesByHash", 2), ("getPayloadBodiesByRange", 2), ("getBlobs", 4),
  ("exchangeTransitionConfiguration", 1), ("getClientVersion", 1)]

/-- The full names of the methods that EthLib defines, at every version. -/
def specifiedMethods : List String :=
  methodVersions.flatMap fun (method, last) =>
    (List.range last).map fun i => versionedMethod method (i + 1)

/-- The version of a full name of a method that EthLib defines.

The method is named without its prefix or version, such as `newPayload`.

For that method, `engine_newPayloadV3` has version 3.

A name of another method, or of a version that EthLib does not define, has no version. -/
def methodVersion (method name : String) : Option Nat :=
  match methodVersions.lookup method with
  | some last =>
    ((List.range last).find? fun i => versionedMethod method (i + 1) == name).map (· + 1)
  | none => none

/-! ## `engine_exchangeCapabilities` -/

/-- The parameters of the request: exactly one, an array of strings.

Anything else is an invalid parameter. -/
def exchangeCapabilitiesParams (params : Json) : Decode (List String) := do
  match ← paramsArray params with
  | [methods] => lift (array "capabilities" (string "capability") methods)
  | params => invalid s!"params: got {params.length}, expected 1"

/-- The parameters of the request as JSON: the names that the consensus node supports. -/
def exchangeCapabilitiesParamsJson (methods : List String) : Json :=
  .arr #[listJson .str methods]

/-- The method at an execution node: decode the request, then answer the supported methods.

Step 2 says that the answer lists what the execution node supports, so it ignores the request.

The list must follow steps 2 and 3: each name with its version, and never this method.

The list of the methods that EthLib defines follows both. -/
def exchangeCapabilities (supported : List String) (params : Json) :
    Except EngineError (List String) := do
  let _ ← exchangeCapabilitiesParams params
  return supported

/-! ## `engine_getClientVersionV1` -/

/-- Whether a string is a client code: two ASCII letters, in either case. -/
def IsClientCode (code : String) : Prop :=
  code.toList.length = 2 ∧ code.toList.all Char.isAlpha = true

instance : DecidablePred IsClientCode := fun code => by
  unfold IsClientCode
  infer_instance

/-- The version object of a program, as the method exchanges it. -/
structure ClientVersion where
  /-- The code of the program, two letters. -/
  code : String
  /-- The name of the program, for people to read. -/
  name : String
  /-- The version of the program. -/
  version : String
  /-- The first four bytes of the hash of the commit that the program was built from. -/
  commit : Vector UInt8 4
  deriving DecidableEq, Repr

/-- The four fields of the structure. -/
def clientVersionFields : List String := ["code", "name", "version", "commit"]

/-- A version object as JSON: three strings and four bytes of data. -/
def clientVersionJson (v : ClientVersion) : Json :=
  Json.mkObj [
    ("code", .str v.code),
    ("name", .str v.name),
    ("version", .str v.version),
    ("commit", dataJson v.commit.toList)]

/-- A version object: an object with exactly the four fields.

The code is two ASCII letters, and the commit exactly four bytes. -/
def clientVersionOfJson (j : Json) : Decode ClientVersion := do
  let fs ← fields "clientVersion" j
  unless hasExactly fs clientVersionFields do
    invalid "clientVersion: not the fields of the structure"
  let get := field "clientVersion" fs
  let code ← string "code" (← get "code")
  unless decide (IsClientCode code) do invalid "code: not two letters"
  return {
    code
    name := ← string "name" (← get "name")
    version := ← string "version" (← get "version")
    commit := ← fixed "commit" 4 (← get "commit") }

/-- The parameters of the request as JSON: the version object of the consensus node alone. -/
def getClientVersionParamsJson (v : ClientVersion) : Json :=
  .arr #[clientVersionJson v]

/-- The answer as JSON: an array of version objects. -/
def clientVersionsJson (vs : List ClientVersion) : Json :=
  listJson clientVersionJson vs

/-- The method at an execution node with a version object: decode the request, answer its own.

Step 3 says that a consensus node with one execution node receives an array of one object.

The object of the node must have a code of two letters, as the decoder asks of the request. -/
def getClientVersion (own : ClientVersion) (params : Json) :
    Except EngineError (List ClientVersion) := do
  match ← paramsArray params with
  | [v] =>
    let _ ← clientVersionOfJson v
    return [own]
  | params => invalid s!"params: got {params.length}, expected 1"

end EthLib.Engine
