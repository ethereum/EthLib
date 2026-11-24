module

public import EthLib.Engine.Json

/-!
# `Engine.Capabilities`

The two methods by which the layers learn about each other.

A step comment names its section or method, as in capabilities, step 2, or client version, step 3.

Sources, at commit `1ca0818` of execution-apis:

- the section [Capabilities][caps] and [`engine_exchangeCapabilities`][xc]: the supported methods
- the method [`engine_getClientVersionV1`][cv]: a version object of four fields
- the structures [`ClientCode`][code] and [`ClientVersionV1`][cvs]
- the [deprecation][deprecate] of `engine_exchangeTransitionConfigurationV1` in Cancun
- the table of [errors][errors] in `common.md`

[caps]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/common.md#capabilities
[xc]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/common.md#engine_exchangecapabilities
[cv]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/identification.md#engine_getclientversionv1
[code]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/identification.md#clientcode
[cvs]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/identification.md#clientversionv1
[deprecate]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/cancun.md#deprecate-engine_exchangetransitionconfigurationv1
[errors]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/common.md#errors
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
  -- Capabilities, step 2: each name includes its version suffix, as in `engine_newPayloadV1`.
  "engine_" ++ method ++ "V" ++ toString version

/-- Whether a name is a method with its version: `engine_`, a method, `V` and a version.

The method is one or more ASCII letters.

The version is a positive decimal number without leading zeros. -/
def isVersionedMethod (name : String) : Bool :=
  -- Capabilities, step 2: the name of each method in both lists includes its version suffix.
  --
  -- The source shows the suffix only by its examples, such as `engine_newPayloadV1`.
  --
  -- The letters and the decimal version without leading zeros are EthLib's reading of them.
  match name.toList with
  | 'e' :: 'n' :: 'g' :: 'i' :: 'n' :: 'e' :: '_' :: rest =>
    -- The name is read from its end: the digits, then `V`, then the letters.
    match rest.reverse.span Char.isDigit with
    | (digits, 'V' :: method) =>
      -- The first digit, last in the reversed name, is not `0`, so the version is positive.
      !method.isEmpty && method.all Char.isAlpha && digits.getLast?.any (· ≠ '0')
    -- The note of the section: `engine_exchangeCapabilities` has no version suffix.
    --
    -- So it fails this test, and a list of names that pass it also follows step 3.
    | _ => false
  | _ => false

/-- A name is a method with its version when the test above accepts it. -/
def IsVersionedMethod (name : String) : Prop := isVersionedMethod name = true

instance : DecidablePred IsVersionedMethod := fun name =>
  inferInstanceAs (Decidable (isVersionedMethod name = true))

/-- The methods that EthLib defines, each with the last version that it defines.

Each method has every version from 1 to that last one.

A real node answers its own list.

This one states what the definitions of EthLib cover. -/
def methodVersions : List (String × Nat) := [
  ("newPayload", 6), ("forkchoiceUpdated", 5), ("getPayload", 6),
  ("getPayloadBodiesByHash", 2), ("getPayloadBodiesByRange", 2), ("getBlobs", 4),
  -- The deprecation in Cancun, step 3: after Cancun, either layer may drop this method.
  --
  -- EthLib keeps it on this line, since it defines that method.
  ("exchangeTransitionConfiguration", 1), ("getClientVersion", 1), ("getInclusionList", 1)]

/-- The full names of the methods that EthLib defines, at every version. -/
def specifiedMethods : List String :=
  methodVersions.flatMap fun (method, last) =>
    -- The versions `1, ..., last` of each method, each name with its suffix, by step 2.
    (List.range last).map fun i => versionedMethod method (i + 1)

/-- The version of a full name of a method that EthLib defines.

The method is named without its prefix or version, such as `newPayload`.

For that method, `engine_newPayloadV3` has version 3.

A name of another method, or of a version that EthLib does not define, has no version. -/
def methodVersion (method name : String) : Option Nat :=
  match methodVersions.lookup method with
  -- The version in `1, ..., last` whose full name is the given name.
  | some last =>
    ((List.range last).find? fun i => versionedMethod method (i + 1) == name).map (· + 1)
  | none => none

/-! ## `engine_exchangeCapabilities` -/

/-- The parameters of the request: exactly one, an array of strings. -/
def exchangeCapabilitiesParams (params : Json) : Decode (List String) := do
  match ← paramsArray params with
  -- Request: one parameter, an `Array of string`, the methods that the consensus node supports.
  --
  -- Step 2 asks each name to include its version, but sets no error for a name without one.
  --
  -- So the decoder takes any string as a name.
  | [methods] => lift (array "capabilities" (string "capability") methods)
  -- Any other parameters are `-32602`, invalid params, by the table of errors.
  | params => invalid s!"params: got {params.length}, expected 1"

/-- The parameters of the request as JSON: the names that the consensus node supports. -/
def exchangeCapabilitiesParamsJson (methods : List String) : Json :=
  .arr #[listJson .str methods]

/-- The method at an execution node: decode the request, then answer the supported methods.

The list given must hold each name with its version, and never this method.

The list of the methods that EthLib defines does. -/
def exchangeCapabilities (supported : List String) (params : Json) :
    Except EngineError (List String) := do
  -- The section on capabilities: every execution node must support this method.
  --
  -- It exchanges the names of the methods that each layer supports.
  --
  -- Step 1 lets the layers call it at will, so no definition models when they do.
  --
  -- Request: the list of the consensus node must decode, though the answer does not read it.
  let _ ← exchangeCapabilitiesParams params
  -- Step 2: the response lists the methods that the execution node supports.
  --
  -- Step 2 also asks each name to include its version, and step 3 leaves this method out.
  --
  -- The list given must follow both, since the answer is that list as it is.
  return supported

/-! ## `engine_getClientVersionV1` -/

/-- Whether a string is a client code: two ASCII letters, in either case. -/
def IsClientCode (code : String) : Prop :=
  -- `ClientCode`: a client named with just two letters.
  --
  -- Client version, step 2: a node takes any two-letter code, even one not reserved.
  --
  -- Every reserved code is uppercase, but the source states no rule on the case.
  --
  -- So EthLib takes two ASCII letters in either case.
  code.toList.length = 2 ∧ code.toList.all Char.isAlpha = true

instance : DecidablePred IsClientCode := fun code => by
  unfold IsClientCode
  infer_instance

/-- The version object of a program, as the method exchanges it. -/
structure ClientVersion where
  -- The rationale of `ClientVersionV1`: the code and the commit identify a program uniquely.
  --
  -- They fit in a limited space, such as the graffiti of a block.
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
  -- `ClientVersionV1`: `code`, `name` and `version` as strings, `commit` as `DATA` of 4 bytes.
  Json.mkObj [
    ("code", .str v.code),
    ("name", .str v.name),
    ("version", .str v.version),
    ("commit", dataJson v.commit.toList)]

/-- A version object: an object with exactly the four fields.

The code is two ASCII letters, and the commit exactly four bytes. -/
def clientVersionOfJson (j : Json) : Decode ClientVersion := do
  -- Not in the source: a `null` field is absent, as in step 1 of `engine_newPayloadV3`.
  let fs ← fields "clientVersion" j
  -- Not in the source: the method states no strict match, and EthLib asks for the four fields.
  --
  -- So a missing field and an unknown field are both invalid params, `-32602`.
  unless hasExactly fs clientVersionFields do
    invalid "clientVersion: not the fields of the structure"
  let get := field "clientVersion" fs
  -- `code`: a `ClientCode`, which by step 2 may be any two letters.
  let code ← string "code" (← get "code")
  unless decide (IsClientCode code) do invalid "code: not two letters"
  return {
    code
    -- `name` and `version`: strings.
    name := ← string "name" (← get "name")
    version := ← string "version" (← get "version")
    -- `commit`: `DATA` of 4 bytes, the first four bytes of the latest commit hash of the build.
    commit := ← fixed "commit" 4 (← get "commit") }

/-- The parameters of the request as JSON: the version object of the consensus node alone. -/
def getClientVersionParamsJson (v : ClientVersion) : Json :=
  -- Request: one parameter, the `ClientVersionV1` that identifies the consensus node.
  .arr #[clientVersionJson v]

/-- The answer as JSON: an array of version objects. -/
def clientVersionsJson (vs : List ClientVersion) : Json :=
  -- Response: an `Array of ClientVersionV1`.
  listJson clientVersionJson vs

/-- The method at an execution node with a version object: decode the request, answer its own.

The object of the node must have a code of two letters, as the decoder asks of the request. -/
def getClientVersion (own : ClientVersion) (params : Json) :
    Except EngineError (List ClientVersion) := do
  -- The method exchanges a version object of four fields.
  --
  -- Step 1 lets the layers call it at will, so no definition models when they do.
  match ← paramsArray params with
  -- Request: one parameter, the `ClientVersionV1` of the consensus node.
  | [v] =>
    -- It must decode, though the answer does not read it.
    let _ ← clientVersionOfJson v
    -- Step 3: a consensus node with a single execution node receives an array of one object.
    --
    -- A multiplexer that joins the arrays of several execution nodes is not modelled here.
    return [own]
  -- Any other parameters are `-32602`, invalid params, by the table of errors.
  | params => invalid s!"params: got {params.length}, expected 1"

end EthLib.Engine
