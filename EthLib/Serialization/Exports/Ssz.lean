module

public import Lean.Data.Json
public import EthLib.Base.Exports
public import EthLib.Serialization.Ssz.Codec.Json
public import EthLib.Serialization.Ssz.Codec.Root
public import EthLib.Serialization.Ssz.Type.Valid

/-!
# `Exports.Ssz`

C-ABI exports for SSZ, callable from the Python C extension.

A type and a value cross the boundary as JSON, one tagged object for each constructor.

A rejected input comes back as the code of its error and a message that names the fault.

JSON that does not parse, or that names no type or value, has code 0.
-/

public section

namespace EthLib.Serialization.Ssz.Exports

open Lean
open EthLib.Exports (Result)

/-- The deepest nesting of types or values that the exports read. -/
def MAX_NESTING : Nat := 256

/-- The one key and its value of an object with exactly one entry. -/
def tagged (document : Json) : Except String (String × Json) := do
  let .obj entries := document | throw "expected an object with one key"
  match entries.toArray with
  | #[⟨key, value⟩] => return (key, value)
  | _ => throw "expected an object with one key"

/-- A natural number, or none for `null`. -/
def optionalNat (document : Json) : Except String (Option Nat) :=
  if document.isNull then .ok none else some <$> document.getNat?

/-- The elements of a JSON array of exactly two elements. -/
def pair (document : Json) : Except String (Json × Json) := do
  match ← document.getArr? with
  | #[first, second] => return (first, second)
  | _ => throw "expected an array of two elements"

/-- The type that a JSON document names, reading at most `fuel` levels of nesting. -/
def descOf : Nat → Json → Except String Desc
  | 0, _ => throw "the type is nested too deeply"
  | fuel + 1, document => do
    if document == "bool" then return .bool
    let (key, body) ← tagged document
    let fields (body : Json) : Except String (List String × List Desc) := do
      let entries ← (← body.getArr?).toList.mapM pair
      let names ← entries.mapM fun (name, _) => name.getStr?
      let types ← entries.mapM fun (_, type) => descOf fuel type
      return (names, types)
    match key with
    | "uint" => return .uint (← body.getNat?)
    | "byte_vector" => return .byteVector (← body.getNat?)
    | "byte_list" => return .byteList (← body.getNat?)
    | "bitvector" => return .bitVector (← body.getNat?)
    | "bitlist" => return .bitList (← body.getNat?)
    | "progressive_bitlist" => return .progressiveBitList (← optionalNat body)
    | "vector" => do
      let (element, length) ← pair body
      return .vector (← descOf fuel element) (← length.getNat?)
    | "list" => do
      let (element, limit) ← pair body
      return .list (← descOf fuel element) (← limit.getNat?)
    | "progressive_list" => do
      let (element, limit) ← pair body
      return .progressiveList (← descOf fuel element) (← optionalNat limit)
    | "container" => do
      let (names, types) ← fields body
      return .container names types
    | "progressive_container" => do
      let (active, entries) ← pair body
      let active ← (← active.getArr?).toList.mapM Json.getBool?
      let (names, types) ← fields entries
      return .progressiveContainer active names types
    | "compatible_union" => do
      let entries ← (← body.getArr?).toList.mapM pair
      let selectors ← entries.mapM fun (selector, _) => selector.getNat?
      let options ← entries.mapM fun (_, option) => descOf fuel option
      return .compatibleUnion selectors options
    | _ => throw s!"unknown SSZ type {key}"

/-- The value that a JSON document writes, reading at most `fuel` levels of nesting. -/
def valueOfJson : Nat → Json → Except String Value
  | 0, _ => throw "the value is nested too deeply"
  | fuel + 1, document => do
    let (key, body) ← tagged document
    match key with
    | "bool" => return .bool (← body.getBool?)
    | "uint" => return .uint (← body.getNat?)
    | "bytes" => do
      match ofHex (← body.getStr?) with
      | .ok data => return .bytes data
      | .error _ => throw "bytes must be 0x and hex digits"
    | "bits" => return .bits (← (← body.getArr?).mapM Json.getBool?)
    | "seq" => return .seq (← (← body.getArr?).toList.mapM (valueOfJson fuel))
    | "union" => do
      let (selector, data) ← pair body
      return .union (← selector.getNat?) (← valueOfJson fuel data)
    | _ => throw s!"unknown SSZ value {key}"

mutual

/-- The JSON document of a value, in the tagged form that the value reader takes. -/
def jsonOfValue : Value → Json
  | .bool b => Json.mkObj [("bool", b)]
  | .uint n => Json.mkObj [("uint", n)]
  | .bytes data => Json.mkObj [("bytes", toHex data)]
  | .bits data => Json.mkObj [("bits", Json.arr (data.map Json.bool))]
  | .seq elements => Json.mkObj [("seq", Json.arr (jsonOfValues elements #[]))]
  | .union selector data => Json.mkObj [("union", Json.arr #[selector, jsonOfValue data])]

/-- The JSON documents so far, then those of the values, in order.

The loop runs in constant stack for any number of values. -/
def jsonOfValues : List Value → Array Json → Array Json
  | [], out => out
  | value :: rest, out => jsonOfValues rest (out.push (jsonOfValue value))

end

/-- Read a JSON document from UTF-8 bytes, then decode it. -/
def readJson {α : Type} (what : String) (text : ByteArray) (decode : Json → Except String α) :
    Result α := do
  let some text := String.fromUTF8? text | throw (0, s!"{what} is not UTF-8")
  (Json.parse text >>= decode).mapError fun e => (0, s!"{what}: {e}")

/-- Run a fallible step of the codec, with the code of its error and a message. -/
def runSsz {α : Type} (what : String) (act : Except Err α) : Result α :=
  act.mapError fun e => (e.code, s!"{what}: {reprStr e}")

/-- The type that a JSON document names, if SSZ allows it.

A type from outside is checked once here, since the codec does not check it at every step. -/
def readType (type : ByteArray) : Result Desc := do
  let shape ← readJson "type" type (descOf MAX_NESTING)
  runSsz "type rejected" shape.wellFormed
  return shape

/-- The SSZ bytes of a value of a type, both given as JSON. -/
@[export eth_ssz_serialize]
def serializeExport (type value : ByteArray) : Result ByteArray := do
  let shape ← readType type
  let value ← readJson "value" value (valueOfJson MAX_NESTING)
  return ⟨← runSsz "value rejected" (serialize shape value)⟩

/-- The value, as JSON, that SSZ bytes hold for a type given as JSON. -/
@[export eth_ssz_deserialize]
def deserializeExport (type data : ByteArray) : Result ByteArray := do
  let shape ← readType type
  let value ← runSsz "input rejected" (deserialize shape data.data)
  return (jsonOfValue value).compress.toUTF8

/-- The 32-byte hash tree root of a value of a type, both given as JSON. -/
@[export eth_ssz_hash_tree_root]
def hashTreeRootExport (type value : ByteArray) : Result ByteArray := do
  let shape ← readType type
  let value ← readJson "value" value (valueOfJson MAX_NESTING)
  return ⟨← runSsz "value rejected" (hashTreeRoot shape value)⟩

end EthLib.Serialization.Ssz.Exports
