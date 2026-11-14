module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Serialization.Ssz.Codec.Json
public import EthLib.Serialization.Ssz.Codec.Proof
public import EthLib.Serialization.Ssz.Codec.Root
public import EthLib.Serialization.Ssz.Type.Valid

/-!
# `Exports.Ssz`

C-ABI exports for SSZ, callable from the Python C extension.

A type and a value cross the boundary as Python values in their tagged form.

Each constructor is a tagged `dict`, and the type `bool` is the `str` that names it.

An integer is an `int`, and bytes are `bytes` or a `str` of `0x` and hex.

A rejected input comes back as the code of its error and a message that names the fault.

A value that names no type or value, or an argument of another form, has code 0.
-/

public section

namespace EthLib.Serialization.Ssz.Exports

open EthLib.Exports (Result PyValue pyExport toPy)

/-- The deepest nesting of types or values that the exports read.

From Python the converter bounds the nesting first, at 64 levels below an argument. -/
def MAX_NESTING : Nat := 256

/-- The key and the value of a `dict` with one key.

A key given more than once keeps its last value, as in a JSON object. -/
def tagged : PyValue → Except String (String × PyValue)
  | .dict entries =>
    match entries.back? with
    | some (key, value) =>
      if entries.all (·.1 == key) then return (key, value)
      else throw "expected an object with one key"
    | none => throw "expected an object with one key"
  | _ => throw "expected an object with one key"

/-- A natural number, from an `int`. -/
def natOf : PyValue → Except String Nat
  | .int n => return n
  | _ => throw "Natural number expected"

/-- A natural number, or none for `None` and for an error inside a result.

JSON wrote both of them as `null`. -/
def optionalNat : PyValue → Except String (Option Nat)
  | .none | .failure _ => return none
  | value => some <$> natOf value

/-- A boolean, from `False` or `True`. -/
def boolOf : PyValue → Except String Bool
  | .false => return false
  | .true => return true
  | _ => throw "Bool expected"

/-- A text, from a `str`, or the `0x` and hex of a `bytes`. -/
def strOf : PyValue → Except String String
  | .str s => return s
  | .bytes data => return Base.hexString data.toList
  | _ => throw "String expected"

/-- The items of a `list` or a `tuple`. -/
def itemsOf : PyValue → Except String (Array PyValue)
  | .list items | .tuple items => return items
  | _ => throw "array expected"

/-- The items of a `list` or a `tuple` of exactly two items. -/
def pair (value : PyValue) : Except String (PyValue × PyValue) := do
  match ← itemsOf value with
  | #[first, second] => return (first, second)
  | _ => throw "expected an array of two elements"

/-- The type that a tagged value names, reading at most `fuel` levels of nesting. -/
def descOf : Nat → PyValue → Except String Desc
  | 0, _ => throw "the type is nested too deeply"
  | _ + 1, .str "bool" => return .bool
  | fuel + 1, document => do
    let (key, body) ← tagged document
    let fields (body : PyValue) : Except String (List String × List Desc) := do
      let entries ← (← itemsOf body).toList.mapM pair
      let names ← entries.mapM fun (name, _) => strOf name
      let types ← entries.mapM fun (_, type) => descOf fuel type
      return (names, types)
    match key with
    | "uint" => return .uint (← natOf body)
    | "byte_vector" => return .byteVector (← natOf body)
    | "byte_list" => return .byteList (← natOf body)
    | "bitvector" => return .bitVector (← natOf body)
    | "bitlist" => return .bitList (← natOf body)
    | "progressive_bitlist" => return .progressiveBitList (← optionalNat body)
    | "vector" => do
      let (element, length) ← pair body
      return .vector (← descOf fuel element) (← natOf length)
    | "list" => do
      let (element, limit) ← pair body
      return .list (← descOf fuel element) (← natOf limit)
    | "progressive_list" => do
      let (element, limit) ← pair body
      return .progressiveList (← descOf fuel element) (← optionalNat limit)
    | "container" => do
      let (names, types) ← fields body
      return .container names types
    | "progressive_container" => do
      let (active, entries) ← pair body
      let active ← (← itemsOf active).toList.mapM boolOf
      let (names, types) ← fields entries
      return .progressiveContainer active names types
    | "compatible_union" => do
      let entries ← (← itemsOf body).toList.mapM pair
      let selectors ← entries.mapM fun (selector, _) => natOf selector
      let options ← entries.mapM fun (_, option) => descOf fuel option
      return .compatibleUnion selectors options
    | _ => throw s!"unknown SSZ type {key}"

/-- The value that a tagged value writes, reading at most `fuel` levels of nesting.

Bytes given as `bytes` are taken as they are, and bytes given as text are read from hex. -/
def valueOf : Nat → PyValue → Except String Value
  | 0, _ => throw "the value is nested too deeply"
  | fuel + 1, document => do
    let (key, body) ← tagged document
    match key, body with
    | "bool", body => return .bool (← boolOf body)
    | "uint", body => return .uint (← natOf body)
    | "bytes", .bytes data => return .bytes data.data
    | "bytes", body => do
      match ofHex (← strOf body) with
      | .ok data => return .bytes data
      | .error _ => throw "bytes must be 0x and hex digits"
    | "bits", body => return .bits (← (← itemsOf body).mapM boolOf)
    | "seq", body => return .seq (← (← itemsOf body).toList.mapM (valueOf fuel))
    | "union", body => do
      let (selector, data) ← pair body
      return .union (← natOf selector) (← valueOf fuel data)
    | _, _ => throw s!"unknown SSZ value {key}"

mutual

/-- A value in the tagged form that the value reader takes, with bytes as `0x` and hex. -/
def pyOfValue : Value → PyValue
  | .bool b => .dict #[("bool", toPy b)]
  | .uint n => .dict #[("uint", .int n)]
  | .bytes data => .dict #[("bytes", .str (toHex data))]
  | .bits data => .dict #[("bits", .list (data.map toPy))]
  | .seq elements => .dict #[("seq", .list (pyOfValues elements #[]))]
  | .union selector data => .dict #[("union", .list #[.int selector, pyOfValue data])]

/-- The tagged values so far, then those of the values, in order.

The loop runs in constant stack for any number of values. -/
def pyOfValues : List Value → Array PyValue → Array PyValue
  | [], out => out
  | value :: rest, out => pyOfValues rest (out.push (pyOfValue value))

end

/-- Decode a Python value. -/
def readValue {α : Type} (what : String) (value : PyValue) (decode : PyValue → Except String α) :
    Result α :=
  (decode value).mapError fun e => (0, s!"{what}: {e}")

/-- Run a fallible step of the codec, with the code of its error and a message. -/
def runSsz {α : Type} (what : String) (act : Except Err α) : Result α :=
  act.mapError fun e => (e.code, s!"{what}: {reprStr e}")

/-- The type that a Python value in its tagged form names, if SSZ allows it.

A type from outside is checked once here, since the codec does not check it at every step. -/
def readType (type : PyValue) : Result Desc := do
  let shape ← readValue "type" type (descOf MAX_NESTING)
  runSsz "type rejected" shape.wellFormed
  return shape

/-- The SSZ bytes of a value of a type. -/
def serializeOf (args : PyValue × PyValue) : Result ByteArray := do
  let (type, value) := args
  let shape ← readType type
  let value ← readValue "value" value (valueOf MAX_NESTING)
  return ⟨← runSsz "value rejected" (serialize shape value)⟩

/-- The SSZ bytes of a value of a type, both given in their tagged form. -/
@[export eth_ssz_serialize]
def serializeExport (args : PyValue) : Result PyValue := pyExport serializeOf args

/-- The value that SSZ bytes hold for a type, in its tagged form. -/
def deserializeOf (args : PyValue × ByteArray) : Result PyValue := do
  let (type, data) := args
  let shape ← readType type
  let value ← runSsz "input rejected" (deserialize shape data.data)
  return pyOfValue value

/-- The value that SSZ bytes hold for a type given in its tagged form, as a tagged `dict`. -/
@[export eth_ssz_deserialize]
def deserializeExport (args : PyValue) : Result PyValue := pyExport deserializeOf args

/-- The 32-byte hash tree root of a value of a type. -/
def hashTreeRootOf (args : PyValue × PyValue) : Result ByteArray := do
  let (type, value) := args
  let shape ← readType type
  let value ← readValue "value" value (valueOf MAX_NESTING)
  return ⟨← runSsz "value rejected" (hashTreeRoot shape value)⟩

/-- The 32-byte hash tree root of a value of a type, both given in their tagged form. -/
@[export eth_ssz_hash_tree_root]
def hashTreeRootExport (args : PyValue) : Result PyValue := pyExport hashTreeRootOf args

/-- The step that one part of a path names, read against the type the path has reached.

A part is a position, a word for a mixed-in node, or the name of a field of a container.

The word `__len__` names the length.

The word `__active_fields__` names the field layout of a progressive container.

The word `__selector__` names the selector of a union.

A container takes the names of its fields only; a position given for a field is refused. -/
def pathStep (shape : Option Desc) (part : PyValue) : Result PathStep :=
  match part, shape with
  | .int position, some (.container _ _) | .int position, some (.progressiveContainer _ _ _) =>
    throw (0, s!"path: no field {position}")
  | .int position, _ => return .position position
  | .str "__len__", _ => return .length
  | .str "__active_fields__", _ => return .activeFields
  | .str "__selector__", _ => return .selector
  | .str name, some (.container names _) | .str name, some (.progressiveContainer _ names _) =>
    if names.contains name then return .position (names.idxOf name)
    else throw (0, s!"path: no field {name}")
  | .str name, _ => throw (0, s!"path: no field {name}")
  | _, _ => throw (0, "path: a part must be an int or a str")

/-- The steps that the parts of a path name, after the steps already read.

The type is the one those steps reach, or none where they leave the tree.

A field name past that point gets the fault that the index gives for any step there. -/
def pathSteps (root : Desc) (read : List PathStep) (shape : Option Desc) :
    List PyValue → Result (List PathStep)
  | [] => return read
  | part :: rest => do
    if let (.str name, none) := (part, shape) then
      if !["__len__", "__active_fields__", "__selector__"].contains name then
        let _ ← runSsz "path rejected" (getGeneralizedIndex root (read ++ [.position 0]))
    let step ← pathStep shape part
    let next := shape.bind fun shape => (shape.resolveStep step).toOption.bind (·.2)
    pathSteps root (read ++ [step]) next rest

/-- The generalized index of the node that a path selects in the tree of a type. -/
def generalizedIndexOf (args : PyValue × List PyValue) : Result Nat := do
  let (type, path) := args
  let shape ← readType type
  runSsz "path rejected" (getGeneralizedIndex shape (← pathSteps shape [] (some shape) path))

/-- The generalized index of the node that a path selects in the tree of a type.

The type is in its tagged form.

Each part of the path is a position, a field name, or a word for a mixed-in node.

A field of a container is named, never given by its position. -/
@[export eth_ssz_generalized_index]
def generalizedIndexExport (args : PyValue) : Result PyValue := pyExport generalizedIndexOf args

/-- The branch that proves the node at a generalized index of a value against its root.

The value is first checked by serializing it, so a value that does not fit gets no proof. -/
def merkleProofOf (args : PyValue × PyValue × Nat) : Result (List ByteArray) := do
  let (type, value, gindex) := args
  let shape ← readType type
  let value ← readValue "value" value (valueOf MAX_NESTING)
  let _ ← runSsz "value rejected" (serialize shape value)
  let branch ← runSsz "proof rejected" (buildProof shape value gindex)
  return branch.map fun sibling => ⟨sibling⟩

/-- The branch that proves the node at a generalized index of a value against its root.

The type and the value are in their tagged form.

The branch lists the sibling of each node on the path, from the node up to the root.

The root itself has no branch, so index 1 is refused. -/
@[export eth_ssz_merkle_proof]
def merkleProofExport (args : PyValue) : Result PyValue := pyExport merkleProofOf args

/-- The root of 32-byte chunks, in a tree padded to a power of two.

The width is the limit if one is given, and the number of chunks otherwise. -/
def merkleizeChunksOf (args : List ByteArray × Option Nat) : Result ByteArray := do
  let (chunks, limit) := args
  let chunks := chunks.map (·.data)
  runSsz "chunks rejected" (checkChunks chunks)
  return ⟨← runSsz "chunks rejected" (merkleizeBoundedUnchecked chunks.toArray limit)⟩

/-- The root of 32-byte chunks, in a tree padded to a power of two.

The width is the limit if one is given, and the number of chunks otherwise.

A limit below the number of chunks is refused, and so is a chunk of another width. -/
@[export eth_ssz_merkleize_chunks]
def merkleizeChunksExport (args : PyValue) : Result PyValue := pyExport merkleizeChunksOf args

end EthLib.Serialization.Ssz.Exports
