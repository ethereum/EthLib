module

public import EthLib.Serialization.Exports.Ssz
public import EthLib.Serialization.Ssz.Typed.Basic

/-! Compact transport for the fields of a short, shallow SSZ container. -/

public section

namespace EthLib.Serialization.Ssz.Exports

open EthLib.Exports (PyValue Result)

/-- An integer or byte string inside a singleton dictionary. -/
inductive RecordPayload where
  | nat : Nat → RecordPayload
  | bytes : ByteArray → RecordPayload

/-- A named type and a tagged value at the same position in a record. -/
structure RecordCell where
  name : String
  typeTag : String
  parameter : Nat
  valueTag : String
  payload : RecordPayload

/-- The original tagged type and value represented by the cells. -/
def recordArgs (typeTag valueTag : String) (cells : Array RecordCell) : PyValue × PyValue :=
  let fields := cells.map fun cell =>
    PyValue.tuple #[.str cell.name, .dict #[(cell.typeTag, .int cell.parameter)]]
  let values := cells.map fun cell =>
    let body := match cell.payload with
      | .nat n => PyValue.int n
      | .bytes b => PyValue.bytes b
    PyValue.dict #[(cell.valueTag, body)]
  (.dict #[(typeTag, .list fields)], .dict #[(valueTag, .list values)])

/-- Read the fixed-width leaf types for which the compact serializer can append in place. -/
@[inline] def RecordCell.readType (cell : @& RecordCell) : Option Desc :=
  match cell.typeTag with
  | "uint" => some (.uint cell.parameter)
  | "byte_vector" => some (.byteVector cell.parameter)
  | _ => none

/-- Read a compact field value with the supplied byte representation. -/
@[inline] def RecordCell.readValue {B : Type} (bytes : ByteArray → B)
    (cell : @& RecordCell) : Option (ValueOf B) :=
  match cell.valueTag, cell.payload with
  | "uint", .nat n => some (.uint n)
  | "bytes", .bytes b => some (.bytes (bytes b))
  | _, _ => none

/-- Append a serialized field while keeping its end within the offset limit. -/
@[inline] private def appendRecordField (type : Desc) (value : ValueOf ByteArray)
    (out : ByteArray) : Option ByteArray :=
  match type, value with
  | .uint width, .uint n =>
    if out.size + width ≥ offsetLimit || !uintFits width n then none else
      some (SszType.pushUintBytes width n out)
  | _, _ => do
    let part ← (serialize type value).toOption
    if out.size + part.size ≥ offsetLimit then none else some (out ++ part)

/-- Check one field and append its encoding to the fixed section. -/
@[inline] def RecordCell.append (state : List String × ByteArray) (cell : @& RecordCell) :
    Option (List String × ByteArray) := do
  let (names, out) := state
  if names.contains cell.name then none else
  let type ← cell.readType
  let () ← type.wellFormed.toOption
  let value ← cell.readValue id
  let out ← appendRecordField type value out
  return (cell.name :: names, out)

/-- Encode a fixed-width container by appending its fields in order. -/
def serializeRecord (typeTag valueTag : String) (cells : Array RecordCell) : Option ByteArray := do
  if typeTag != "container" || valueTag != "seq" || cells.isEmpty then none else
  let (_, out) ← cells.foldlM RecordCell.append ([], ByteArray.emptyWithCapacity 128)
  return out

/-- Serialize compact fields, using the tagged reader for any rejection. -/
@[export eth_ssz_serialize_record]
def serializeRecordExport (typeTag valueTag : String) (cells : Array RecordCell) :
    Result ByteArray :=
  match serializeRecord typeTag valueTag cells with
  | some bytes => .ok bytes
  | none => serializeOf (recordArgs typeTag valueTag cells)

/-- Read the type and value from compact fields and compute their root with the codec. -/
def hashTreeRootRecord (typeTag valueTag : String) (cells : Array RecordCell) :
    Option ByteArray := do
  if typeTag != "container" || valueTag != "seq" then none else
  let (names, fields, values) ← cells.foldlM (fun (names, fields, values) cell => do
    return (cell.name :: names, (← cell.readType) :: fields,
      (← cell.readValue ByteArray.data) :: values)) ([], [], [])
  let shape := Desc.container names.reverse fields.reverse
  let () ← shape.wellFormed.toOption
  return ⟨← (hashTreeRoot shape (.seq values.reverse)).toOption⟩

/-- Root compact fields, using the tagged reader for any rejection. -/
@[export eth_ssz_hash_tree_root_record]
def hashTreeRootRecordExport (typeTag valueTag : String) (cells : Array RecordCell) :
    Result ByteArray :=
  match hashTreeRootRecord typeTag valueTag cells with
  | some root => .ok root
  | none => hashTreeRootOf (recordArgs typeTag valueTag cells)

end EthLib.Serialization.Ssz.Exports
