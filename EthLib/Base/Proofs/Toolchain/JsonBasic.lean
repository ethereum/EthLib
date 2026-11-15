module

public import Lean.Data.Json.Basic
-- The equations below restate the bodies of the JSON builder and accessors.
import all Lean.Data.Json.Basic

/-!
# `Base.Proofs.Toolchain.JsonBasic`

The equations of the JSON object builder, null test and accessors, from `Lean.Data.Json.Basic`.

Lean does not expose these bodies.

This module reads them and states each as a public theorem.

Other proofs cite these theorems, so a Lean release that changes a body breaks this file only.
-/

@[expose] public section

namespace EthLib.Base.Toolchain

open Lean

/-- An object built from a list of pairs is the tree map of that list. -/
theorem mkObj_eq (pairs : List (String × Json)) :
    Json.mkObj pairs = .obj (Std.TreeMap.Raw.ofList pairs) := by
  unfold Json.mkObj; rfl

/-- Only `null` is null. -/
theorem isNull_eq (j : Json) : j.isNull = match j with | .null => true | _ => false := by
  cases j <;> rfl

/-- `null` is null. -/
theorem isNull_null : Json.null.isNull = true := by
  rw [isNull_eq]

/-- A Boolean is not null. -/
theorem isNull_bool (b : Bool) : (Json.bool b).isNull = false := by
  rw [isNull_eq]

/-- A string is not null. -/
theorem isNull_str (s : String) : (Json.str s).isNull = false := by
  rw [isNull_eq]

/-- An array is not null. -/
theorem isNull_arr (a : Array Json) : (Json.arr a).isNull = false := by
  rw [isNull_eq]

/-- An object is not null. -/
theorem isNull_obj (kvs : Std.TreeMap.Raw String Json compare) :
    (Json.obj kvs).isNull = false := by
  rw [isNull_eq]

/-- An object built from a list of pairs is not null. -/
theorem isNull_mkObj (pairs : List (String × Json)) : (Json.mkObj pairs).isNull = false := by
  rw [mkObj_eq, isNull_obj]

/-- Reading array items succeeds exactly for an array. -/
theorem getArr?_eq (j : Json) : j.getArr? = match j with
    | .arr items => .ok items
    | _ => .error "array expected" := by
  cases j <;> rfl

/-- Reading a string succeeds exactly for a string. -/
theorem getStr?_eq (j : Json) : j.getStr? = match j with
    | .str text => .ok text
    | _ => .error "String expected" := by
  cases j <;> rfl

/-- Reading a natural number succeeds exactly for its JSON representation. -/
theorem getNat?_eq (j : Json) : j.getNat? = match j with
    | (n : Nat) => .ok n
    | _ => .error "Natural number expected" := by
  cases j <;> rfl

/-- Reading a Boolean succeeds exactly for a Boolean. -/
theorem getBool?_eq (j : Json) : j.getBool? = match j with
    | (b : Bool) => .ok b
    | _ => .error "Bool expected" := by
  cases j <;> rfl

/-- Reading a member of an object looks its name up in the tree map. -/
theorem getObjVal?_eq (j : Json) (k : String) :
    j.getObjVal? k = match j with
      | .obj kvs => match kvs.get? k with
        | some v => .ok v
        | none => .error s!"property not found: {k}"
      | _ => .error "object expected" := by
  cases j <;> rfl

end EthLib.Base.Toolchain
