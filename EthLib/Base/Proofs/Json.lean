module

public import EthLib.Base.Proofs.Toolchain.JsonBasic
public import Std.Data.TreeMap.Raw.Lemmas

/-!
# Reading back a JSON object

A JSON object built from a list of pairs holds each pair, when no name appears twice.

A name that the list does not hold is missing from the object.
-/

@[expose] public section

namespace EthLib.Base.Json

open Lean

/-- A name written into an object is read back from it, when no name was written twice. -/
theorem getObjVal?_mkObj {pairs : List (String × Json)} {name : String} {value : Json}
    (distinct : pairs.Pairwise fun a b => a.1 ≠ b.1) (member : (name, value) ∈ pairs) :
    (Json.mkObj pairs).getObjVal? name = .ok value := by
  -- Distinct names stay distinct under the order an object is built with.
  have keys : pairs.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) :=
    distinct.imp fun different equal => different (Std.LawfulEqOrd.compare_eq_iff_eq.mp equal)
  have read :=
    Std.TreeMap.Raw.getElem?_ofList_of_mem (cmp := compare) Std.ReflCmp.compare_self keys member
  simp only [Toolchain.Json.mkObj_eq, Toolchain.Json.getObjVal?_eq,
    Std.TreeMap.Raw.get?_eq_getElem?, read]

/-- A name that was not written into an object is not found in it.

The lookup fails with the message that names the missing property. -/
theorem getObjVal?_mkObj_of_not_mem {pairs : List (String × Json)} {name : String}
    (absent : name ∉ pairs.map Prod.fst) :
    (Json.mkObj pairs).getObjVal? name = .error s!"property not found: {name}" := by
  have none : (Std.TreeMap.Raw.ofList pairs (cmp := compare))[name]? = none :=
    Std.TreeMap.Raw.getElem?_ofList_of_contains_eq_false (by simpa using absent)
  simp only [Toolchain.Json.mkObj_eq, Toolchain.Json.getObjVal?_eq,
    Std.TreeMap.Raw.get?_eq_getElem?, none]

end EthLib.Base.Json
