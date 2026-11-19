module

public import EthLib.Base.Exports.PyValueCore
public import EthLib.Base.Hex
public import Lean.Data.Json

/-!
# JSON at the Python boundary

The conversions between Python values and the JSON values that the exports read and write.

Bytes use lower-case hexadecimal text with the prefix `0x`.
-/

@[expose] public section

namespace EthLib.Exports.PyValue

open Lean (Json)

mutual

/-- A value as JSON, as `json.dumps` writes it, with bytes as `0x` and lowercase hex.

A list and a tuple become an array, and an error becomes `null`. -/
def toJson : PyValue → Json
  | .none | .failure _ => .null
  | .false => .bool Bool.false
  | .true => .bool Bool.true
  | .int n => .num n
  | .bytes data => .str (Base.hexString data.toList)
  | .str s => .str s
  | .list items | .tuple items => .arr (toJsonArray items)
  | .dict entries => Json.mkObj (toJsonEntries entries).toList
termination_by structural v => v

/-- The items of a sequence as JSON. -/
def toJsonArray : Array PyValue → Array Json
  | ⟨items⟩ => toJsonList items #[]

/-- The JSON of some items so far, then the JSON of the items, in order.

The loop runs in constant stack for any number of items. -/
def toJsonList : List PyValue → Array Json → Array Json
  | [], out => out
  | v :: vs, out => toJsonList vs (out.push (toJson v))

/-- The entries of a `dict` as JSON. -/
def toJsonEntries : Array (String × PyValue) → Array (String × Json)
  | ⟨entries⟩ => toJsonPairs entries #[]

/-- The JSON of some entries so far, then the JSON of the entries, in order.

The loop runs in constant stack for any number of entries. -/
def toJsonPairs : List (String × PyValue) → Array (String × Json) → Array (String × Json)
  | [], out => out
  | (key, v) :: rest, out => toJsonPairs rest (out.push (key, toJson v))

end

mutual

/-- The value of JSON, as `json.loads` reads it for the JSON that the exports write.

A number that is an integer and not negative becomes an `int`.

Any other number becomes its text, and an object becomes a `dict` in the order of its keys. -/
def ofJson : Json → PyValue
  | .null => .none
  | .bool b => if b then .true else .false
  | .num n => if n.exponent = 0 ∧ 0 ≤ n.mantissa then .int n.mantissa.toNat else .str n.toString
  | .str s => .str s
  | .arr items => .list (ofJsonArray items)
  | .obj entries => .dict (ofJsonTree entries.inner.inner #[])
termination_by structural j => j

/-- The values of the items of a JSON array. -/
def ofJsonArray : Array Json → Array PyValue
  | ⟨items⟩ => ofJsonList items #[]

/-- The values of some items so far, then the values of the items of a JSON array, in order.

The loop runs in constant stack for any number of items. -/
def ofJsonList : List Json → Array PyValue → Array PyValue
  | [], out => out
  | j :: js, out => ofJsonList js (out.push (ofJson j))

/-- The entries of a JSON object, in the order of its keys, after some entries. -/
def ofJsonTree : Std.DTreeMap.Internal.Impl String (fun _ => Json) →
    Array (String × PyValue) → Array (String × PyValue)
  | .leaf, entries => entries
  | .inner _ key j left right, entries =>
    ofJsonTree right ((ofJsonTree left entries).push (key, ofJson j))

end


end EthLib.Exports.PyValue
