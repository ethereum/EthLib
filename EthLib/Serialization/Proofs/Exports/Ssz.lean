module

public import EthLib.Base.Proofs.Hex
public import Lean.Data.Json
public import EthLib.Serialization.Ssz.Codec.Json
public import EthLib.Serialization.Exports.Ssz
public import EthLib.Serialization.Proofs.Ssz.Codec.Packed
import EthLib.Base.Proofs.ExceptT
import EthLib.Serialization.Proofs.Ssz.Typed.Basic
import EthLib.Serialization.Proofs.Ssz.Codec.BindingPacking
import EthLib.Serialization.Proofs.Ssz.Codec.Summary
import EthLib.Base.Proofs.Toolchain.JsonBasic
import all EthLib.Serialization.Exports.Ssz
import all EthLib.Base.Exports.PyValueCore
import all EthLib.Base.Exports.PyValueJson
import Std.Data.TreeMap.Raw.Lemmas
import Std.Data.TreeMap.Raw.WF

/-!
# Proofs: `Serialization.Exports.Ssz`

The SSZ exports read and write Python values directly.

This file holds JSON readers of types and values, and a JSON writer of values, as a reference.

The readers here test for the type `bool` with a match, not with the equality of JSON documents.

It proves that reading a Python value gives what the reference gives on its JSON.

The result is the same type, the same value or the same error, on every input.

It also proves that the writer gives the same Python value as the reference JSON read back.
-/

public section

namespace EthLib.Serialization.Ssz.Exports.Proofs

open Lean (Json)
open EthLib.Exports (PyValue)

/-- The one key and its value of an object with exactly one entry. -/
noncomputable def jsonTagged (document : Json) : Except String (String × Json) := do
  let .obj entries := document | throw "expected an object with one key"
  match entries.toArray with
  | #[⟨key, value⟩] => return (key, value)
  | _ => throw "expected an object with one key"

/-- A natural number, or none for `null`. -/
noncomputable def jsonOptionalNat (document : Json) : Except String (Option Nat) :=
  if document.isNull then .ok none else some <$> document.getNat?

/-- The elements of a JSON array of exactly two elements. -/
noncomputable def jsonPair (document : Json) : Except String (Json × Json) := do
  match ← document.getArr? with
  | #[first, second] => return (first, second)
  | _ => throw "expected an array of two elements"

/-- The type that a tagged document names, reading at most `fuel` levels of nesting.

The equality of JSON documents is a partial function, so the logic cannot unfold it.

So this reader tests for the word `bool` with a match.

A document equals the word `bool` exactly when it is that string. -/
noncomputable def jsonDescOf : Nat → Json → Except String Desc
  | 0, _ => throw "the type is nested too deeply"
  | fuel + 1, document => do
    if let .str "bool" := document then return .bool
    let (key, body) ← jsonTagged document
    let fields (body : Json) : Except String (List String × List Desc) := do
      let entries ← (← body.getArr?).toList.mapM jsonPair
      let names ← entries.mapM fun (name, _) => name.getStr?
      let types ← entries.mapM fun (_, type) => jsonDescOf fuel type
      return (names, types)
    match key with
    | "uint" => return .uint (← body.getNat?)
    | "byte_vector" => return .byteVector (← body.getNat?)
    | "byte_list" => return .byteList (← body.getNat?)
    | "bitvector" => return .bitVector (← body.getNat?)
    | "bitlist" => return .bitList (← body.getNat?)
    | "progressive_bitlist" => return .progressiveBitList (← jsonOptionalNat body)
    | "vector" => do
      let (element, length) ← jsonPair body
      return .vector (← jsonDescOf fuel element) (← length.getNat?)
    | "list" => do
      let (element, limit) ← jsonPair body
      return .list (← jsonDescOf fuel element) (← limit.getNat?)
    | "progressive_list" => do
      let (element, limit) ← jsonPair body
      return .progressiveList (← jsonDescOf fuel element) (← jsonOptionalNat limit)
    | "container" => do
      let (names, types) ← fields body
      return .container names types
    | "progressive_container" => do
      let (active, entries) ← jsonPair body
      let active ← (← active.getArr?).toList.mapM Json.getBool?
      let (names, types) ← fields entries
      return .progressiveContainer active names types
    | "compatible_union" => do
      let entries ← (← body.getArr?).toList.mapM jsonPair
      let selectors ← entries.mapM fun (selector, _) => selector.getNat?
      let options ← entries.mapM fun (_, option) => jsonDescOf fuel option
      return .compatibleUnion selectors options
    | _ => throw s!"unknown SSZ type {key}"

/-- The value that a tagged document writes, reading at most `fuel` levels of nesting. -/
noncomputable def jsonValueOf : Nat → Json → Except String Value
  | 0, _ => throw "the value is nested too deeply"
  | fuel + 1, document => do
    let (key, body) ← jsonTagged document
    match key with
    | "bool" => return .bool (← body.getBool?)
    | "uint" => return .uint (← body.getNat?)
    | "bytes" => do
      match ofHex (← body.getStr?) with
      | .ok data => return .bytes data
      | .error _ => throw "bytes must be 0x and hex digits"
    | "bits" => return .bits (← (← body.getArr?).mapM Json.getBool?)
    | "seq" => return .seq (← (← body.getArr?).toList.mapM (jsonValueOf fuel))
    | "union" => do
      let (selector, data) ← jsonPair body
      return .union (← selector.getNat?) (← jsonValueOf fuel data)
    | _ => throw s!"unknown SSZ value {key}"

mutual

/-- The JSON document of a value, in the tagged form that the value reader takes. -/
noncomputable def jsonOfValue : Value → Json
  | .bool b => Json.mkObj [("bool", b)]
  | .uint n => Json.mkObj [("uint", n)]
  | .bytes data => Json.mkObj [("bytes", toHex data)]
  | .bits data => Json.mkObj [("bits", Json.arr (data.map Json.bool))]
  | .seq elements => Json.mkObj [("seq", Json.arr (jsonOfValues elements #[]))]
  | .union selector data => Json.mkObj [("union", Json.arr #[selector, jsonOfValue data])]

/-- The JSON documents so far, then those of the values, in order. -/
noncomputable def jsonOfValues : List Value → Array Json → Array Json
  | [], out => out
  | value :: rest, out => jsonOfValues rest (out.push (jsonOfValue value))

end

/-- An object of one entry reads back as a `dict` of that one entry. -/
private theorem ofJson_mkObj_single (key : String) (j : Json) :
    PyValue.ofJson (Json.mkObj [(key, j)]) = .dict #[(key, PyValue.ofJson j)] := by
  have h : Json.mkObj [(key, j)] = .obj ⟨⟨.inner 1 key j .leaf .leaf⟩⟩ := by
    rw [Base.Toolchain.Json.mkObj_eq]
    rfl
  rw [h, PyValue.ofJson]
  rfl

/-- The array loop of the reader appends the values of the items, in order. -/
private theorem ofJsonList_eq (items : List Json) (out : Array PyValue) :
    PyValue.ofJsonList items out = out ++ (items.map PyValue.ofJson).toArray := by
  induction items generalizing out with
  | nil => simp [PyValue.ofJsonList]
  | cons j js ih => simp [PyValue.ofJsonList, ih]

/-- A JSON array reads back as a `list` of the values of its items. -/
private theorem ofJson_arr (items : Array Json) :
    PyValue.ofJson (.arr items) = .list (items.map PyValue.ofJson) := by
  rw [PyValue.ofJson]
  cases items
  simp [PyValue.ofJsonArray, ofJsonList_eq]

/-- The JSON writer of values appends the document of each value, in order. -/
private theorem jsonOfValues_eq (values : List Value) (out : Array Json) :
    jsonOfValues values out = out ++ (values.map jsonOfValue).toArray := by
  induction values generalizing out with
  | nil => simp [jsonOfValues]
  | cons v vs ih => simp [jsonOfValues, ih]

/-- The Python writer of values appends the tagged value of each value, in order. -/
private theorem pyOfValues_eq (values : List Value) (out : Array PyValue) :
    pyOfValues values out = out ++ (values.map pyOfValue).toArray := by
  induction values generalizing out with
  | nil => simp [pyOfValues]
  | cons v vs ih => simp [pyOfValues, ih]

/-- Writing a value gives the Python value that its JSON gave, by recursion on the value. -/
private theorem pyOfValue_eq_json_aux : (value : Value) →
    pyOfValue value = PyValue.ofJson (jsonOfValue value)
  | .bool b => by
    rw [jsonOfValue, ofJson_mkObj_single, pyOfValue]
    cases b <;> rfl
  | .uint n => by
    rw [jsonOfValue, ofJson_mkObj_single, pyOfValue]
    simp [PyValue.ofJson, Lean.JsonNumber.fromNat]
  | .bytes data => by
    rw [jsonOfValue, ofJson_mkObj_single, pyOfValue]
    simp [PyValue.ofJson]
  | .bits data => by
    rw [jsonOfValue, ofJson_mkObj_single, pyOfValue, ofJson_arr]
    simp [PyValue.ofJson]
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  | .seq elements => by
    rw [jsonOfValue, ofJson_mkObj_single, pyOfValue, ofJson_arr, jsonOfValues_eq,
      pyOfValues_eq]
    simp only [List.map_toArray, List.map_map, Array.empty_append]
    -- Each element is written alike, by recursion on that element.
    rw [List.map_congr_left fun v _ => pyOfValue_eq_json_aux v]
    rfl
  | .union selector data => by
    rw [jsonOfValue, ofJson_mkObj_single, pyOfValue, ofJson_arr, pyOfValue_eq_json_aux data]
    simp [PyValue.ofJson, Lean.JsonNumber.fromNat]

/-- The array loop of the writer appends the JSON of the items, in order. -/
private theorem toJsonList_eq (items : List PyValue) (out : Array Json) :
    PyValue.toJsonList items out = out ++ (items.map PyValue.toJson).toArray := by
  induction items generalizing out with
  | nil => simp [PyValue.toJsonList]
  | cons v vs ih => simp [PyValue.toJsonList, ih]

/-- The items of a sequence as JSON are the JSON of each item. -/
private theorem toJsonArray_eq (items : Array PyValue) :
    PyValue.toJsonArray items = items.map PyValue.toJson := by
  cases items
  simp [PyValue.toJsonArray, toJsonList_eq]

/-- The entry loop of the writer appends each key with the JSON of its value, in order. -/
private theorem toJsonPairs_eq (entries : List (String × PyValue)) (out : Array (String × Json)) :
    PyValue.toJsonPairs entries out =
      out ++ (entries.map fun entry => (entry.1, entry.2.toJson)).toArray := by
  induction entries generalizing out with
  | nil => simp [PyValue.toJsonPairs]
  | cons e es ih => simp [PyValue.toJsonPairs, ih]

/-- The entries of a `dict` as JSON are each key with the JSON of its value. -/
private theorem toJsonEntries_eq (entries : Array (String × PyValue)) :
    PyValue.toJsonEntries entries = entries.map fun entry => (entry.1, entry.2.toJson) := by
  cases entries
  simp [PyValue.toJsonEntries, toJsonPairs_eq]

/-- Reading a natural number from JSON reads it from the Python value. -/
private theorem getNat?_toJson (value : PyValue) : value.toJson.getNat? = natOf value := by
  cases value <;>
    simp [PyValue.toJson, natOf, Base.Toolchain.Json.getNat?_eq, Base.Toolchain.Json.mkObj_eq] <;>
      rfl

/-- Reading a boolean from JSON reads it from the Python value. -/
private theorem getBool?_toJson (value : PyValue) : value.toJson.getBool? = boolOf value := by
  cases value <;>
    simp [PyValue.toJson, boolOf, Base.Toolchain.Json.getBool?_eq, Base.Toolchain.Json.mkObj_eq] <;>
      rfl

/-- Reading a text from JSON reads it from the Python value. -/
private theorem getStr?_toJson (value : PyValue) : value.toJson.getStr? = strOf value := by
  cases value <;>
    simp [PyValue.toJson, strOf, Base.Toolchain.Json.getStr?_eq, Base.Toolchain.Json.mkObj_eq] <;>
      rfl

/-- Reading an array from JSON reads the items of the Python value, as JSON. -/
private theorem getArr?_toJson (value : PyValue) :
    value.toJson.getArr? = (·.map PyValue.toJson) <$> itemsOf value := by
  cases value <;>
    simp [PyValue.toJson, itemsOf, Base.Toolchain.Json.getArr?_eq, Base.Toolchain.Json.mkObj_eq,
      toJsonArray_eq] <;> rfl

/-- Reading a pair from JSON reads the pair of the Python value, as JSON. -/
private theorem jsonPair_toJson (value : PyValue) :
    jsonPair value.toJson =
      (fun items => (items.1.toJson, items.2.toJson)) <$> pair value := by
  unfold jsonPair pair
  rw [getArr?_toJson]
  cases itemsOf value with
  | error e => rfl
  | ok items =>
    rcases items with ⟨items⟩
    have h : (Array.map PyValue.toJson <$> (.ok ⟨items⟩ : Except String (Array PyValue))) =
        .ok ⟨items.map PyValue.toJson⟩ := by
      simp [Functor.map, Except.map]
    rw [h]
    rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> rfl

/-- Setting the one key of a map of one entry replaces its value. -/
private theorem insert_single (key : String) (old new : Json) :
    (⟨⟨.inner 1 key old .leaf .leaf⟩⟩ : Std.TreeMap.Raw String Json compare).insert key new =
      ⟨⟨.inner 1 key new .leaf .leaf⟩⟩ := by
  simp [Std.TreeMap.Raw.insert, Std.DTreeMap.Raw.insert, Std.DTreeMap.Internal.Impl.insert!]

/-- Setting the one key of a map of one entry again and again keeps the last value. -/
private theorem insertMany_single (key : String) (old : Json) (rest : List (String × Json))
    (same : ∀ entry ∈ rest, entry.1 = key) :
    (⟨⟨.inner 1 key old .leaf .leaf⟩⟩ : Std.TreeMap.Raw String Json compare).insertMany rest =
      ⟨⟨.inner 1 key ((rest.getLast?.map (·.2)).getD old) .leaf .leaf⟩⟩ := by
  induction rest generalizing old with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨k, v⟩ := entry
    obtain rfl : k = key := same (k, v) (by simp)
    rw [Std.TreeMap.Raw.insertMany_cons, insert_single, ih _ fun e he => same e (by simp [he])]
    cases rest <;> simp [List.getLast?_cons]

/-- An object whose keys are all one key reads as that key with its last value. -/
private theorem jsonTagged_mkObj_same (key : String) (first : Json)
    (rest : List (String × Json)) (same : ∀ entry ∈ rest, entry.1 = key) :
    jsonTagged (Json.mkObj ((key, first) :: rest)) =
      .ok (key, (rest.getLast?.map (·.2)).getD first) := by
  have single : (∅ : Std.TreeMap.Raw String Json compare).insert key first =
      ⟨⟨.inner 1 key first .leaf .leaf⟩⟩ := rfl
  rw [Base.Toolchain.Json.mkObj_eq, Std.TreeMap.Raw.ofList_cons, single,
    insertMany_single _ _ _ same]
  rfl

/-- A key of a map whose entries are one entry is the key of that entry. -/
private theorem key_eq_of_toArray (l : List (String × Json)) (key key' : String) (value : Json)
    (entries : (Std.TreeMap.Raw.ofList l compare).toArray = #[(key', value)])
    (mem : key ∈ l.map Prod.fst) : key = key' := by
  have wf : (Std.TreeMap.Raw.ofList l compare).WF := Std.TreeMap.Raw.WF.ofList
  have inMap : key ∈ Std.TreeMap.Raw.ofList l compare := by simpa using mem
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp
    ((Std.TreeMap.Raw.mem_iff_isSome_getElem? wf).mp inMap)
  have := (Std.TreeMap.Raw.mem_toArray_iff_getElem?_eq_some wf).mpr hv
  rw [entries] at this
  simp at this
  exact this.1

/-- An object with two different keys is not an object with one key. -/
private theorem jsonTagged_mkObj_two (l : List (String × Json)) (a b : String)
    (ha : a ∈ l.map Prod.fst) (hb : b ∈ l.map Prod.fst) (ne : a ≠ b) :
    jsonTagged (Json.mkObj l) = .error "expected an object with one key" := by
  unfold jsonTagged
  rw [Base.Toolchain.Json.mkObj_eq]
  rcases entries : (Std.TreeMap.Raw.ofList l compare).toArray with
    ⟨_ | ⟨⟨k, v⟩, _ | ⟨x, rest⟩⟩⟩
  · dsimp only
    rw [entries]
    rfl
  · exact absurd ((key_eq_of_toArray l a k v entries ha).trans
      (key_eq_of_toArray l b k v entries hb).symm) ne
  · dsimp only
    rw [entries]
    rfl

/-- Reading the one key from JSON reads it from the Python value, with its value as JSON. -/
private theorem jsonTagged_toJson (value : PyValue) :
    jsonTagged value.toJson = (fun entry => (entry.1, entry.2.toJson)) <$> tagged value := by
  cases value with
  | dict entries =>
    rw [PyValue.toJson, toJsonEntries_eq]
    rcases entries with ⟨l⟩
    rw [Array.toList_map]
    rcases List.eq_nil_or_concat l with rfl | ⟨init, ⟨key, value⟩, rfl⟩
    · rw [Base.Toolchain.Json.mkObj_eq]
      rfl
    · simp only [List.concat_eq_append]
      simp [tagged]
      by_cases same : ∀ entry ∈ init, entry.1 = key
      · have all : (⟨init ++ [(key, value)]⟩ : Array (String × PyValue)).all
            (fun entry => entry.1 == key) = true := by
          simpa using same
        simp only [all, Bool.or_true, ↓reduceIte]
        cases init with
        | nil => exact jsonTagged_mkObj_same key _ [] (by simp)
        | cons first init =>
          obtain ⟨k, v⟩ := first
          obtain rfl : k = key := same (k, v) (by simp)
          rw [List.map_cons, List.cons_append, jsonTagged_mkObj_same]
          · simp
            rfl
          · simp only [List.mem_append, List.mem_map, List.mem_singleton]
            rintro e (⟨a, mem, rfl⟩ | rfl)
            · exact same a (by simp [mem])
            · rfl
      · -- Some entry has another key than the last one, so the object has two keys.
        obtain ⟨entry, mem, other⟩ : ∃ entry ∈ init, entry.1 ≠ key := by
          simpa using same
        have notAll : ¬ (⟨init ++ [(key, value)]⟩ : Array (String × PyValue)).all
            (fun entry => entry.1 == key) = true := by
          simp
          exact ⟨entry.1, ⟨entry.2, mem⟩, other⟩
        have sizeNotOne : (⟨init ++ [(key, value)]⟩ : Array (String × PyValue)).size ≠ 1 := by
          simpa using (List.ne_nil_of_mem mem)
        simp only [beq_eq_false_iff_ne.mpr sizeNotOne, notAll, Bool.false_or]
        rw [jsonTagged_mkObj_two _ entry.1 key ?_ ?_ other]
        · rfl
        · simp
          exact .inl ⟨entry.2, mem⟩
        · simp
  | _ => rfl

/-- Each of the sixteen digits reads back as its own value. -/
private theorem hexDigit_hexDigitChar (digit : Fin 16) :
    hexDigit (Base.hexDigitChar digit) = .ok digit.val := by
  -- Sixteen characters, each checked against the three ranges the reader tests.
  obtain ⟨value, small⟩ := digit
  rcases value with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | value
  all_goals first | rfl | omega

/-- The byte loop of the hex reader from some bytes is the loop from none, after them. -/
private theorem hexBytesFrom_eq : ∀ (digits : List Char) (out : Bytes),
    hexBytesFrom digits out = (hexBytesFrom digits #[]).map (out ++ ·)
  | [], out => by simp [hexBytesFrom, Except.map]
  | [_], _ => rfl
  | high :: low :: rest, out => by
    simp only [hexBytesFrom]
    cases hexDigit high with
    | error e => rfl
    | ok h =>
      cases hexDigit low with
      | error e => rfl
      | ok l =>
        show hexBytesFrom rest (out.push _) = (hexBytesFrom rest (#[].push _)).map _
        rw [hexBytesFrom_eq rest (out.push _), hexBytesFrom_eq rest (#[].push _)]
        cases hexBytesFrom rest #[] <;>
          simp only [Except.map, Array.push_eq_append, Array.empty_append, Array.append_assoc]

/-- The first two digits hold the first byte, and the rest hold the bytes after it. -/
private theorem hexBytes_cons (high low : Char) (rest : List Char) :
    hexBytes (high :: low :: rest) = do
      let byte := 16 * (← hexDigit high) + (← hexDigit low)
      return #[UInt8.ofNat byte] ++ (← hexBytes rest) := by
  simp only [hexBytes, hexBytesFrom]
  cases hexDigit high with
  | error e => rfl
  | ok h =>
    cases hexDigit low with
    | error e => rfl
    | ok l =>
      show hexBytesFrom rest (#[].push _) = _
      rw [hexBytesFrom_eq]
      cases hexBytesFrom rest #[] <;> rfl

/-- A hex string that the writer gives reads back as the bytes it was written from. -/
private theorem ofHex_hexString (bytes : List UInt8) :
    ofHex (Base.hexString bytes) = .ok bytes.toArray := by
  -- Two digits at a time rebuild one byte, and the rest of the string follows.
  have general : ∀ (bytes : List UInt8),
      hexBytes (bytes.flatMap Base.byteHexDigits) = .ok bytes.toArray := by
    intro bytes
    induction bytes with
    | nil => rfl
    | cons byte rest ih =>
      simp [Base.byteHexDigits, hexBytes_cons, hexDigit_hexDigitChar, Nat.div_add_mod, ih,
        Bind.bind, Except.bind, pure, Except.pure, UInt8.ofNat_toNat]
  simp [ofHex, Base.toList_hexString, general]

/-- The list loop of a byte buffer gives the bytes so far, reversed, then the bytes left. -/
private theorem toList_loop (bytes : ByteArray) : ∀ (n i : Nat) (out : List UInt8),
    bytes.size - i = n →
      ByteArray.toList.loop bytes i out = out.reverse ++ bytes.data.toList.drop i
  | 0, i, out, left => by
    rw [ByteArray.toList.loop]
    have done : ¬ i < bytes.size := by omega
    simp only [done, ↓reduceIte]
    rw [List.drop_eq_nil_of_le (by rw [Array.length_toList]; exact Nat.le_of_not_lt done),
      List.append_nil]
  | n + 1, i, out, left => by
    rw [ByteArray.toList.loop]
    have more : i < bytes.size := by omega
    simp only [more, ↓reduceIte]
    rw [toList_loop bytes n (i + 1) _ (by omega)]
    have inList : i < bytes.data.toList.length := by rw [Array.length_toList]; exact more
    rw [List.drop_eq_getElem_cons inList, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    obtain ⟨data⟩ := bytes
    simp only [ByteArray.get!, Array.getElem_toList, getElem!_pos data i more]

/-- The bytes of a byte buffer, as a list, are those of its array. -/
private theorem byteArray_toList (bytes : ByteArray) : bytes.toList = bytes.data.toList := by
  rw [ByteArray.toList]
  simpa using toList_loop bytes _ 0 [] rfl

/-- Only the word `bool` itself has the JSON of that word. -/
private theorem toJson_ne_bool (type : PyValue) (word : type ≠ .str "bool") :
    type.toJson ≠ .str "bool" := by
  cases type with
  | bytes data =>
    -- A hex string starts with `0`, and the word starts with `b`.
    intro same
    have chars := congrArg String.toList (Json.str.inj same)
    rw [Base.toList_hexString] at chars
    simp at chars
  | str s => simpa [PyValue.toJson] using word
  | dict entries => simp [PyValue.toJson, Base.Toolchain.Json.mkObj_eq]
  | _ => simp [PyValue.toJson]

/-- Reading an optional natural number from JSON reads it from the Python value. -/
private theorem jsonOptionalNat_toJson (value : PyValue) :
    jsonOptionalNat value.toJson = optionalNat value := by
  cases value <;>
    simp [jsonOptionalNat, PyValue.toJson, optionalNat, Base.Toolchain.Json.isNull_eq,
      Base.Toolchain.Json.mkObj_eq, Base.Toolchain.Json.getNat?_eq, natOf] <;> rfl

/-- Reading pairs from JSON reads the pairs of the Python values, as JSON. -/
private theorem mapM_jsonPair (items : List PyValue) :
    (items.map PyValue.toJson).mapM jsonPair =
      List.map (fun p => (p.1.toJson, p.2.toJson)) <$> items.mapM pair := by
  induction items with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, List.mapM_cons, jsonPair_toJson, ih]
    cases pair v <;> cases vs.mapM pair <;> rfl

/-- Reading a type gives what reading its JSON gave, the same type or the same error. -/
theorem descOf_eq_json (fuel : Nat) (type : PyValue) :
    descOf fuel type = jsonDescOf fuel type.toJson := by
  induction fuel generalizing type with
  | zero => rfl
  | succ fuel ih =>
    by_cases word : type = .str "bool"
    · subst word
      rfl
    rw [descOf.eq_3 _ _ word, jsonDescOf, jsonTagged_toJson]
    rotate_left
    · exact toJson_ne_bool type word
    cases tagged type with
    | error e => rfl
    | ok entry =>
      obtain ⟨key, body⟩ := entry
      simp only [Functor.map, Except.map, bind, Except.bind]
      split
      all_goals simp only [getNat?_toJson, getArr?_toJson, jsonPair_toJson, jsonOptionalNat_toJson]
      case h_7 | h_8 | h_9 =>
        cases pair body with
        | error e => rfl
        | ok p => simp only [Functor.map, Except.map, ← ih, getNat?_toJson, jsonOptionalNat_toJson]
      case h_10 | h_12 =>
        cases itemsOf body with
        | error e => rfl
        | ok items =>
          simp only [Functor.map, Except.map, Array.toList_map, mapM_jsonPair]
          cases items.toList.mapM pair with
          | error e => rfl
          | ok entries =>
            simp only [List.mapM_map, Function.comp_def, getStr?_toJson, getNat?_toJson, ← ih]
      case h_11 =>
        cases pair body with
        | error e => rfl
        | ok p =>
          simp only [Functor.map, Except.map, getArr?_toJson]
          cases itemsOf p.1 with
          | error e => rfl
          | ok active =>
            simp only [Array.toList_map, List.mapM_map, Function.comp_def, getBool?_toJson]
            cases active.toList.mapM boolOf with
            | error e => rfl
            | ok flags =>
              cases itemsOf p.2 with
              | error e => rfl
              | ok items =>
                simp only [Array.toList_map, mapM_jsonPair, Functor.map, Except.map]
                cases items.toList.mapM pair with
                | error e => rfl
                | ok entries =>
                  simp only [List.mapM_map, Function.comp_def, getStr?_toJson, ← ih]

private theorem reverse_foldlM_cons (f : α → Except String β) (items : List α)
    (acc : List β) :
    List.reverse <$> items.foldlM (fun out item => return (← f item) :: out) acc =
      List.mapM.loop f items acc := by
  induction items generalizing acc with
  | nil => rfl
  | cons item items ih =>
    rw [List.foldlM_cons, List.mapM.loop]
    cases e : f item with
    | error => rfl
    | ok value => exact ih (value :: acc)

private theorem valueOfWith_array (fuel : Nat) (value : PyValue) :
    valueOfWith ByteArray.data id fuel value = valueOf fuel value := rfl

/-- Reading a value gives what reading its JSON gave, the same value or the same error. -/
theorem valueOf_eq_json (fuel : Nat) (value : PyValue) :
    valueOf fuel value = jsonValueOf fuel value.toJson := by
  induction fuel generalizing value with
  | zero => rfl
  | succ fuel ih =>
    rw [valueOf, valueOfWith, jsonValueOf, jsonTagged_toJson]
    cases tagged value with
    | error e => rfl
    | ok entry =>
      obtain ⟨key, body⟩ := entry
      simp only [Functor.map, Except.map, bind, Except.bind]
      split
      all_goals simp only [getBool?_toJson, getNat?_toJson, getStr?_toJson, getArr?_toJson,
        jsonPair_toJson, valueOfWith_array]
      case h_3 => simp only [strOf, pure, Except.pure, byteArray_toList, ofHex_hexString]
      case h_4 => rfl
      case h_5 =>
        cases itemsOf body with
        | error e => rfl
        | ok items =>
          simp only [Functor.map, Except.map, Array.mapM_map, Function.comp_def,
            getBool?_toJson]
      case h_6 =>
        cases itemsOf body with
        | error e => rfl
        | ok items =>
          simp only [Functor.map, Except.map, Array.toList_map, List.mapM_map, Function.comp_def,
            ← ih, ← Array.foldlM_toList]
          let step := fun (acc : List Value) item => (do return (← valueOf fuel item) :: acc :
            Except String (List Value))
          change (Value.seq ∘ List.reverse) <$> items.toList.foldlM step [] =
            Value.seq <$> items.toList.mapM (valueOf fuel)
          rw [comp_map, reverse_foldlM_cons]
          rfl
      case h_7 =>
        cases pair body with
        | error e => rfl
        | ok items =>
          simp only [Functor.map, Except.map, getNat?_toJson, ← ih]

private theorem unpack_foldlM
    (readPacked : PyValue → Except String (ValueOf ByteArray))
    (readArrays : PyValue → Except String Value)
    (same : ∀ item, (readPacked item).map ValueOf.toArrayValue = readArrays item) :
    ∀ (items : List PyValue) (acc : List (ValueOf ByteArray)),
      (items.foldlM (fun values item => return (← readPacked item) :: values) acc).map
        ValueOf.toArrayValues =
        items.foldlM (fun values item => return (← readArrays item) :: values)
          (ValueOf.toArrayValues acc) := by
  intro items
  induction items with
  | nil => intro acc; rfl
  | cons item rest ih =>
    intro acc
    simp only [List.foldlM_cons, ← same item, Bind.bind, Except.bind, Except.map]
    cases readPacked item with
    | error => rfl
    | ok value => exact ih (value :: acc)

/-- Keeping packed byte leaves reads exactly the same value and error. -/
theorem valueOfWith_packed_eq (fuel : Nat) (value : PyValue) :
    (valueOfWith id ByteArray.mk fuel value).map ValueOf.toArrayValue = valueOf fuel value := by
  induction fuel generalizing value with
  | zero => rfl
  | succ fuel ih =>
    rw [valueOf, valueOfWith, valueOfWith]
    cases read : tagged value with
    | error => rfl
    | ok entry =>
      obtain ⟨key, body⟩ := entry
      simp only [Bind.bind, Except.bind]
      split
      case h_1 => cases boolOf body <;> rfl
      case h_2 => cases natOf body <;> rfl
      case h_3 => rfl
      case h_4 =>
        cases strOf body with
        | error => rfl
        | ok text =>
          simp only []
          cases ofHex text <;> rfl
      case h_5 =>
        cases itemsOf body with
        | error => rfl
        | ok items =>
          simp only []
          cases items.mapM boolOf <;> rfl
      case h_6 =>
        cases itemsOf body with
        | error => rfl
        | ok items =>
          simp only [← Array.foldlM_toList]
          let readPacked := valueOfWith id ByteArray.mk fuel
          let readArrays := valueOf fuel
          let stepPacked := fun (values : List (ValueOf ByteArray)) item =>
            (do return (← readPacked item) :: values : Except String (List (ValueOf ByteArray)))
          let stepArrays := fun (values : List Value) item =>
            (do return (← readArrays item) :: values : Except String (List Value))
          have folded : (items.toList.foldlM stepPacked []).map ValueOf.toArrayValues =
              items.toList.foldlM stepArrays [] := unpack_foldlM readPacked readArrays ih _ _
          change Except.map ValueOf.toArrayValue
              (do return .seq (← items.toList.foldlM stepPacked []).reverse) =
            (do return .seq (← items.toList.foldlM stepArrays []).reverse)
          rw [← folded]
          cases items.toList.foldlM stepPacked [] <;>
            simp [Except.map, Bind.bind, Except.bind, pure, Except.pure, ValueOf.toArrayValue,
              ValueOf.toArrayValues_eq, List.map_reverse]
      case h_7 =>
        cases pair body with
        | error => rfl
        | ok parts =>
          simp only []
          cases natOf parts.1 with
          | error => rfl
          | ok selector =>
            change Except.map ValueOf.toArrayValue
              (do return .union selector (← valueOfWith id ByteArray.mk fuel parts.2)) =
              (do return .union selector (← valueOf fuel parts.2))
            rw [← ih parts.2]
            cases valueOfWith id ByteArray.mk fuel parts.2 <;> rfl
      case h_8 => rfl

/-- The packed encoder agrees with first unpacking the value and encoding ordinary arrays. -/
theorem serializeValueOf_eq_array (shape : Desc) (value : PyValue) :
    serializeValueOf shape value = (do
      let unpacked ← readValue "value" value (valueOf MAX_NESTING)
      return ⟨← runSsz "value rejected" (serialize shape unpacked)⟩) := by
  unfold serializeValueOf readValue
  rw [← valueOfWith_packed_eq MAX_NESTING value]
  cases valueOfWith id ByteArray.mk MAX_NESTING value with
  | error => rfl
  | ok packed =>
    have written := serialize_data_eq shape packed
    simp only [Except.map, Except.mapError, Bind.bind, Except.bind]
    rw [← written]
    cases serialize shape packed <;> rfl

private theorem expandedBatch_reads (batch : BytesBatch)
    (outer : batch.outerKey = "seq") (inner : batch.itemKey = "bytes") (fuel : Nat) :
    valueOf (fuel + 2) batch.toPyValue = .ok (.seq ((List.range batch.count).map fun i =>
      .bytes (batch.data.data.extract (i * batch.width) ((i + 1) * batch.width)))) := by
  let item (i : Fin batch.count) : PyValue :=
    .dict #[(batch.itemKey, .bytes (batch.data.extract (i.val * batch.width)
      (i.val * batch.width + batch.width)))]
  let decoded (i : Fin batch.count) : Value :=
    .bytes (batch.data.data.extract (i.val * batch.width) ((i.val + 1) * batch.width))
  have readItem (i : Fin batch.count) : valueOf (fuel + 1) (item i) = .ok (decoded i) := by
    unfold item valueOf
    rw [inner, valueOfWith]
    simp [tagged, decoded, ByteArray.data_extract, Nat.succ_mul, Bind.bind, Except.bind,
      pure, Except.pure]
  have readItems : (List.ofFn item).mapM (valueOf (fuel + 1)) = .ok (List.ofFn decoded) := by
    let positions := List.finRange batch.count
    have indexItem : List.ofFn item = positions.map item := by
      simp [positions, List.finRange, Function.comp_def]
    have indexDecoded : List.ofFn decoded = positions.map decoded := by
      simp [positions, List.finRange, Function.comp_def]
    rw [indexItem, indexDecoded, List.mapM_map]
    have reads : valueOf (fuel + 1) ∘ item = pure ∘ decoded := funext readItem
    rw [reads]
    exact List.mapM_pure
  have ordered : List.ofFn decoded = (List.range batch.count).map (fun i => .bytes
      (batch.data.data.extract (i * batch.width) ((i + 1) * batch.width))) := by
    apply List.ext_getElem?
    intro i
    by_cases inside : i < batch.count <;>
      simp [inside, decoded]
  unfold BytesBatch.toPyValue valueOf
  rw [outer, valueOfWith]
  let step := fun (acc : List Value) py =>
    (do return (← valueOf (fuel + 1) py) :: acc : Except String (List Value))
  change (Value.seq ∘ List.reverse) <$> (Array.ofFn item).foldlM step [] = _
  rw [← Array.foldlM_toList, comp_map, reverse_foldlM_cons, Array.toList_ofFn]
  change Value.seq <$> (List.ofFn item).mapM (valueOf (fuel + 1)) = _
  rw [readItems, ordered]
  rfl

/-- The batched export returns the same bytes or error as its expanded tagged value. -/
theorem serializeBytesBatchOf_eq (type : PyValue) (batch : BytesBatch) :
    serializeBytesBatchOf (type, batch) = serializeOf (type, batch.toPyValue) := by
  simp only [serializeBytesBatchOf, serializeOf, Bind.bind, Except.bind]
  cases readType type with
  | error => rfl
  | ok shape =>
    by_cases compact : batch.matches shape = true
    · simp only [compact, ↓reduceIte]
      rw [serializeValueOf_eq_array]
      cases shape <;> try simp [BytesBatch.matches] at compact
      case vector element count =>
        cases element <;> try simp at compact
        case byteVector width =>
          simp only [and_assoc] at compact
          obtain ⟨outer, inner, counted, wide, sized, bounded⟩ := compact
          subst count
          subst width
          have read := expandedBatch_reads batch outer inner (MAX_NESTING - 2)
          change valueOf MAX_NESTING batch.toPyValue = _ at read
          have written := serialize_byteVectorSlices batch.data.data batch.width batch.count
            sized bounded
          have packedSize : ByteBuffer.size batch.data = batch.data.size := rfl
          simp [readValue, read, written, serialize, packedSize, Nat.not_le_of_lt bounded,
            runSsz, Bind.bind, Except.bind, Except.mapError, pure, Except.pure]
    · simp [compact]

/-- A vector of complete nodes supplies those nodes to the bounded tree. -/
private theorem hashTreeRoot_vector_nodes (chunks : Array Bytes)
    (whole : ∀ i (inside : i < chunks.size), chunks[i].size = bytesPerChunk) :
    hashTreeRoot (.vector (.byteVector bytesPerChunk) chunks.size)
        (.seq (chunks.toList.map ValueOf.bytes)) =
      merkleizeBoundedUnchecked chunks (some chunks.size) := by
  let slots := chunks.toList.map fun node =>
    some (Desc.byteVector bytesPerChunk, ValueOf.bytes node)
  have layout :
      merkleLayout (.vector (.byteVector bytesPerChunk) chunks.size)
          (.seq (chunks.toList.map ValueOf.bytes)) =
        .ok (.nesting slots (some chunks.size) none) := by
    simp [slots, merkleLayout, sequenceLayout, Desc.isBasic, Function.comp_def, pure, Except.pure]
  have rooted : layoutChunksAt 1 (.nesting slots (some chunks.size) none) = .ok chunks := by
    rw [layoutChunksAt_eq]
    simp only [MerkleLayout.nesting, Leaves.count, Option.getD_none, Nat.sub_zero,
      List.drop_zero, List.take_length, slots, List.mapM_map]
    have each (node : Bytes) (mem : node ∈ chunks.toList) :
        hashTreeRootAt 1 (.byteVector bytesPerChunk) (.bytes node) = .ok node := by
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (by simpa using mem)
      exact hashTreeRoot_chunk (whole i hi)
    have mapped (nodes : List Bytes) (member : ∀ node ∈ nodes, node ∈ chunks.toList) :
        nodes.mapM (fun node => hashTreeRootAt 1 (.byteVector bytesPerChunk) (.bytes node)) =
          .ok nodes := by
      induction nodes with
      | nil => rfl
      | cons node rest ih =>
        have head := each node (member node List.mem_cons_self)
        have tail := ih fun other mem => member other (List.mem_cons_of_mem _ mem)
        simp [List.mapM_cons, head, tail, Bind.bind, Except.bind, pure, Except.pure]
    change (do
      let leaves ← chunks.toList.mapM (fun node => hashTreeRootAt 1 (.byteVector bytesPerChunk)
        (.bytes node))
      return leaves.toArray : Except Err (Array Bytes)) = _
    rw [mapped _ fun _ mem => mem]
    simp [Bind.bind, Except.bind, pure, Except.pure]
  rw [hashTreeRoot_eq_nesting]
  change hashTreeRootAt (1 + 1) _ _ = _
  simp only [hashTreeRootAt_succ, layout, Bind.bind, Except.bind, rooted]
  simp only [MerkleLayout.nesting]
  cases merkleizeBoundedUnchecked chunks (some chunks.size) <;> rfl

private theorem packBytes_vector_slices (data : ByteArray) (count : Nat)
    (sized : data.size = count * bytesPerChunk) :
    (packBytes data.data).toList = (List.range count).map fun i =>
      data.data.extract (i * bytesPerChunk) ((i + 1) * bytesPerChunk) := by
  have size : (packBytes data.data).size = count := by
    rw [packBytes_size, ByteArray.size_data, sized]
    simp only [bytesPerChunk]
    omega
  apply List.ext_getElem?
  intro i
  by_cases inside : i < count
  · have bound : (i + 1) * bytesPerChunk ≤ data.data.size := by
      rw [ByteArray.size_data, sized]
      exact Nat.mul_le_mul_right _ (by omega)
    have full : (data.data.extract (i * bytesPerChunk) ((i + 1) * bytesPerChunk)).size =
        bytesPerChunk := by
      rw [Array.size_extract, Nat.min_eq_left bound, Nat.succ_mul, Nat.add_sub_cancel_left]
    have node : (packBytes data.data)[i]'(by rw [size]; exact inside) =
        data.data.extract (i * bytesPerChunk) ((i + 1) * bytesPerChunk) := by
      simp only [packBytes_eq, Array.getElem_ofFn]
      rw [show i * bytesPerChunk + bytesPerChunk = (i + 1) * bytesPerChunk by
        rw [Nat.succ_mul]]
      simp [full]
    simp [inside, size, node]
  · simp [inside, size]

/-- The byte batch has the root of its expanded tagged value. -/
theorem hashTreeRootBytesBatchOf_eq (type : PyValue) (batch : BytesBatch) :
    hashTreeRootBytesBatchOf (type, batch) = hashTreeRootOf (type, batch.toPyValue) := by
  simp only [hashTreeRootBytesBatchOf, hashTreeRootOf, Bind.bind, Except.bind]
  cases readType type with
  | error => rfl
  | ok shape =>
    by_cases fast : (batch.width == bytesPerChunk && batch.matches shape) = true
    · simp only [fast, ↓reduceIte]
      simp only [Bool.and_eq_true, beq_iff_eq] at fast
      obtain ⟨atWidth, compact⟩ := fast
      cases shape <;> try simp [BytesBatch.matches] at compact
      case vector element count =>
        cases element <;> try simp at compact
        case byteVector width =>
          simp only [and_assoc] at compact
          obtain ⟨outer, inner, counted, wide, sized, _⟩ := compact
          subst count width
          rw [atWidth] at sized
          have read := expandedBatch_reads batch outer inner (MAX_NESTING - 2)
          change valueOf MAX_NESTING batch.toPyValue = _ at read
          rw [atWidth] at read
          rw [show (fun i => ValueOf.bytes (batch.data.data.extract (i * bytesPerChunk)
              ((i + 1) * bytesPerChunk))) = ValueOf.bytes ∘
                (fun i => batch.data.data.extract (i * bytesPerChunk)
                  ((i + 1) * bytesPerChunk)) from rfl, ← List.map_map,
            ← packBytes_vector_slices batch.data batch.count sized] at read
          let chunks := packBytes batch.data.data
          have count : chunks.size = batch.count := by
            rw [show chunks = packBytes batch.data.data by rfl, packBytes_size,
              ByteArray.size_data, sized]
            simp only [bytesPerChunk]
            omega
          have rooted := hashTreeRoot_vector_nodes chunks (packBytes_chunk_size batch.data.data)
          rw [count] at rooted
          have packed :
              (merkleizePackedBoundedUnchecked batch.data (some batch.count)).run =
                merkleizeBoundedUnchecked chunks (some batch.count) := by
            rw [merkleizePackedBoundedUnchecked_eq]
            rfl
          dsimp [chunks] at rooted packed
          simp [hashTreeRootValueOf, readValue, read, atWidth, rooted, packed, Except.mapError,
            Bind.bind, Except.bind]
    · simp [fast]

private theorem expandedNatBatch_reads {B : Type} (native : ByteArray → B)
    (hex : Array UInt8 → B) (batch : NatBatch)
    (outer : batch.outerKey = "seq") (inner : batch.itemKey = "uint") (fuel : Nat) :
    valueOfWith native hex (fuel + 2) batch.toPyValue =
      .ok (.seq (batch.values.toList.map ValueOf.uint)) := by
  let item := fun n : Nat => PyValue.dict #[(batch.itemKey, .int n)]
  let read := valueOfWith native hex (fuel + 1)
  have readItem (n : Nat) : read (item n) = .ok (ValueOf.uint n) := by
    unfold read item
    rw [inner, valueOfWith]
    simp [tagged, natOf, Bind.bind, Except.bind, pure, Except.pure]
  unfold NatBatch.toPyValue
  rw [outer, valueOfWith]
  let step := fun (acc : List (ValueOf B)) py =>
    (do return (← read py) :: acc : Except String (List (ValueOf B)))
  change (ValueOf.seq ∘ List.reverse) <$> (batch.values.map item).foldlM step [] = _
  rw [← Array.foldlM_toList, comp_map, reverse_foldlM_cons, Array.toList_map]
  change ValueOf.seq <$> (batch.values.toList.map item).mapM read = _
  rw [List.mapM_map, show read ∘ item = pure ∘ ValueOf.uint from funext readItem]
  simp [Function.comp_def]
  rfl

private theorem natBatch_read_eq {B : Type} (native : ByteArray → B) (hex : Array UInt8 → B)
    (batch : NatBatch) :
    NatBatch.read (valueOfWith native hex MAX_NESTING) batch =
      readValue "value" batch.toPyValue (valueOfWith native hex MAX_NESTING) := by
  unfold NatBatch.read
  split
  · rename_i tags
    obtain ⟨outer, inner⟩ : batch.outerKey = "seq" ∧ batch.itemKey = "uint" := by
      simpa using tags
    have expanded := expandedNatBatch_reads native hex batch outer inner (MAX_NESTING - 2)
    change valueOfWith native hex MAX_NESTING batch.toPyValue = _ at expanded
    rw [readValue, expanded]
    rfl
  · rfl

/-- The number batch serializes as its expanded tagged value. -/
theorem serializeNatBatchOf_eq (type : PyValue) (batch : NatBatch) :
    serializeNatBatchOf (type, batch) = serializeOf (type, batch.toPyValue) := by
  simp [serializeNatBatchOf, serializeOf, serializeValueOf, natBatch_read_eq]

private theorem serializeEach_uints (width : Nat) (values : List Nat) :
    serializeEach (.uint width) (values.map ValueOf.uint) =
      if values.all (uintFits width) then .ok (values.map (uintBytes width))
      else .error .typeMismatch := by
  induction values with
  | nil => simp [serializeEach]
  | cons n rest ih =>
    simp only [List.map_cons, serializeEach_cons, serialize, List.all_cons, ih]
    cases uintFits width n <;> cases rest.all (uintFits width) <;>
      simp [Bind.bind, Except.bind, pure, Except.pure, ByteBuffer.ofArray]

private theorem data_foldl_uintBytes (width : Nat) (values : List Nat) (out : ByteArray) :
    (values.foldl (fun acc n => SszType.pushUintBytes width n acc) out).data =
      (values.map (uintBytes width)).foldl (· ++ ·) out.data := by
  induction values generalizing out with
  | nil => rfl
  | cons n rest ih =>
    rw [List.foldl_cons, ih, SszType.data_pushUintBytes, List.map_cons, List.foldl_cons]

private theorem hashTreeRootNatList_eq (width limit : Nat) (values : Array Nat) :
    hashTreeRootNatList width limit values =
      hashTreeRoot (.list (.uint width) limit) (.seq (values.toList.map ValueOf.uint)) := by
  let initial := ByteArray.emptyWithCapacity (values.size * width)
  let data := values.foldl (fun out n => SszType.pushUintBytes width n out) initial
  have written : data.data = concatParts (values.toList.map (uintBytes width)) := by
    rw [show data = values.foldl (fun out n => SszType.pushUintBytes width n out) initial from rfl,
      ← Array.foldl_toList, data_foldl_uintBytes, fold_parts_eq_concat,
      show initial.data = #[] from rfl, Array.empty_append]
  simp only [hashTreeRootNatList, hashTreeRoot, hashTreeRootM, Desc.nesting, hashTreeRootAtM,
    listLayout, merkleLayout, List.length_map, Array.length_toList, sequenceLayout, Desc.isBasic,
    ite_true, serializeEach_uints, Array.all_toList, ExceptT.run, EthLib.Base.exceptT_id_bind,
    EthLib.Base.exceptT_id_monadLift]
  by_cases over : limit < values.size
  · simp [over, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
  · cases values.all (uintFits width) with
    | false => simp [over, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
    | true =>
      simp [over, pure, Except.pure, Bind.bind, Except.bind, packedSequenceLayout]
      change (hashLayoutFromM sha256Hasher (lengthWord values.size)
        (merkleizePackedBoundedUnchecked data _)).run = _
      simp [merkleizePackedBoundedUnchecked_eq, written, packElements, fold_parts_eq_concat,
        layoutChunksAtM, MerkleLayout.packing, hashLayoutChunksM, pure]
      rfl

/-- The number batch has the root of its expanded tagged value. -/
theorem hashTreeRootNatBatchOf_eq (type : PyValue) (batch : NatBatch) :
    hashTreeRootNatBatchOf (type, batch) = hashTreeRootOf (type, batch.toPyValue) := by
  simp only [hashTreeRootNatBatchOf, hashTreeRootOf, hashTreeRootValueOf, valueOf, Bind.bind,
    Except.bind]
  rw [← natBatch_read_eq]
  cases readType type with
  | error => rfl
  | ok shape =>
    cases shape <;> try rfl
    case list element limit =>
      cases element <;> try rfl
      case uint width =>
        by_cases tags : (batch.outerKey == "seq" && batch.itemKey == "uint") = true
        · simp [NatBatch.read, tags, hashTreeRootNatList_eq]
        · simp [tags]

/-- Writing a value gives the Python value that its JSON gave. -/
theorem pyOfValue_eq_json (value : Value) :
    pyOfValue value = PyValue.ofJson (jsonOfValue value) :=
  pyOfValue_eq_json_aux value

/-- Decode a Python value by writing it as JSON and reading the JSON. -/
noncomputable def jsonReadValue {α : Type} (what : String) (value : PyValue)
    (decode : Json → Except String α) : EthLib.Exports.Result α :=
  (decode value.toJson).mapError fun e => (0, s!"{what}: {e}")

/-- An export reads a type as it read the JSON of the type. -/
theorem readValue_descOf (what : String) (fuel : Nat) (type : PyValue) :
    readValue what type (descOf fuel) = jsonReadValue what type (jsonDescOf fuel) := by
  simp [readValue, jsonReadValue, descOf_eq_json]

/-- An export reads a value as it read the JSON of the value. -/
theorem readValue_valueOf (what : String) (fuel : Nat) (value : PyValue) :
    readValue what value (valueOf fuel) = jsonReadValue what value (jsonValueOf fuel) := by
  simp [readValue, jsonReadValue, valueOf_eq_json]

end EthLib.Serialization.Ssz.Exports.Proofs
