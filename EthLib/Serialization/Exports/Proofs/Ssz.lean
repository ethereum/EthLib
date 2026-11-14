module

public import Lean.Data.Json
public import EthLib.Serialization.Ssz.Codec.Json
public import EthLib.Serialization.Exports.Ssz
import all EthLib.Serialization.Exports.Ssz
import all EthLib.Base.Exports.PyValue
import all Lean.Data.Json.Basic
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
  have h : Json.mkObj [(key, j)] = .obj ⟨⟨.inner 1 key j .leaf .leaf⟩⟩ := rfl
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
  cases value <;> simp [PyValue.toJson, natOf, Json.getNat?, Json.mkObj] <;> rfl

/-- Reading a boolean from JSON reads it from the Python value. -/
private theorem getBool?_toJson (value : PyValue) : value.toJson.getBool? = boolOf value := by
  cases value <;> simp [PyValue.toJson, boolOf, Json.getBool?, Json.mkObj] <;> rfl

/-- Reading a text from JSON reads it from the Python value. -/
private theorem getStr?_toJson (value : PyValue) : value.toJson.getStr? = strOf value := by
  cases value <;> simp [PyValue.toJson, strOf, Json.getStr?, Json.mkObj] <;> rfl

/-- Reading an array from JSON reads the items of the Python value, as JSON. -/
private theorem getArr?_toJson (value : PyValue) :
    value.toJson.getArr? = (·.map PyValue.toJson) <$> itemsOf value := by
  cases value <;> simp [PyValue.toJson, itemsOf, Json.getArr?, Json.mkObj, toJsonArray_eq] <;> rfl

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
  rw [Json.mkObj, Std.TreeMap.Raw.ofList_cons, single, insertMany_single _ _ _ same]
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
  rw [Json.mkObj]
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
    · rfl
    · simp only [List.concat_eq_append]
      simp [tagged]
      by_cases same : ∀ entry ∈ init, entry.1 = key
      · have all : (⟨init ++ [(key, value)]⟩ : Array (String × PyValue)).all
            (fun entry => entry.1 == key) = true := by
          simpa using same
        simp only [all, ↓reduceIte]
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
        simp only [notAll]
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
  | dict entries => simp [PyValue.toJson, Json.mkObj]
  | _ => simp [PyValue.toJson]

/-- Reading an optional natural number from JSON reads it from the Python value. -/
private theorem jsonOptionalNat_toJson (value : PyValue) :
    jsonOptionalNat value.toJson = optionalNat value := by
  cases value <;> rfl

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

/-- Reading a value gives what reading its JSON gave, the same value or the same error. -/
theorem valueOf_eq_json (fuel : Nat) (value : PyValue) :
    valueOf fuel value = jsonValueOf fuel value.toJson := by
  induction fuel generalizing value with
  | zero => rfl
  | succ fuel ih =>
    rw [valueOf, jsonValueOf, jsonTagged_toJson]
    cases tagged value with
    | error e => rfl
    | ok entry =>
      obtain ⟨key, body⟩ := entry
      simp only [Functor.map, Except.map, bind, Except.bind]
      split
      all_goals simp only [getBool?_toJson, getNat?_toJson, getStr?_toJson, getArr?_toJson,
        jsonPair_toJson]
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
            ← ih]
      case h_7 =>
        cases pair body with
        | error e => rfl
        | ok items =>
          simp only [Functor.map, Except.map, getNat?_toJson, ← ih]

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
