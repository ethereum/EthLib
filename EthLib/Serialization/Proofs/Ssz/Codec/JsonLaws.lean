module

public import EthLib.Serialization.Proofs.Ssz.Codec.JsonHex
public import EthLib.Serialization.Proofs.Ssz.Codec.RoundTrip
public import Std.Data.TreeMap.Raw.WF
public import Std.Data.TreeMap.Raw.Lemmas
public import Std.Data.String.ToNat
-- The round-trip proof unfolds Lean's `Json.mkObj` and `Json.getObjVal?`.
import all Lean.Data.Json.Basic

/-! Reading back what the JSON mapping writes, and what the mapping does not pin down. -/

@[expose] public section

namespace EthLib.Serialization.Ssz

open Lean Std

/--
A name written into an object is read back from it, when no name was written twice.

A struct's field names are distinct by declaration, which is what makes this apply to one.
-/
theorem getObjVal?_mkObj {pairs : List (String × Json)} {name : String} {value : Json}
    (distinct : pairs.Pairwise fun a b => a.1 ≠ b.1) (member : (name, value) ∈ pairs) :
    (Json.mkObj pairs).getObjVal? name = .ok value := by
  -- Distinct names stay distinct under the order an object is built with.
  have keys : pairs.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    exact distinct.imp fun different equal => different (compare_eq_iff_eq.mp equal)
  have read := Std.TreeMap.Raw.getElem?_ofList_of_mem (cmp := compare) compare_self keys member
  simp only [Json.mkObj, Json.getObjVal?, Std.TreeMap.Raw.get?_eq_getElem?, read]
  rfl

/-- A name that was not written into an object is not found in it.

The lookup fails with the message that names the missing property. -/
theorem getObjVal?_mkObj_of_not_mem {pairs : List (String × Json)} {name : String}
    (absent : name ∉ pairs.map Prod.fst) :
    (Json.mkObj pairs).getObjVal? name = .error s!"property not found: {name}" := by
  have none : (Std.TreeMap.Raw.ofList pairs (cmp := compare))[name]? = none :=
    Std.TreeMap.Raw.getElem?_ofList_of_contains_eq_false (by simpa using absent)
  simp only [Json.mkObj, Json.getObjVal?, Std.TreeMap.Raw.get?_eq_getElem?, none]
  rfl

/--
Every name an object carries is one of the names it was written from.

A written struct therefore never trips the undeclared-field refusal.
-/
theorem objectNames_mkObj {pairs : List (String × Json)} {name : String}
    (member : name ∈ objectNames (Json.mkObj pairs)) : name ∈ pairs.map Prod.fst := by
  have wf : (Std.TreeMap.Raw.ofList pairs (cmp := compare)).WF := Std.TreeMap.Raw.WF.ofList
  simp only [objectNames, Json.mkObj] at member
  rw [Std.TreeMap.Raw.map_fst_toList_eq_keys] at member
  simpa using Std.TreeMap.Raw.mem_ofList.mp ((Std.TreeMap.Raw.mem_keys wf).mp member)

/-- The digits of a number read back as that number, however the string was reached. -/
@[simp] theorem readNat_str (n : Nat) : readNat (.str (toString n)) = .ok n := by
  -- The digits `toString` writes are the ones `Nat.ofDigitChars` reads.
  simp [readNat, Nat.toString_eq_repr, Nat.toList_repr, Nat.ofDigitChars_ten_toDigits]

@[simp, inherit_doc readNat_str] theorem readNat_decimal (n : Nat) :
    readNat (decimal n) = .ok n := readNat_str n

/-- A boolean document reads back as the boolean it was written from. -/
theorem valueOf_jsonOf_bool {spelling : Spelling} {b : Bool} {document : Json}
    (written : jsonOf .bool spelling (.bool b) = .ok document) :
    valueOf .bool spelling document = .ok (.bool b) := by
  simp only [jsonOf, Except.ok.injEq] at written
  subst written
  rw [valueOf]

/--
An unsigned integer document reads back as the integer it was written from.

The alias marks a one-byte integer, so the one byte its hex names is the whole value.

Every other spelling writes the digits, which read back at any width.
-/
theorem valueOf_jsonOf_uint {spelling : Spelling} {width n : Nat} {document : Json}
    (fitted : n < 2 ^ (8 * width))
    (written : jsonOf (.uint width) spelling (.uint n) = .ok document) :
    valueOf (.uint width) spelling document = .ok (.uint n) := by
  have wide : ¬ (2 ^ (8 * width) ≤ n) := Nat.not_le.mpr fitted
  rw [jsonOf] at written
  by_cases alias? : (spelling.isByte && width == 1) = true
  · have single : width = 1 := by simpa using ((Bool.and_eq_true ..).mp alias?).2
    have small : n < 256 := by rw [single] at fitted; simpa using fitted
    have byte : (UInt8.ofNat n).toNat = n := by
      simpa [UInt8.toNat_ofNat] using Nat.mod_eq_of_lt small
    simp only [wide, ite_false, alias?, ite_true, Except.ok.injEq] at written
    subst written
    rw [valueOf, ite_eq_left alias?]
    simp [ofHex_toHex, byte, Bind.bind, Except.bind, pure, Except.pure]
  · rw [ite_eq_right wide, ite_eq_right (by simpa using alias?), Except.ok.injEq] at written
    subst written
    -- The digits have to be a constructor before the reader's own match can reduce.
    simp only [decimal]
    rw [valueOf, ite_eq_right alias?, readNat_str]
    simp [wide, Bind.bind, Except.bind, pure, Except.pure]

/-- A byte array document reads back as the bytes it was written from. -/
theorem valueOf_jsonOf_byteVector {spelling : Spelling} {length : Nat} {data : Bytes}
    {document : Json} (fitted : data.size = length)
    (written : jsonOf (.byteVector length) spelling (.bytes data) = .ok document) :
    valueOf (.byteVector length) spelling document = .ok (.bytes data) := by
  simp only [jsonOf, fitted, beq_self_eq_true, ↓reduceIte, Except.ok.injEq] at written
  subst written
  rw [valueOf]
  simp [collectionHex, ofHex_toHex, fitted, Bind.bind, Except.bind, pure, Except.pure]

/-- Reading decimal strings appends the bytes that they hold to the bytes so far. -/
theorem byteDigitsFrom_map : ∀ (bytes : List UInt8) (out : Bytes),
    byteDigitsFrom (bytes.map fun byte => decimal byte.toNat) out = .ok (out ++ bytes.toArray)
  | [], out => by simp [byteDigitsFrom]
  | byte :: rest, out => by
    have small : ¬ byte.toNat ≥ 256 := by have := byte.toNat_lt; omega
    simp only [List.map_cons, byteDigitsFrom, readNat_decimal, Bind.bind, Except.bind, small,
      ite_false, UInt8.ofNat_toNat, byteDigitsFrom_map rest]
    simp

/-- A byte list document reads back as the bytes it was written from. -/
theorem valueOf_jsonOf_byteList {spelling : Spelling} {limit : Nat} {data : Bytes}
    {document : Json} (fitted : data.size ≤ limit)
    (written : jsonOf (.byteList limit) spelling (.bytes data) = .ok document) :
    valueOf (.byteList limit) spelling document = .ok (.bytes data) := by
  simp only [jsonOf, fitted, ↓reduceIte, Except.ok.injEq, byteListJson] at written
  by_cases digits : spelling.isDigits = true
  · simp only [digits, ↓reduceIte] at written
    subst written
    rw [valueOf]
    simp [digits, Array.toList_map, byteDigitsFrom_map, Nat.not_lt.mpr fitted, Bind.bind,
      Except.bind, pure, Except.pure]
  · rw [Bool.not_eq_true] at digits
    simp only [digits, Bool.false_eq_true, ↓reduceIte] at written
    subst written
    rw [valueOf]
    simp [digits, collectionHex, ofHex_toHex, Nat.not_lt.mpr fitted, Bind.bind, Except.bind,
      pure, Except.pure]
    intro _ same
    cases same

/--
A bitfield document reads back as the bits it was written from.

A bitfield is written as the hex of its own encoding, so the codec is what reads it back.
-/
theorem valueOf_jsonOf_bitVector {spelling : Spelling} {data : Array Bool} {document : Json}
    (legal : (Desc.bitVector data.size).wellFormed = .ok ())
    (fitted : Fits (.bitVector data.size) (.bits data))
    (written : jsonOf (.bitVector data.size) spelling (.bits data) = .ok document) :
    valueOf (.bitVector data.size) spelling document = .ok (.bits data) := by
  have wrote : serialize (.bitVector data.size) (.bits data)
      = .ok (packBits data ((data.size + 7) / 8)) := by simp [serialize]
  have back := roundTrip_of_wellFormed legal fitted wrote
  simp only [jsonOf, wrote, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at written
  subst written
  rw [valueOf]
  simp [readBitfield, collectionHex, ofHex_toHex, back, Bind.bind, Except.bind,
    pure, Except.pure]

@[inherit_doc valueOf_jsonOf_bitVector]
theorem valueOf_jsonOf_bitList {spelling : Spelling} {limit : Nat} {data : Array Bool}
    {document : Json} (within : data.size ≤ limit)
    (legal : (Desc.bitList limit).wellFormed = .ok ())
    (fitted : Fits (.bitList limit) (.bits data))
    (written : jsonOf (.bitList limit) spelling (.bits data) = .ok document) :
    valueOf (.bitList limit) spelling document = .ok (.bits data) := by
  have wrote : serialize (.bitList limit) (.bits data) = .ok (packBitsDelimited data) := by
    simp [serialize, within]
  have back := roundTrip_of_wellFormed legal fitted wrote
  simp only [jsonOf, wrote, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at written
  subst written
  rw [valueOf]
  simp [readBitfield, collectionHex, ofHex_toHex, back, Bind.bind, Except.bind,
    pure, Except.pure]

@[inherit_doc valueOf_jsonOf_bitVector]
theorem valueOf_jsonOf_progressiveBitList {spelling : Spelling} {limit : Option Nat}
    {data : Array Bool} {document : Json}
    (within : withinBound limit data.size = true)
    (legal : (Desc.progressiveBitList limit).wellFormed = .ok ())
    (fitted : Fits (.progressiveBitList limit) (.bits data))
    (written : jsonOf (.progressiveBitList limit) spelling (.bits data) = .ok document) :
    valueOf (.progressiveBitList limit) spelling document = .ok (.bits data) := by
  have wrote : serialize (.progressiveBitList limit) (.bits data)
      = .ok (packBitsDelimited data) := by
    simp [serialize, boundCheck_of_withinBound limit _ within, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  have back := roundTrip_of_wellFormed legal fitted wrote
  simp only [jsonOf, wrote, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at written
  subst written
  rw [valueOf]
  simp [readBitfield, collectionHex, ofHex_toHex, back, Bind.bind, Except.bind,
    pure, Except.pure]

/--
The mapping is not canonical: two documents give one value.

A hex digit is read in either letter case.

So a byte array has as many documents as its bytes have spellings.

The byte encoding pins one string per value, and nothing here does the same for documents.
-/
theorem valueOf_not_canonical :
    ∃ (shape : Desc) (spelling : Spelling) (left right : Json) (value : Value),
      left ≠ right ∧ valueOf shape spelling left = .ok value
        ∧ valueOf shape spelling right = .ok value := by
  have lower : ofHex "0x0a" = .ok #[10] := by rfl
  have upper : ofHex "0x0A" = .ok #[10] := by rfl
  refine ⟨.byteVector 1, .opaque, .str "0x0a", .str "0x0A", .bytes #[10], by simp, ?_, ?_⟩ <;>
    simp [valueOf, collectionHex, lower, upper, Bind.bind, Except.bind, pure, Except.pure]


/--
A struct read stops at the first declared field its object leaves out.
Fields are read in declaration order, and an earlier refusal also counts.
-/
theorem valueOfFields_missing {name : String} {document : Json}
    (absent : (document.getObjVal? name).toOption = none) :
    ∀ (fields : List Desc) (names : List String) (spelling : Spelling) (start ordinal : Nat),
      names.getD ordinal "" = name → start ≤ ordinal → ordinal < start + fields.length →
      ∃ fault, valueOfFields fields names spelling start document = .error fault := by
  intro fields
  induction fields with
  | nil => intro _ _ _ _ _ _ inside; simp at inside; omega
  | cons field rest ih =>
    intro names spelling start ordinal named after inside
    rw [valueOfFields]
    cases lookup : (document.getObjVal? (names.getD start "")).toOption with
    | none => exact ⟨_, rfl⟩
    | some part =>
      -- The field found here is not the missing one, so the missing one comes later.
      have later : ordinal ≠ start := by
        intro here
        subst here named
        rw [absent] at lookup
        contradiction
      obtain ⟨fault, failed⟩ := ih names spelling (start + 1) ordinal named (by omega)
        (by simp at inside; omega)
      cases read : valueOf field (spelling.part start) part <;>
        simp [read, failed, Bind.bind, Except.bind]

/--
A container document missing a declared field is refused.
The mapping asks every field of the schema to be present with a value.
-/
theorem valueOf_container_missing_field {names : List String} {fields : List Desc}
    {spelling : Spelling} {document : Json} {ordinal : Nat} {name : String}
    (named : names[ordinal]? = some name) (declared : ordinal < fields.length)
    (absent : (document.getObjVal? name).toOption = none) :
    ∃ fault, valueOf (.container names fields) spelling document = .error fault := by
  obtain ⟨fault, failed⟩ := valueOfFields_missing absent fields names spelling 0 ordinal
    (by simp [List.getD_eq_getElem?_getD, named]) (Nat.zero_le _) (by omega)
  -- A document that is not an object, or names an undeclared field, is refused before the fields.
  cases document <;> simp only [valueOf] <;> try exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  · simp [failed, Bind.bind, Except.bind]

@[inherit_doc valueOf_container_missing_field]
theorem valueOf_progressiveContainer_missing_field {active : List Bool} {names : List String}
    {fields : List Desc} {spelling : Spelling} {document : Json} {ordinal : Nat}
    {name : String}
    (named : names[ordinal]? = some name) (declared : ordinal < fields.length)
    (absent : (document.getObjVal? name).toOption = none) :
    ∃ fault, valueOf (.progressiveContainer active names fields) spelling document = .error fault := by
  obtain ⟨fault, failed⟩ := valueOfFields_missing absent fields names spelling 0 ordinal
    (by simp [List.getD_eq_getElem?_getD, named]) (Nat.zero_le _) (by omega)
  cases document <;> simp only [valueOf] <;> try exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  · simp [failed, Bind.bind, Except.bind]

/-! ## Objects with the same fields -/

/-- A name that an object holds is among the names that it carries. -/
theorem mem_objectNames {fields : TreeMap.Raw String Json} (wf : fields.WF) {name : String}
    (member : name ∈ fields) : name ∈ objectNames (.obj fields) := by
  simp only [objectNames]
  rw [Std.TreeMap.Raw.map_fst_toList_eq_keys]
  exact (Std.TreeMap.Raw.mem_keys wf).mpr member

/-- Erasing a name just written into an object that did not hold it gives the same fields back. -/
theorem erase_insert_equiv {fields : TreeMap.Raw String Json} (wf : fields.WF) {name : String}
    {value : Json} (absent : name ∉ fields) :
    ((fields.insert name value).erase name).Equiv fields := by
  have wfi := wf.insert (a := name) (b := value)
  refine Std.TreeMap.Raw.Equiv.of_forall_getElem?_eq (wfi.erase) wf fun key => ?_
  rw [Std.TreeMap.Raw.getElem?_erase wfi, Std.TreeMap.Raw.getElem?_insert wf]
  by_cases same : compare name key = .eq
  · have : name = key := compare_eq_iff_eq.mp same
    subst this
    simpa [same] using (Std.TreeMap.Raw.getElem?_eq_none wf absent).symm
  · simp [same]

/-- Two objects with the same fields give the same value under each name. -/
theorem getObjVal?_obj_of_equiv {first second : TreeMap.Raw String Json} (wf₁ : first.WF)
    (wf₂ : second.WF) (same : first.Equiv second) (name : String) :
    (Json.obj first).getObjVal? name = (Json.obj second).getObjVal? name := by
  simp only [Json.getObjVal?, Std.TreeMap.Raw.get?_eq_getElem?]
  rw [Std.TreeMap.Raw.Equiv.getElem?_eq wf₁ wf₂ same]

/-- Two objects with the same fields carry the same names, in the same order. -/
theorem objectNames_obj_of_equiv {first second : TreeMap.Raw String Json} (wf₁ : first.WF)
    (wf₂ : second.WF) (same : first.Equiv second) :
    objectNames (.obj first) = objectNames (.obj second) := by
  have := (Std.TreeMap.Raw.equiv_iff_toList_eq wf₁ wf₂).mp same
  simp [objectNames, this]

/-- A struct's fields are read alike out of two objects with the same fields. -/
theorem valueOfFields_obj_of_equiv {first second : TreeMap.Raw String Json} (wf₁ : first.WF)
    (wf₂ : second.WF) (same : first.Equiv second) :
    ∀ (fields : List Desc) (names : List String) (spelling : Spelling) (start : Nat),
      valueOfFields fields names spelling start (.obj first)
        = valueOfFields fields names spelling start (.obj second) := by
  intro fields
  induction fields with
  | nil => intro names spelling start; simp [valueOfFields]
  | cons field rest ih =>
    intro names spelling start
    rw [valueOfFields, valueOfFields, getObjVal?_obj_of_equiv wf₁ wf₂ same, ih]

/-- Two objects with the same fields read alike against any declaration.

It holds for a refusal as well as a value. -/
theorem valueOf_obj_of_equiv {shape : Desc} {spelling : Spelling}
    {first second : TreeMap.Raw String Json} (wf₁ : first.WF) (wf₂ : second.WF)
    (same : first.Equiv second) :
    valueOf shape spelling (.obj first) = valueOf shape spelling (.obj second) := by
  have names := objectNames_obj_of_equiv wf₁ wf₂ same
  have read := getObjVal?_obj_of_equiv wf₁ wf₂ same
  have fieldsOf := valueOfFields_obj_of_equiv wf₁ wf₂ same
  cases shape <;>
    simp [valueOf, valueOfSequence, readBitfield, readNat, collectionHex, names, read, fieldsOf]

end EthLib.Serialization.Ssz
