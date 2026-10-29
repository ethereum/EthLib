import EthLib.Consensus.Proofs.Ssz.Codec.JsonHex
import EthLib.Consensus.Proofs.Ssz.Codec.RoundTrip
import Std.Data.TreeMap.Raw.WF
import Std.Data.TreeMap.Raw.Lemmas
import Std.Data.String.ToNat

/-! Reading back what the JSON mapping writes, and what the mapping does not pin down. -/

namespace EthLib.Consensus.Ssz

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

The alias marks a one-byte integer, so the one byte its hex names is the whole value, and
every other spelling writes the digits, which read back at any width.
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

/-- A byte list document reads back as the bytes it was written from. -/
theorem valueOf_jsonOf_byteList {spelling : Spelling} {limit : Nat} {data : Bytes}
    {document : Json} (fitted : data.size ≤ limit)
    (written : jsonOf (.byteList limit) spelling (.bytes data) = .ok document) :
    valueOf (.byteList limit) spelling document = .ok (.bytes data) := by
  simp only [jsonOf, fitted, ↓reduceIte, Except.ok.injEq] at written
  subst written
  rw [valueOf]
  simp [collectionHex, ofHex_toHex, Nat.not_lt.mpr fitted, Bind.bind, Except.bind,
    pure, Except.pure]

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

A hex digit is read in either letter case, so a byte array has as many documents as its
bytes have spellings.

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

end EthLib.Consensus.Ssz
