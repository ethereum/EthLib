module

public import EthLib.Serialization.Ssz.Codec.Json

/-!
# Proofs: hex reads the same in either case

A hex digit reads the same in uppercase, so a hex string does too.

A document reads the same with any hex digits of its strings in uppercase, at every shape.

A spelling that carries the text mark is left out, since the case of a text is part of it.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- A lowercase letter is 32 below the code of its uppercase letter. -/
private theorem toUpper_val_of_lower {c : Char} (low : 'a'.val.toNat ≤ c.val.toNat)
    (high : c.val.toNat ≤ 'z'.val.toNat) : c.toUpper.val.toNat + 32 = c.val.toNat := by
  have h : 'a'.val ≤ c.val ∧ c.val ≤ 'z'.val := by
    simp only [UInt32.le_iff_toNat_le]
    exact ⟨low, high⟩
  simp only [Char.toUpper, h, and_self, ↓reduceDIte, UInt32.toNat_add, UInt32.toNat_sub]
  have ea : 'a'.val.toNat = 97 := rfl
  have eA : 'A'.val.toNat = 65 := rfl
  have ez : 'z'.val.toNat = 122 := rfl
  omega

/-- The code of any other character is kept in uppercase. -/
private theorem toUpper_of_not_lower {c : Char} (h : ¬ ('a'.val.toNat ≤ c.val.toNat ∧
    c.val.toNat ≤ 'z'.val.toNat)) : c.toUpper = c := by
  have h' : ¬ ('a'.val ≤ c.val ∧ c.val ≤ 'z'.val) := by
    simpa only [UInt32.le_iff_toNat_le] using h
  unfold Char.toUpper
  simp only [h', ↓reduceDIte]

/-- A hex digit reads the same in uppercase. -/
theorem hexDigit_toUpper (c : Char) : hexDigit c.toUpper = hexDigit c := by
  by_cases h : 'a'.val.toNat ≤ c.val.toNat ∧ c.val.toNat ≤ 'z'.val.toNat
  · have key := toUpper_val_of_lower h.1 h.2
    unfold hexDigit
    simp only [Char.le_def, Char.toNat, UInt32.le_iff_toNat_le]
    generalize c.toUpper = d at *
    have e0 : '0'.val.toNat = 48 := rfl
    have e9 : '9'.val.toNat = 57 := rfl
    have ea : 'a'.val.toNat = 97 := rfl
    have ef : 'f'.val.toNat = 102 := rfl
    have ez : 'z'.val.toNat = 122 := rfl
    have eA : 'A'.val.toNat = 65 := rfl
    have eF : 'F'.val.toNat = 70 := rfl
    simp only [e0, e9, ea, ef, ez, eA, eF, Bool.and_eq_true, decide_eq_true_eq] at *
    repeat' split
    all_goals first | rfl | (exfalso; omega) | (congr 1; omega)
  · rw [toUpper_of_not_lower h]

/-- Pairs of digits read the same in uppercase. -/
theorem hexBytesFrom_map_toUpper :
    ∀ (digits : List Char) (out : Bytes),
      hexBytesFrom (digits.map Char.toUpper) out = hexBytesFrom digits out
  | [], _ => rfl
  | [_], _ => rfl
  | high :: low :: rest, out => by
    simp only [List.map_cons, hexBytesFrom, hexDigit_toUpper, hexBytesFrom_map_toUpper rest]

/-- Hex reads the same with its digits in uppercase. -/
theorem ofHex_uppercase (digits : String) :
    ofHex ("0x" ++ digits.map Char.toUpper) = ofHex ("0x" ++ digits) := by
  simp only [ofHex, String.toList_append, String.toList_map]
  have marker : "0x".toList = ['0', 'x'] := by decide
  simp only [marker, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
    List.drop_succ_cons, List.drop_zero, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  exact hexBytesFrom_map_toUpper digits.toList #[]

open Lean

/-- Whether two lists of characters have the same length and match place by place.

At each place, the second character is the first one or its uppercase form. -/
def KeptOrUpper : List Char → List Char → Prop
  | [], [] => True
  | digit :: digits, kept :: rest => (kept = digit ∨ kept = digit.toUpper) ∧ KeptOrUpper digits rest
  | _, _ => False

/-- Whether the second text is the first, or the first with some characters after `0x` in uppercase.

Each character is kept, or replaced by its uppercase form, so any mix of cases is covered. -/
def HexCase (text other : String) : Prop :=
  text = other ∨ ∃ digits upper : List Char,
    text.toList = '0' :: 'x' :: digits ∧ other.toList = '0' :: 'x' :: upper ∧
      KeptOrUpper digits upper

/-- Whether the second document is the first with some characters after `0x` in uppercase.

Both have the same form, the same keys and the same other leaves. -/
inductive SameUpToCase : Json → Json → Prop
  /-- Null matches null. -/
  | null : SameUpToCase .null .null
  /-- A boolean matches itself. -/
  | bool (b : Bool) : SameUpToCase (.bool b) (.bool b)
  /-- A number matches itself. -/
  | num (n : JsonNumber) : SameUpToCase (.num n) (.num n)
  /-- A string matches itself, or itself with some characters after `0x` in uppercase. -/
  | str {text other : String} (cased : HexCase text other) :
      SameUpToCase (.str text) (.str other)
  /-- An array matches one of the same size whose entries match, entry by entry. -/
  | arr {left right : Array Json} (size : left.size = right.size)
      (each : ∀ (i : Nat) (inLeft : i < left.size) (inRight : i < right.size),
        SameUpToCase left[i] right[i]) :
      SameUpToCase (.arr left) (.arr right)
  /-- An object matches one with the same names whose values match, name by name. -/
  | obj {left right : Std.TreeMap.Raw String Json}
      (names : objectNames (.obj left) = objectNames (.obj right))
      (present : ∀ name, ((Json.obj left).getObjVal? name).toOption.isSome =
        ((Json.obj right).getObjVal? name).toOption.isSome)
      (each : ∀ name value other, (Json.obj left).getObjVal? name = .ok value →
        (Json.obj right).getObjVal? name = .ok other → SameUpToCase value other) :
      SameUpToCase (.obj left) (.obj right)

/-- A digit and its uppercase form, or a digit kept, read the same. -/
private theorem hexDigit_keptOrUpper {digit kept : Char}
    (h : kept = digit ∨ kept = digit.toUpper) : hexDigit kept = hexDigit digit := by
  rcases h with rfl | rfl
  · rfl
  · exact hexDigit_toUpper digit

/-- Pairs of digits read the same with some of them in uppercase. -/
private theorem hexBytesFrom_keptOrUpper :
    ∀ (digits upper : List Char) (out : Bytes), KeptOrUpper digits upper →
      hexBytesFrom upper out = hexBytesFrom digits out
  | [], [], _, _ => rfl
  | [_], [_], _, _ => rfl
  | high :: low :: rest, kHigh :: kLow :: kRest, out, h => by
    obtain ⟨hHigh, hLow, hRest⟩ : _ ∧ _ ∧ KeptOrUpper rest kRest := ⟨h.1, h.2.1, h.2.2⟩
    simp only [hexBytesFrom, hexDigit_keptOrUpper hHigh, hexDigit_keptOrUpper hLow,
      hexBytesFrom_keptOrUpper rest kRest _ hRest]
  | [], _ :: _, _, h | _ :: _, [], _, h => h.elim
  | [_], _ :: _ :: _, _, h => h.2.elim
  | _ :: _ :: _, [_], _, h => h.2.elim

/-- A list of characters matches its own uppercase form, place by place. -/
private theorem keptOrUpper_map_toUpper :
    ∀ digits : List Char, KeptOrUpper digits (digits.map Char.toUpper)
  | [] => trivial
  | _ :: rest => ⟨.inr rfl, keptOrUpper_map_toUpper rest⟩

/-- A string matches the same string with all the digits after its marker in uppercase. -/
theorem sameUpToCase_uppercase (digits : String) :
    SameUpToCase (.str ("0x" ++ digits)) (.str ("0x" ++ digits.map Char.toUpper)) := by
  have marker : "0x".toList = ['0', 'x'] := by decide
  refine .str (.inr ⟨digits.toList, digits.toList.map Char.toUpper, ?_, ?_,
    keptOrUpper_map_toUpper _⟩) <;>
    simp [String.toList_append, String.toList_map, marker]

/-- Hex behind the marker is read from the digits after it. -/
private theorem ofHex_marked {text : String} {digits : List Char}
    (marked : text.toList = '0' :: 'x' :: digits) : ofHex text = hexBytes digits := by
  simp only [ofHex, marked, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
    List.drop_zero, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]

/-- Hex reads the same with some of its digits in uppercase. -/
theorem ofHex_hexCase {text other : String} (cased : HexCase text other) :
    ofHex text = ofHex other := by
  rcases cased with rfl | ⟨digits, upper, marked, markedOther, kept⟩
  · rfl
  · rw [ofHex_marked marked, ofHex_marked markedOther, hexBytes, hexBytes,
      hexBytesFrom_keptOrUpper digits upper _ kept]

/-- No decimal string has an `x` as its second character. -/
private theorem toString_toList_ne_marked (n : Nat) (rest : List Char) :
    (toString n).toList ≠ '0' :: 'x' :: rest := by
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
  intro h
  have member : 'x' ∈ Nat.toDigits 10 n := by simp [h]
  exact absurd (Nat.isDigit_of_mem_toDigits (by decide) (by decide) member) (by decide)

/-- A string behind the hex marker holds no number. -/
private theorem readNat_marked {text : String} {rest : List Char}
    (marked : text.toList = '0' :: 'x' :: rest) : readNat (.str text) = .error .typeMismatch := by
  simp only [readNat, ite_eq_right_iff]
  intro h
  exact absurd (by rw [beq_iff_eq.mp h, marked]) (toString_toList_ne_marked _ rest)

/-- Matching documents hold the same number. -/
private theorem readNat_same {left right : Json} (same : SameUpToCase left right) :
    readNat left = readNat right := by
  cases same with
  | str cased =>
    rcases cased with rfl | ⟨_, _, marked, markedOther, _⟩
    · rfl
    · rw [readNat_marked marked, readNat_marked markedOther]
  | _ => rfl

/-- Matching documents hold the same hex collection, whatever is done with its bytes. -/
private theorem collectionHex_same {α : Type} {left right : Json} (same : SameUpToCase left right)
    (next : Bytes → Except Err α) :
    (do let data ← ofHex (← collectionHex left); next data) =
      (do let data ← ofHex (← collectionHex right); next data) := by
  cases same with
  | str cased => simp only [collectionHex, Bind.bind, Except.bind, ofHex_hexCase cased]
  | _ => rfl

/-- Whether two lists of documents match entry by entry. -/
private inductive EachSame : List Json → List Json → Prop
  /-- Two empty lists match. -/
  | nil : EachSame [] []
  /-- Lists match when their first entries match and the rest match. -/
  | cons {head other : Json} {rest others : List Json} (first : SameUpToCase head other)
      (tail : EachSame rest others) : EachSame (head :: rest) (other :: others)

/-- Lists of the same length whose entries match at each place match entry by entry. -/
private theorem eachSame_of_getElem :
    ∀ (left right : List Json), left.length = right.length →
      (∀ (i : Nat) (inLeft : i < left.length) (inRight : i < right.length),
        SameUpToCase left[i] right[i]) → EachSame left right
  | [], [], _, _ => .nil
  | head :: rest, other :: others, size, each =>
    .cons (each 0 (by simp) (by simp))
      (eachSame_of_getElem rest others (by simpa using size)
        fun i inLeft inRight => each (i + 1) (by simpa using inLeft) (by simpa using inRight))
  | [], _ :: _, size, _ | _ :: _, [], size, _ => by simp at size

/-- Matching arrays match entry by entry. -/
private theorem eachSame_of_arr {left right : Array Json} (size : left.size = right.size)
    (each : ∀ (i : Nat) (inLeft : i < left.size) (inRight : i < right.size),
      SameUpToCase left[i] right[i]) : EachSame left.toList right.toList :=
  eachSame_of_getElem _ _ (by simp [size]) fun i inLeft inRight => by
    simpa using each i (by simpa using inLeft) (by simpa using inRight)

/-- Decimal strings that match entry by entry hold the same bytes. -/
private theorem byteDigitsFrom_same {left right : List Json}
    (same : EachSame left right) (out : Bytes) :
    byteDigitsFrom left out = byteDigitsFrom right out := by
  induction same generalizing out with
  | nil => rfl
  | cons head _ ih => simp only [byteDigitsFrom, readNat_same head, ih]

/-- Matching objects hold, at each name, nothing in both or matching values. -/
private theorem lookup_same {left right : Std.TreeMap.Raw String Json}
    (present : ∀ name, ((Json.obj left).getObjVal? name).toOption.isSome =
      ((Json.obj right).getObjVal? name).toOption.isSome)
    (each : ∀ name value other, (Json.obj left).getObjVal? name = .ok value →
      (Json.obj right).getObjVal? name = .ok other → SameUpToCase value other)
    (name : String) :
    Option.Rel SameUpToCase ((Json.obj left).getObjVal? name).toOption
      ((Json.obj right).getObjVal? name).toOption := by
  have known := present name
  cases inLeft : (Json.obj left).getObjVal? name <;>
    cases inRight : (Json.obj right).getObjVal? name <;>
    simp only [inLeft, inRight, Except.toOption, Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, Bool.true_eq_false] at known ⊢
  · exact .none
  · exact .some (each name _ _ inLeft inRight)

/-- A list of spellings carries no text mark when none of its members does. -/
theorem Spelling.anyText_eq_false {parts : List Spelling} :
    Spelling.anyText parts = false ↔ ∀ part ∈ parts, part.hasText = false := by
  induction parts with
  | nil => simp [Spelling.anyText]
  | cons part rest ih => simp [Spelling.anyText, ih]

/-- A spelling with no text holds none in the declarations it holds. -/
theorem Spelling.hasText_part {spelling : Spelling} (plain : spelling.hasText = false)
    (position : Nat) : (spelling.part position).hasText = false := by
  cases spelling with
  | byte | digits => simp [Spelling.part, Spelling.opaque, Spelling.hasText, Spelling.anyText]
  | text => simp [Spelling.hasText] at plain
  | plain parts =>
    simp only [Spelling.part]
    by_cases inside : position < parts.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside, Option.getD_some]
      simp only [Spelling.hasText, Spelling.anyText_eq_false] at plain
      exact plain _ (List.getElem_mem inside)
    · have none : parts[position]? = none := List.getElem?_eq_none (by omega)
      simp [List.getD_eq_getElem?_getD, none, Spelling.opaque, Spelling.hasText,
        Spelling.anyText]

/-- Whether matching documents read the same under a declaration, at every spelling with no text. -/
private def ReadsSame (shape : Desc) : Prop :=
  ∀ (spelling : Spelling), spelling.hasText = false → ∀ {left right : Json},
    SameUpToCase left right →
    valueOf shape spelling left = valueOf shape spelling right

/-- Entries that match one by one read the same, entry by entry. -/
private theorem valueOfEntries_same {element : Desc} (reads : ReadsSame element)
    (spelling : Spelling) (plain : spelling.hasText = false) {left right : List Json}
    (same : EachSame left right) :
    valueOfEntries element spelling left = valueOfEntries element spelling right := by
  induction same with
  | nil => rfl
  | cons first _ ih => simp only [valueOfEntries, reads spelling plain first, ih]

/-- Matching sequence documents hold the same elements. -/
private theorem valueOfSequence_same {element : Desc} (reads : ReadsSame element)
    (spelling : Spelling) (plain : spelling.hasText = false) {left right : Json}
    (same : SameUpToCase left right) :
    valueOfSequence element spelling left = valueOfSequence element spelling right := by
  unfold valueOfSequence
  by_cases byte : (spelling.isByte && element.isOneByte) = true
  · simp only [byte, ↓reduceIte]
    exact collectionHex_same same _
  · simp only [byte, Bool.false_eq_true, ↓reduceIte]
    cases same with
    | arr size each => exact valueOfEntries_same reads spelling plain (eachSame_of_arr size each)
    | _ => rfl

/-- Fields read the same out of documents that hold matching values at each name. -/
private theorem valueOfFields_same {left right : Json}
    (lookup : ∀ name, Option.Rel SameUpToCase (left.getObjVal? name).toOption
      (right.getObjVal? name).toOption) (names : List String) (spelling : Spelling)
    (plain : spelling.hasText = false) :
    ∀ (fields : List Desc), (∀ field ∈ fields, ReadsSame field) → ∀ position,
      valueOfFields fields names spelling position left =
        valueOfFields fields names spelling position right
  | [], _, _ => by simp only [valueOfFields]
  | field :: fields, reads, position => by
    simp only [valueOfFields]
    have found := lookup (names.getD position "")
    revert found
    generalize (left.getObjVal? (names.getD position "")).toOption = part
    generalize (right.getObjVal? (names.getD position "")).toOption = other
    intro found
    cases found with
    | none => rfl
    | some first =>
      simp only [reads field (by simp) _ (Spelling.hasText_part plain position) first,
        valueOfFields_same lookup names spelling plain fields (fun f m => reads f (by simp [m]))]

/-- The option a selector names reads the same out of matching payloads. -/
private theorem valueOfOption_same (spelling : Spelling) (plain : spelling.hasText = false)
    {payload other : Json}
    (same : SameUpToCase payload other) :
    ∀ (selectors : List Nat) (options : List Desc), (∀ option ∈ options, ReadsSame option) →
      ∀ position selector, valueOfOption selectors options spelling position selector payload =
        valueOfOption selectors options spelling position selector other
  | [], [], _, _, _ => by simp only [valueOfOption]
  | chosen :: selectors, option :: options, reads, position, selector => by
    simp only [valueOfOption,
      reads option (by simp) _ (Spelling.hasText_part plain position) same,
      valueOfOption_same spelling plain same selectors options (fun o m => reads o (by simp [m]))]
  | [], _ :: _, _, _, _ | _ :: _, [], _, _, _ => by simp only [valueOfOption]

/-- Matching documents read the same under every declaration. -/
private theorem readsSame (shape : Desc) : ReadsSame shape := by
  induction shape using Desc.rec
    (motive_2 := fun fields => ∀ field ∈ fields, ReadsSame field) with
  | bool =>
    intro spelling plain left right same
    cases same <;> simp only [valueOf]
  | uint width =>
    intro spelling plain left right same
    unfold valueOf
    by_cases byte : (spelling.isByte && width == 1) = true
    · simp only [byte, ↓reduceIte]
      cases same with
      | str cased => simp only [ofHex_hexCase cased]
      | _ => rfl
    · simp only [byte, Bool.false_eq_true, ↓reduceIte, readNat_same same]
  | byteVector length =>
    intro spelling plain left right same
    rw [valueOf, valueOf]
    exact collectionHex_same same _
  | byteList limit =>
    intro spelling plain left right same
    unfold valueOf
    have notText : spelling.isText = false := by
      cases spelling <;> simp_all [Spelling.hasText, Spelling.isText]
    by_cases digits : spelling.isDigits = true
    · simp only [digits, ↓reduceIte]
      cases same with
      | arr size each => simp only [byteDigitsFrom_same (eachSame_of_arr size each)]
      | _ => rfl
    · simp only [digits, notText, Bool.false_eq_true, ↓reduceIte]
      exact collectionHex_same same _
  | bitVector length =>
    intro spelling plain left right same
    rw [valueOf, valueOf, readBitfield, readBitfield]
    exact collectionHex_same same _
  | bitList limit =>
    intro spelling plain left right same
    rw [valueOf, valueOf, readBitfield, readBitfield]
    exact collectionHex_same same _
  | progressiveBitList limit =>
    intro spelling plain left right same
    rw [valueOf, valueOf, readBitfield, readBitfield]
    exact collectionHex_same same _
  | vector element length ih =>
    intro spelling plain left right same
    rw [valueOf, valueOf, valueOfSequence_same ih _ (Spelling.hasText_part plain 0) same]
  | list element limit ih =>
    intro spelling plain left right same
    rw [valueOf, valueOf, valueOfSequence_same ih _ (Spelling.hasText_part plain 0) same]
  | progressiveList element limit ih =>
    intro spelling plain left right same
    rw [valueOf, valueOf, valueOfSequence_same ih _ (Spelling.hasText_part plain 0) same]
  | container names fields ih =>
    intro spelling plain left right same
    cases same with
    | obj names present each =>
      simp only [valueOf, names,
        valueOfFields_same (lookup_same present each) _ spelling plain fields ih]
    | _ => simp only [valueOf]
  | progressiveContainer active names fields ih =>
    intro spelling plain left right same
    cases same with
    | obj names present each =>
      simp only [valueOf, names,
        valueOfFields_same (lookup_same present each) _ spelling plain fields ih]
    | _ => simp only [valueOf]
  | compatibleUnion selectors options ih =>
    intro spelling plain left right same
    cases same with
    | obj names present each =>
      simp only [valueOf, names]
      have selector := lookup_same present each "selector"
      have data := lookup_same present each "data"
      revert selector data
      generalize ((Json.obj _).getObjVal? "selector").toOption = selector
      generalize ((Json.obj _).getObjVal? "selector").toOption = selectorOther
      generalize ((Json.obj _).getObjVal? "data").toOption = data
      generalize ((Json.obj _).getObjVal? "data").toOption = dataOther
      intro selectorSame dataSame
      cases selectorSame with
      | none => rfl
      | some selectorFirst =>
        cases dataSame with
        | none => rfl
        | some dataFirst =>
          simp only [readNat_same selectorFirst,
            valueOfOption_same spelling plain dataFirst selectors options ih]
    | _ => simp only [valueOf]
  | nil =>
    rename_i field member
    simp at member
  | cons head rest ihHead ihRest =>
    rename_i field member
    rcases List.mem_cons.mp member with rfl | inRest
    · exact ihHead
    · exact ihRest field inRest

/-- A document reads the same with some characters after `0x` of its strings in uppercase.

Two documents that differ only in that case both read as their lowercase form, so they read alike.

It holds at every shape, and at every spelling with no text, for a refusal as well as a value. -/
theorem valueOf_sameUpToCase (shape : Desc) {spelling : Spelling}
    (plain : spelling.hasText = false) {left right : Json} (same : SameUpToCase left right) :
    valueOf shape spelling left = valueOf shape spelling right := by
  exact readsSame shape spelling plain same

end EthLib.Serialization.Ssz
