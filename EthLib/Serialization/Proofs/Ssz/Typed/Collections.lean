module

public import EthLib.Serialization.Ssz.Typed.Collections
public import EthLib.Serialization.Proofs.Ssz.Typed.Basic

/-!
# Proofs: typed SSZ collections are lawful

A collection converts each element on its own, so its laws follow from those of its elements.

A count that the type fixes or bounds is checked when the collection reads back.

A byte list reads back from bytes exactly when they fit its limit and the offset width.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open SszType

namespace SszType

/-- Reading elements onto those read so far appends the elements that the list reads to. -/
theorem ofElementsOnto_eq {α : Type} [SszType α] :
    ∀ (elements : List Value) (read : Array α),
      ofElementsOnto elements read = (read ++ ·.toArray) <$> elements.mapM ofValue
  | [], read => by simp [ofElementsOnto, pure, Except.pure, Functor.map, Except.map]
  | element :: rest, read => by
    simp only [ofElementsOnto, List.mapM_cons]
    cases head : ofValue (α := α) element with
    | error fault => simp [bind, Except.bind, Functor.map, Except.map]
    | ok item =>
      simp only []
      rw [ofElementsOnto_eq rest (read.push item)]
      cases tail : rest.mapM (ofValue (α := α)) <;>
        simp [bind, Except.bind, Functor.map, Except.map, pure, Except.pure]

/-- Reading elements is reading the list in order, then making it an array. -/
theorem ofElements_eq {α : Type} [SszType α] (elements : List Value) :
    ofElements (α := α) elements = List.toArray <$> elements.mapM ofValue := by
  simp [ofElements, ofElementsOnto_eq]

variable {α : Type} [SszType α] [LawfulSszType α]

/-- Converted elements read back as the elements they came from. -/
theorem ofElements_map (items : List α) : ofElements (items.map toValue) = .ok items.toArray := by
  suffices read : (items.map toValue).mapM (ofValue (α := α)) = .ok items by
    simp [ofElements_eq, read, Functor.map, Except.map]
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp [List.mapM_cons, LawfulSszType.ofValue_toValue, ih, bind, Except.bind, pure, Except.pure]

/-- Elements that read back are the values that their typed elements stand for. -/
theorem map_toValue_of_ofElements {elements : List Value} {items : Array α}
    (read : ofElements elements = .ok items) : items.toList.map toValue = elements := by
  suffices back : ∀ {items : List α}, elements.mapM ofValue = .ok items →
      items.map toValue = elements by
    rw [ofElements_eq] at read
    cases mapped : elements.mapM (ofValue (α := α)) with
    | error fault => simp [mapped, Functor.map, Except.map] at read
    | ok list =>
      simp only [mapped, Functor.map, Except.map, Except.ok.injEq] at read
      subst read
      simpa using back mapped
  clear read
  induction elements with
  | nil => intro items read; cases read; rfl
  | cons element rest ih =>
    intro items read
    simp only [List.mapM_cons, bind, Except.bind] at read
    cases head : ofValue (α := α) element with
    | error fault => simp [head] at read
    | ok item =>
      cases tail : rest.mapM (ofValue (α := α)) with
      | error fault => simp [head, tail] at read
      | ok others =>
        simp only [head, tail, pure, Except.pure, Except.ok.injEq] at read
        subst read
        simp [LawfulSszType.toValue_of_ofValue head, ih tail]

/-- Elements that fit the element type all read, and the array has one item for each. -/
theorem ofElements_ok {elements : List Value} (each : ∀ value ∈ elements, Fits (desc α) value) :
    ∃ items : Array α, ofElements elements = .ok items ∧ items.size = elements.length := by
  suffices read : ∃ items : List α, elements.mapM (ofValue (α := α)) = .ok items ∧
      items.length = elements.length by
    obtain ⟨items, read, size⟩ := read
    exact ⟨items.toArray, by simp [ofElements_eq, read, Functor.map, Except.map], size⟩
  induction elements with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons element rest ih =>
    obtain ⟨others, tail, size⟩ := ih fun value mem => each value (List.mem_cons_of_mem _ mem)
    cases head : ofValue (α := α) element with
    | error fault => exact absurd head (LawfulSszType.ofValue_ne_error (each _ List.mem_cons_self))
    | ok item =>
      exact ⟨item :: others, by simp [List.mapM_cons, head, tail, bind, Except.bind, pure,
        Except.pure], by simp [size]⟩

/-- Every converted element fits the element type. -/
theorem forall_fits_map (items : List α) : ∀ value ∈ items.map toValue, Fits (desc α) value := by
  simpa using fun item _ => LawfulSszType.fits item

end SszType

/-- The bytes of elements written one after another are those of the untyped encoder. -/
theorem encodeElementsOnto_eq {α : Type} [SszType α] [LawfulSszType α] (items : Array α)
    (i : Nat) (out : ByteArray) :
    encodeElementsOnto items i out =
      (serializeEach (desc α) ((items.toList.drop i).map toValue)).map
        fun parts => out ++ ⟨concatParts parts⟩ := by
  rw [encodeElementsOnto]
  by_cases inside : i < items.size
  · rw [dite_eq_left inside,
      List.drop_eq_getElem_cons (by simpa using inside), List.map_cons, serializeEach_cons,
      LawfulSszType.encode_eq]
    simp only [Array.getElem_toList]
    cases serialize (desc α) (toValue items[i]) with
    | error fault => rfl
    | ok head =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [encodeElementsOnto_eq items (i + 1)]
      cases serializeEach (desc α) ((items.toList.drop (i + 1)).map toValue) with
      | error fault => rfl
      | ok parts =>
        simp only [Except.map, Except.ok.injEq]
        ext1
        simp [concatParts, Array.append_assoc]
  · rw [dite_eq_right inside,
      List.drop_eq_nil_of_le (by simp; omega)]
    simp only [List.map_nil, serializeEach_nil, Except.map]
    congr 1
    ext1
    simp [concatParts]
termination_by items.size - i

instance {α : Type} [SszType α] [LawfulSszType α] {length : Nat} [NeZero length] :
    LawfulSszType (Vector α length) where
  wellFormed := by
    simp [desc, Desc.wellFormed, NeZero.ne length, LawfulSszType.wellFormed (α := α)]
  fits v := .vector (by simp) (forall_fits_map v.toList)
  ofValue_toValue v := by
    simp [toValue, ofValue, ofElements_map, bind, Except.bind, pure, Except.pure,
      Vector.toArray_toList]
  toValue_of_ofValue {value v} made := by
    cases value <;> simp only [ofValue] at made <;> try cases made
    rename_i elements
    cases read : ofElements (α := α) elements with
    | error fault => simp [read, bind, Except.bind] at made
    | ok items =>
      by_cases exact : items.size = length
      · simp only [read, exact, bind, Except.bind, dite_true, pure, Except.pure,
          Except.ok.injEq] at made
        subst made
        simp [toValue, ← map_toValue_of_ofElements read]
      · simp [read, exact, bind, Except.bind] at made
  ofValue_ne_error {value fault} fits made := by
    cases fits with
    | vector count each =>
      obtain ⟨items, read, size⟩ := ofElements_ok each
      simp [ofValue, read, count, size, bind, Except.bind, pure, Except.pure] at made
  encode_eq v := by
    by_cases fixed : (desc α).isFixed
    · -- Fixed elements: their bytes one after another, as the untyped encoder lays them out.
      simp only [encode, fixed, ite_true, encodeFixedElements, desc, toValue, Ssz.serialize,
        List.length_map, Vector.length_toList, beq_self_eq_true, serializeSequence,
        assemble_inline_eq]
      rw [encodeElementsOnto_eq, List.drop_zero]
      rw [show v.toList = v.toArray.toList from rfl]
      cases serializeEach (desc α) (v.toArray.toList.map toValue) with
      | error fault => rfl
      | ok parts =>
        have empty : ∀ c, ByteArray.emptyWithCapacity c ++ ⟨concatParts parts⟩ =
            ⟨concatParts parts⟩ := fun c => by
          ext1
          simp [show (ByteArray.emptyWithCapacity c).data = #[] from rfl]
        have size : (⟨concatParts parts⟩ : ByteArray).size = (concatParts parts).size := rfl
        by_cases big : (concatParts parts).size ≥ 2 ^ (8 * bytesPerOffset)
        · simp [Except.map, empty, bind, Except.bind, size, big, throw, throwThe,
            MonadExceptOf.throw]
        · simp [Except.map, empty, bind, Except.bind, size, big, pure, Except.pure]
    · simp only [encode, fixed, Bool.false_eq_true, ite_false]
      rfl

instance {α : Type} [SszType α] [LawfulSszType α] {limit : Nat} :
    LawfulSszType (SszList α limit) where
  wellFormed := LawfulSszType.wellFormed (α := α)
  fits l := .list (by simpa using l.bound) (forall_fits_map l.data.toList)
  ofValue_toValue l := by
    simp [toValue, ofValue, ofElements_map, bind, Except.bind, l.bound, pure, Except.pure]
  toValue_of_ofValue {value l} made := by
    cases value <;> simp only [ofValue] at made <;> try cases made
    rename_i elements
    cases read : ofElements (α := α) elements with
    | error fault => simp [read, bind, Except.bind] at made
    | ok items =>
      by_cases within : items.size ≤ limit
      · simp only [read, within, bind, Except.bind, dite_true, pure, Except.pure,
          Except.ok.injEq] at made
        subst made
        simp [toValue, ← map_toValue_of_ofElements read]
      · simp [read, within, bind, Except.bind] at made
  ofValue_ne_error {value fault} fits made := by
    cases fits with
    | list within each =>
      obtain ⟨items, read, size⟩ := ofElements_ok each
      simp [ofValue, read, within, size, bind, Except.bind, pure, Except.pure] at made

instance {limit : Nat} : LawfulSszType (SszList UInt8 limit) where
  wellFormed := rfl
  fits l := .byteList l.bound
  ofValue_toValue l := by simp [toValue, ofValue, l.bound]
  toValue_of_ofValue {value l} made := by
    cases value <;> simp only [ofValue] at made <;> try cases made
    rename_i data
    by_cases within : data.size ≤ limit
    · simp only [within, dite_true, Except.ok.injEq] at made
      subst made
      rfl
    · simp [within] at made
  ofValue_ne_error {value fault} fits made := by
    cases fits with
    | byteList within => simp [ofValue, within] at made

/-- A byte list reads back from bytes exactly when they fit the offset width, as those same bytes.

The limit of the list is the bound that the read value carries. -/
theorem SszList.deserialize_uint8_eq_ok_iff {limit : Nat} {data : ByteArray}
    {l : SszList UInt8 limit} :
    SszType.deserialize (SszList UInt8 limit) data = .ok l ↔
      data.size < 2 ^ (8 * bytesPerOffset) ∧ l.data = data.data := by
  obtain ⟨items, bound⟩ := l
  have size : data.size = data.data.size := rfl
  simp only [SszType.deserialize, SszType.decode, Ssz.deserialize, bind, Except.bind, pure,
    Except.pure, throw, throwThe, MonadExceptOf.throw]
  by_cases wide : 2 ^ (8 * bytesPerOffset) ≤ data.size
  · simp [wide, Nat.not_lt.mpr wide]
  · by_cases over : limit < data.size
    · have : items ≠ data.data := fun same => by subst same; omega
      simp [wide, over, Nat.lt_of_not_le wide, this]
    · simp [wide, over, Nat.lt_of_not_le wide, Nat.le_of_not_lt over, eq_comm]

instance {length : Nat} [NeZero length] : LawfulSszType (Bitvector length) where
  wellFormed := by simp [desc, Desc.wellFormed, NeZero.ne length]
  fits b := .bitVector b.bits.size_toArray
  ofValue_toValue b := by simp [toValue, ofValue, b.bits.size_toArray]
  toValue_of_ofValue {value b} made := by
    cases value <;> simp only [ofValue] at made <;> try cases made
    rename_i data
    by_cases exact : data.size = length
    · simp only [exact, dite_true, Except.ok.injEq] at made
      subst made
      rfl
    · simp [exact] at made
  ofValue_ne_error {value fault} fits made := by
    cases fits with
    | bitVector exact => simp [ofValue, exact] at made

instance {limit : Nat} : LawfulSszType (Bitlist limit) where
  wellFormed := rfl
  fits b := .bitList b.bound
  ofValue_toValue b := by simp [toValue, ofValue, b.bound]
  toValue_of_ofValue {value b} made := by
    cases value <;> simp only [ofValue] at made <;> try cases made
    rename_i data
    by_cases within : data.size ≤ limit
    · simp only [within, dite_true, Except.ok.injEq] at made
      subst made
      rfl
    · simp [within] at made
  ofValue_ne_error {value fault} fits made := by
    cases fits with
    | bitList within => simp [ofValue, within] at made

instance {α : Type} [SszType α] [LawfulSszType α] : LawfulSszType (ProgressiveList α) where
  wellFormed := LawfulSszType.wellFormed (α := α)
  fits l := .progressiveList rfl (forall_fits_map l.data.toList)
  ofValue_toValue l := by simp [toValue, ofValue, ofElements_map, Functor.map, Except.map]
  toValue_of_ofValue {value l} made := by
    cases value <;> simp only [ofValue] at made <;> try cases made
    rename_i elements
    cases read : ofElements (α := α) elements with
    | error fault => simp [read, Functor.map, Except.map] at made
    | ok items =>
      simp only [read, Functor.map, Except.map, Except.ok.injEq] at made
      subst made
      simp [toValue, ← map_toValue_of_ofElements read]
  ofValue_ne_error {value fault} fits made := by
    cases fits with
    | progressiveList within each =>
      obtain ⟨items, read, size⟩ := ofElements_ok each
      simp [ofValue, read, Functor.map, Except.map] at made

instance : LawfulSszType ProgressiveBitlist where
  wellFormed := rfl
  fits b := .progressiveBitList rfl
  ofValue_toValue b := rfl
  toValue_of_ofValue {value b} made := by
    cases value <;> simp only [ofValue] at made <;> try cases made
    rfl
  ofValue_ne_error {value fault} fits made := by
    cases fits
    simp [ofValue] at made

/-- An empty encoding has no slices. -/
theorem listSlices_empty (element : Desc) (limit : Option Nat) :
    listSlices element limit #[] = .ok [] := by
  simp [listSlices, bytesPerOffset, pure, Except.pure]

/-- The empty bytes decode to the empty progressive list. -/
theorem deserialize_progressiveList_empty {α : Type} [SszType α] :
    SszType.deserialize (ProgressiveList α) ByteArray.empty = .ok ⟨#[]⟩ := by
  unfold SszType.deserialize SszType.decode
  show (do SszType.ofValue (← Ssz.deserialize _ #[])) = _
  rw [Ssz.deserialize]
  simp [listSlices_empty, deserializeEach_nil, bind, Except.bind, pure, Except.pure,
      SszType.ofValue, SszType.ofElements, SszType.ofElementsOnto, Functor.map, Except.map]

/-- The empty progressive list has empty SSZ bytes. -/
theorem serialize_progressiveList_empty {α : Type} [SszType α] [LawfulSszType α] :
    SszType.serialize (⟨#[]⟩ : ProgressiveList α) = .ok .empty :=
  SszType.serialize_deserialize deserialize_progressiveList_empty

/-- A progressive list with SSZ bytes is empty exactly when its bytes are. -/
theorem progressiveList_size_eq_zero_iff {α : Type} [SszType α] [LawfulSszType α]
    {list : ProgressiveList α} {data : ByteArray} (wrote : SszType.serialize list = .ok data) :
    list.data.size = 0 ↔ data.size = 0 := by
  rw [SszType.size_eq_zero_iff_of_deserialize_empty deserialize_progressiveList_empty wrote]
  cases list
  simp [Array.size_eq_zero_iff]

end EthLib.Serialization.Ssz
