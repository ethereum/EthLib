module

public import EthLib.Serialization.Ssz.Typed.Collections
public import EthLib.Serialization.Proofs.Ssz.Typed.Basic

/-!
# Proofs: typed SSZ collections are lawful

A collection converts each element on its own, so its laws follow from those of its elements.

A count that the type fixes or bounds is checked when the collection reads back.
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

/-- Every converted element fits the element type. -/
theorem forall_fits_map (items : List α) : ∀ value ∈ items.map toValue, Fits (desc α) value := by
  simpa using fun item _ => LawfulSszType.fits item

end SszType

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

instance : LawfulSszType ProgressiveBitlist where
  wellFormed := rfl
  fits b := .progressiveBitList rfl
  ofValue_toValue b := rfl
  toValue_of_ofValue {value b} made := by
    cases value <;> simp only [ofValue] at made <;> try cases made
    rfl

end EthLib.Serialization.Ssz
