module

public import EthLib.Serialization.Ssz.Typed.ForkKind
public import EthLib.Serialization.Proofs.Ssz.Typed.Collections
public import EthLib.Serialization.Proofs.Ssz.Typed.Container

/-!
# Proofs: kinds that a fork chooses are lawful

At every fork, a fork-chosen list, bitlist or container reads back the value it came from.

Before the switch, each one has the SSZ type and the values of the kind it replaces.

So a fork that the switch does not reach encodes and roots exactly as before.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open Base SszType

variable {switch fork : Fork}

/-- Before the switch, the fork is below it. -/
theorem lt_of_not_switch (before : ¬switch ≤ fork) : fork < switch := Nat.lt_of_not_le before

/-- From the switch on, the fork is not below it. -/
theorem not_lt_of_switch (from_ : switch ≤ fork) : ¬fork < switch := Nat.not_lt.mpr from_

/-- Below the switch, the fork has not reached it. -/
theorem not_switch_of_lt (before : fork < switch) : ¬switch ≤ fork := Nat.not_le.mpr before

section List

variable {α : Type} [SszType α] {limit : Nat}

/-- Before the switch, a fork-chosen list has the SSZ type of a list with the limit. -/
theorem desc_forkList (before : fork < switch) :
    desc (ForkList switch fork α limit) = desc (SszList α limit) := by
  simp [desc, not_switch_of_lt before]

/-- Before the switch, a fork-chosen list has the value of the list with its elements. -/
theorem toValue_forkList_ofSszList (l : SszList α limit) :
    toValue (ForkList.ofSszList (switch := switch) (fork := fork) l) = toValue l := rfl

/-- Before the switch, a fork-chosen list has the bytes and the root of the same list. -/
theorem serialize_forkList_ofSszList (before : fork < switch) (l : SszList α limit) :
    SszType.serialize (ForkList.ofSszList (switch := switch) (fork := fork) l) =
        SszType.serialize l ∧
      SszType.hashTreeRoot (ForkList.ofSszList (switch := switch) (fork := fork) l) =
        SszType.hashTreeRoot l := by
  constructor <;>
    simp only [SszType.serialize, SszType.hashTreeRoot, desc_forkList before,
      toValue_forkList_ofSszList]

variable [LawfulSszType α]

instance : LawfulSszType (ForkList switch fork α limit) where
  wellFormed := by
    simp only [desc]
    split <;> exact LawfulSszType.wellFormed (α := α)
  fits l := by
    simp only [desc, toValue]
    split
    · exact .progressiveList rfl (forall_fits_map l.data.toList)
    · rename_i before
      exact .list (by simpa using l.bound (lt_of_not_switch before))
        (forall_fits_map l.data.toList)
  ofValue_toValue l := by
    simp only [toValue, ofValue, ofElements_map, bind, Except.bind, Array.toArray_toList]
    rw [dite_eq_left_of_eq_true (eq_true l.bound)]
    rfl
  toValue_of_ofValue {value l} made := by
    cases value <;> simp only [ofValue] at made <;> try cases made
    rename_i elements
    cases read : ofElements (α := α) elements with
    | error fault => simp [read, bind, Except.bind] at made
    | ok items =>
      simp only [read, bind, Except.bind] at made
      split at made
      · simp only [pure, Except.pure, Except.ok.injEq] at made
        subst made
        simp [toValue, ← map_toValue_of_ofElements read]
      · cases made

end List

section Bytes

variable {limit : Nat}

/-- Before the switch, fork-chosen bytes have the SSZ type of a byte list with the limit. -/
theorem desc_forkList_uint8 (before : fork < switch) :
    desc (ForkList switch fork UInt8 limit) = desc (SszList UInt8 limit) := by
  simp [desc, not_switch_of_lt before]

/-- Before the switch, fork-chosen bytes have the value of the byte list with those bytes. -/
theorem toValue_forkList_uint8 (before : fork < switch) (l : SszList UInt8 limit) :
    toValue (ForkList.ofSszList (switch := switch) (fork := fork) l) = toValue l := by
  simp [toValue, ForkList.ofSszList, not_switch_of_lt before]

/-- Before the switch, fork-chosen bytes have the bytes and the root of the same byte list. -/
theorem serialize_forkList_uint8 (before : fork < switch) (l : SszList UInt8 limit) :
    SszType.serialize (ForkList.ofSszList (switch := switch) (fork := fork) l) =
        SszType.serialize l ∧
      SszType.hashTreeRoot (ForkList.ofSszList (switch := switch) (fork := fork) l) =
        SszType.hashTreeRoot l := by
  constructor <;>
    simp only [SszType.serialize, SszType.hashTreeRoot, desc_forkList_uint8 before,
      toValue_forkList_uint8 before]

instance : LawfulSszType (ForkList switch fork UInt8 limit) where
  wellFormed := by
    simp only [desc]
    split
    · exact LawfulSszType.wellFormed (α := UInt8)
    · rfl
  fits l := by
    simp only [desc, toValue]
    split
    · exact .progressiveList rfl (forall_fits_map l.data.toList)
    · rename_i before
      exact .byteList (l.bound (lt_of_not_switch before))
  ofValue_toValue l := by
    by_cases from_ : switch ≤ fork
    · have read := ofElements_map (α := UInt8) l.data.toList
      simp only [toValue] at read
      simp only [toValue, ofValue, from_, ↓reduceIte, read, bind, Except.bind,
        Array.toArray_toList]
      rw [dite_eq_left_of_eq_true (eq_true l.bound)]
      rfl
    · simp only [toValue, ofValue, from_, ↓reduceIte]
      rw [dite_eq_left_of_eq_true (eq_true l.bound)]
  toValue_of_ofValue {value l} made := by
    by_cases from_ : switch ≤ fork
    · simp only [ofValue, from_, ↓reduceIte] at made
      cases value <;> simp only at made <;> try cases made
      rename_i elements
      cases read : ofElements (α := UInt8) elements with
      | error fault => simp [read, bind, Except.bind] at made
      | ok items =>
        simp only [read, bind, Except.bind] at made
        split at made
        · simp only [pure, Except.pure, Except.ok.injEq] at made
          subst made
          simp [toValue, from_, ← map_toValue_of_ofElements read]
        · cases made
    · simp only [ofValue, from_, ↓reduceIte] at made
      cases value <;> simp only at made <;> try cases made
      rename_i data
      split at made
      · simp only [Except.ok.injEq] at made
        subst made
        simp [toValue, from_]
      · cases made

end Bytes

section Bitlist

variable {limit : Nat}

/-- Before the switch, a fork-chosen bitlist has the SSZ type of a bitlist with the limit. -/
theorem desc_forkBitlist (before : fork < switch) :
    desc (ForkBitlist switch fork limit) = desc (Bitlist limit) := by
  simp [desc, not_switch_of_lt before]

/-- A fork-chosen bitlist has the value of the bitlist with its bits. -/
theorem toValue_forkBitlist_ofBitlist (b : Bitlist limit) :
    toValue (ForkBitlist.ofBitlist (switch := switch) (fork := fork) b) = toValue b := rfl

/-- Before the switch, a fork-chosen bitlist has the bytes and the root of the same bitlist. -/
theorem serialize_forkBitlist_ofBitlist (before : fork < switch) (b : Bitlist limit) :
    SszType.serialize (ForkBitlist.ofBitlist (switch := switch) (fork := fork) b) =
        SszType.serialize b ∧
      SszType.hashTreeRoot (ForkBitlist.ofBitlist (switch := switch) (fork := fork) b) =
        SszType.hashTreeRoot b := by
  constructor <;>
    simp only [SszType.serialize, SszType.hashTreeRoot, desc_forkBitlist before,
      toValue_forkBitlist_ofBitlist]

instance : LawfulSszType (ForkBitlist switch fork limit) where
  wellFormed := by
    simp only [desc]
    split <;> rfl
  fits b := by
    simp only [desc, toValue]
    split
    · exact .progressiveBitList rfl
    · rename_i before
      exact .bitList (b.bound (lt_of_not_switch before))
  ofValue_toValue b := by
    simp only [toValue, ofValue]
    rw [dite_eq_left_of_eq_true (eq_true b.bound)]
  toValue_of_ofValue {value b} made := by
    cases value <;> simp only [ofValue] at made <;> try cases made
    split at made
    · simp only [Except.ok.injEq] at made
      subst made
      rfl
    · cases made

end Bitlist

/-- A fork-chosen container is lawful when its kind at the fork is.

The layout matters only from the switch on. -/
theorem LawfulSszType.forkContainer {σ β : Type} [SszFields β] [LawfulSszFields β]
    {active : List Bool} {names : List String} {fields : σ → β} {build : β → σ}
    (layout : switch ≤ fork → active.getLast? = some true ∧
      active.length ≤ maxActiveFields ∧ active.count true = (SszFields.descs β).length)
    (named : names.length = (SszFields.descs β).length ∧ names ≠ [] ∧
      firstDuplicate names = none)
    (left : ∀ s, build (fields s) = s) (right : ∀ b, fields (build b) = b) :
    @LawfulSszType σ (SszType.forkContainer switch fork active names fields build) := by
  by_cases from_ : switch ≤ fork
  · have chosen : SszType.forkContainer switch fork active names fields build =
        .progressiveContainer active names fields build := by simp [SszType.forkContainer, from_]
    rw [chosen]
    exact LawfulSszType.progressiveContainer (layout from_) named left right
  · have chosen : SszType.forkContainer switch fork active names fields build =
        .container names fields build := by simp [SszType.forkContainer, from_]
    rw [chosen]
    exact LawfulSszType.container named left right

/-- Before the switch, a fork-chosen container is the container of the same fields. -/
theorem forkContainer_of_lt {σ β : Type} [SszFields β] {active : List Bool}
    {names : List String} {fields : σ → β} {build : β → σ} (before : fork < switch) :
    SszType.forkContainer switch fork active names fields build =
      SszType.container names fields build := by
  simp [SszType.forkContainer, not_switch_of_lt before]

end EthLib.Serialization.Ssz
