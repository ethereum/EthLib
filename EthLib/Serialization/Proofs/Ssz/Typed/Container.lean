module

public import EthLib.Serialization.Ssz.Typed.Container
public import EthLib.Serialization.Proofs.Ssz.Typed.Class
public import EthLib.Serialization.Proofs.Ssz.Codec.RootDomain
public import EthLib.Serialization.Proofs.Ssz.Codec.Summary

/-!
# Proofs: typed SSZ containers are lawful

The fields of a container convert one by one, so their laws follow from those of each field.

A structure is then lawful when it converts to and from the tuple of its fields without loss.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open SszType SszFields

/-- The laws of the fields of a container, as those of a typed value hold for one field. -/
class LawfulSszFields (β : Type) [SszFields β] : Prop where
  /-- Every field type is well formed. -/
  allWellFormed : Desc.allWellFormed (descs β) = .ok ()
  /-- Every field stands for a value that its own type admits, one value for each type. -/
  fits : ∀ b : β, (descs β).length = (toValues b).length ∧
    ∀ pair ∈ (descs β).zip (toValues b), Fits pair.1 pair.2
  /-- Reading back untyped fields gives the typed fields they came from. -/
  ofValues_toValues : ∀ b : β, ofValues (toValues b) = .ok b
  /-- Untyped fields that read back are the ones their typed fields stand for. -/
  toValues_of_ofValues : ∀ {values : List Value} {b : β}, ofValues values = .ok b →
    toValues b = values
  /-- The roots of the fields are the roots of their untyped values. -/
  roots_eq : ∀ b : β,
    roots b = ((descs β).zip (toValues b)).mapM fun field => Ssz.hashTreeRoot field.1 field.2

instance (priority := low) {α : Type} [SszType α] [LawfulSszType α] : LawfulSszFields α where
  allWellFormed := by
    simp [descs, Desc.allWellFormed, LawfulSszType.wellFormed (α := α), bind, Except.bind]
  fits a := by simpa [descs, toValues] using LawfulSszType.fits a
  ofValues_toValues a := LawfulSszType.ofValue_toValue a
  toValues_of_ofValues {values a} read := by
    match values, read with
    | [value], read => simp [toValues, LawfulSszType.toValue_of_ofValue read]
    | [], read | _ :: _ :: _, read => cases read
  roots_eq a := by simp [roots, descs, toValues, LawfulSszType.root_eq]

instance {α β : Type} [SszType α] [LawfulSszType α] [SszFields β] [LawfulSszFields β] :
    LawfulSszFields (α × β) where
  allWellFormed := by
    simp [descs, Desc.allWellFormed, LawfulSszType.wellFormed (α := α),
      LawfulSszFields.allWellFormed (β := β), bind, Except.bind]
  fits pair := by
    obtain ⟨count, each⟩ := LawfulSszFields.fits pair.2
    refine ⟨by simp [descs, toValues, count], ?_⟩
    simp only [descs, toValues, List.zip_cons_cons, List.mem_cons, forall_eq_or_imp]
    exact ⟨LawfulSszType.fits pair.1, each⟩
  ofValues_toValues pair := by
    simp [toValues, ofValues, LawfulSszType.ofValue_toValue, LawfulSszFields.ofValues_toValues,
      bind, Except.bind, pure, Except.pure]
  toValues_of_ofValues {values pair} read := by
    match values, read with
    | [], read => cases read
    | value :: rest, read =>
      simp only [ofValues, bind, Except.bind] at read
      cases head : ofValue (α := α) value with
      | error fault => simp [head] at read
      | ok first =>
        cases tail : ofValues (β := β) rest with
        | error fault => simp [head, tail] at read
        | ok others =>
          simp only [head, tail, pure, Except.pure, Except.ok.injEq] at read
          subst read
          simp [toValues, LawfulSszType.toValue_of_ofValue head,
            LawfulSszFields.toValues_of_ofValues tail]
  roots_eq pair := by
    simp [roots, descs, toValues, LawfulSszType.root_eq, LawfulSszFields.roots_eq (β := β)]

/-- Fields of well-formed types, each admitting its value, all have roots. -/
theorem fieldRoots_total : ∀ {fields : List (Desc × Value)},
    (∀ field ∈ fields, field.1.wellFormed = .ok () ∧ Fits field.1 field.2) →
    ∃ roots, fields.mapM (fun field => Ssz.hashTreeRoot field.1 field.2) = .ok roots
  | [], _ => ⟨[], rfl⟩
  | field :: fields, sound => by
    obtain ⟨root, rooted, -⟩ := Ssz.hashTreeRoot_total field.1 field.2
      (sound field (by simp)).1 (sound field (by simp)).2
    obtain ⟨roots, rest⟩ := fieldRoots_total fun other member =>
      sound other (List.mem_cons_of_mem _ member)
    exact ⟨root :: roots, by simp [List.mapM_cons, rooted, rest, bind, Except.bind, pure,
      Except.pure]⟩

/-- The fields of lawful types all have roots. -/
theorem LawfulSszFields.roots_total {β : Type} [SszFields β] [LawfulSszFields β] (b : β) :
    ∃ roots, ((descs β).zip (toValues b)).mapM
      (fun field => Ssz.hashTreeRoot field.1 field.2) = .ok roots :=
  fieldRoots_total fun field member =>
    ⟨allWellFormed_mem _ LawfulSszFields.allWellFormed _ (List.of_mem_zip member).1,
      (LawfulSszFields.fits b).2 field member⟩

/--
A container is lawful when its names are well formed and its two conversions undo each other.

The names must be distinct, at least one, and one for each field.
-/
theorem LawfulSszType.container {σ β : Type} [SszFields β] [LawfulSszFields β]
    {names : List String} {fields : σ → β} {build : β → σ}
    (named : names.length = (descs β).length ∧ names ≠ [] ∧ firstDuplicate names = none)
    (left : ∀ s, build (fields s) = s) (right : ∀ b, fields (build b) = b) :
    @LawfulSszType σ (SszType.container names fields build) := by
  letI := SszType.container names fields build
  obtain ⟨count, present, distinct⟩ := named
  have nonempty : descs β ≠ [] := fun empty => present (List.eq_nil_of_length_eq_zero (by
    simp [count, empty]))
  exact {
    wellFormed := by
      simp [desc, Desc.wellFormed, List.isEmpty_iff, nonempty, count, distinct,
        LawfulSszFields.allWellFormed (β := β)]
    fits := fun s => .container (LawfulSszFields.fits (fields s)).1
      (LawfulSszFields.fits (fields s)).2
    ofValue_toValue := fun s => by
      simp [toValue, ofValue, LawfulSszFields.ofValues_toValues, left, Functor.map, Except.map]
    toValue_of_ofValue := fun {value s} made => by
      cases value <;> simp only [ofValue] at made <;> try cases made
      rename_i values
      cases read : ofValues (β := β) values with
      | error fault => simp [read, Functor.map, Except.map] at made
      | ok b =>
        simp only [read, Functor.map, Except.map, Except.ok.injEq] at made
        subst made
        simp [toValue, right, LawfulSszFields.toValues_of_ofValues read]
    root_eq := fun s => by
      -- Every field has a root, and the container of those roots has the container's root.
      obtain ⟨roots, rooted⟩ := LawfulSszFields.roots_total (fields s)
      simp only [root, LawfulSszFields.roots_eq, rooted, bind, Except.bind, summaryRoot]
      exact hashTreeRoot_container_roots (LawfulSszFields.fits (fields s)).1 rooted }

/--
A progressive container is lawful when its layout and names are well formed.

The layout ends on a set bit, has at most 256 bits, and sets one bit for each field.

The names must be distinct, at least one, and one for each field.

The two conversions must undo each other.
-/
theorem LawfulSszType.progressiveContainer {σ β : Type} [SszFields β] [LawfulSszFields β]
    {active : List Bool} {names : List String} {fields : σ → β} {build : β → σ}
    (layout : active.getLast? = some true ∧ active.length ≤ maxActiveFields ∧
      active.count true = (descs β).length)
    (named : names.length = (descs β).length ∧ names ≠ [] ∧ firstDuplicate names = none)
    (left : ∀ s, build (fields s) = s) (right : ∀ b, fields (build b) = b) :
    @LawfulSszType σ (SszType.progressiveContainer active names fields build) := by
  letI := SszType.progressiveContainer active names fields build
  obtain ⟨last, narrow, set⟩ := layout
  obtain ⟨count, present, distinct⟩ := named
  have nonempty : descs β ≠ [] := fun empty => present (List.eq_nil_of_length_eq_zero (by
    simp [count, empty]))
  have occupied : active ≠ [] := by rintro rfl; simp at last
  exact {
    wellFormed := by
      simp [desc, Desc.wellFormed, List.isEmpty_iff, occupied, last, Nat.not_lt.mpr narrow,
        nonempty, ← set, List.count, count, distinct, LawfulSszFields.allWellFormed (β := β)]
    fits := fun s => .progressiveContainer (LawfulSszFields.fits (fields s)).1
      (LawfulSszFields.fits (fields s)).2
    ofValue_toValue := fun s => by
      simp [toValue, ofValue, LawfulSszFields.ofValues_toValues, left, Functor.map, Except.map]
    toValue_of_ofValue := fun {value s} made => by
      cases value <;> simp only [ofValue] at made <;> try cases made
      rename_i values
      cases read : ofValues (β := β) values with
      | error fault => simp [read, Functor.map, Except.map] at made
      | ok b =>
        simp only [read, Functor.map, Except.map, Except.ok.injEq] at made
        subst made
        simp [toValue, right, LawfulSszFields.toValues_of_ofValues read]
    root_eq := fun s => by
      -- Every field has a root, and the container of those roots has the container's root.
      obtain ⟨roots, rooted⟩ := LawfulSszFields.roots_total (fields s)
      simp only [root, LawfulSszFields.roots_eq, rooted, bind, Except.bind, summaryRoot]
      exact hashTreeRoot_progressiveContainer_roots (LawfulSszFields.fits (fields s)).1 rooted }

end EthLib.Serialization.Ssz
