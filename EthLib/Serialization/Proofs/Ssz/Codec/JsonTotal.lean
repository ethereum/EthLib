module

public import EthLib.Serialization.Proofs.Ssz.Codec.Admits
public import EthLib.Serialization.Ssz.Codec.Json
public import EthLib.Serialization.Ssz.Type.Valid

/-!
# Proofs: the JSON writer never fails without a byte alias

A well-formed type writes every value that it admits, when no declaration marks the byte alias.

With the alias marked, a sequence of wider integers would fail to write as hex.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open Lean

/-- The spelling that marks no alias gives no alias to any of its parts. -/
theorem Spelling.part_opaque (position : Nat) : Spelling.opaque.part position = .opaque := by
  simp [Spelling.opaque, Spelling.part]

/-- The spelling that marks no alias does not mark a byte. -/
theorem Spelling.isByte_opaque : Spelling.opaque.isByte = false := rfl

/-- Whether a type writes every value that it admits, under the spelling with no alias. -/
def WritesAll (shape : Desc) : Prop :=
  ∀ value : Value, Fits shape value → ∃ document, jsonOf shape .opaque value = .ok document

/-- Elements that each write give a list of documents. -/
theorem jsonOfEach_opaque_ok (element : Desc) : ∀ (elements : List Value),
    (∀ value ∈ elements, ∃ document, jsonOf element .opaque value = .ok document) →
    ∃ documents, jsonOfEach element .opaque elements = .ok documents
  | [], _ => ⟨[], by simp [jsonOfEach]⟩
  | value :: rest, each => by
    obtain ⟨head, wroteHead⟩ := each value List.mem_cons_self
    obtain ⟨tail, wroteTail⟩ :=
      jsonOfEach_opaque_ok element rest fun other member => each other (.tail _ member)
    exact ⟨head :: tail, by simp [jsonOfEach, wroteHead, wroteTail, Bind.bind, Except.bind,
      pure, Except.pure]⟩

/-- Elements that each write give a sequence document. -/
theorem jsonOfSequence_opaque_ok {element : Desc} {elements : List Value}
    (each : ∀ value ∈ elements, ∃ document, jsonOf element .opaque value = .ok document) :
    ∃ document, jsonOfSequence element .opaque elements = .ok document := by
  -- No alias collapses the elements, so they are written as an array.
  obtain ⟨documents, wrote⟩ := jsonOfEach_opaque_ok element elements each
  simp [jsonOfSequence, Spelling.isByte_opaque, wrote, Bind.bind, Except.bind, pure, Except.pure]

/-- Fields paired with values that each write give a list of documents. -/
theorem jsonOfFields_opaque_ok : ∀ (fields : List Desc) (values : List Value) (position : Nat),
    fields.length = values.length →
    (∀ pair ∈ fields.zip values, ∃ document, jsonOf pair.1 .opaque pair.2 = .ok document) →
    ∃ documents, jsonOfFields fields .opaque position values = .ok documents
  | [], [], _, _, _ => ⟨[], by simp [jsonOfFields]⟩
  | field :: fields, value :: values, position, paired, each => by
    obtain ⟨head, wroteHead⟩ := each (field, value) List.mem_cons_self
    obtain ⟨tail, wroteTail⟩ := jsonOfFields_opaque_ok fields values (position + 1)
      (by simpa using paired) fun pair member => each pair (.tail _ member)
    exact ⟨head :: tail, by simp [jsonOfFields, Spelling.part_opaque, wroteHead, wroteTail,
      Bind.bind, Except.bind, pure, Except.pure]⟩
  | [], _ :: _, _, paired, _ => by simp at paired
  | _ :: _, [], _, paired, _ => by simp at paired

/-- A well-formed type writes every value that it admits, under a spelling with no alias. -/
theorem jsonOf_opaque_ok {shape : Desc} {value : Value} (formed : shape.wellFormed = .ok ())
    (fitted : Fits shape value) : ∃ document, jsonOf shape .opaque value = .ok document := by
  revert formed value
  induction shape using Desc.rec
    (motive_2 := fun fields => Desc.allWellFormed fields = .ok () →
      ∀ field ∈ fields, WritesAll field) with
  | bool =>
    intro _ _ fitted
    cases fitted with
    | bool b => exact ⟨.bool b, by simp [jsonOf]⟩
  | uint width =>
    intro _ _ fitted
    cases fitted with
    | uint bound => simp [jsonOf, Nat.not_le.mpr bound, Spelling.isByte_opaque]
  | byteVector length =>
    intro _ _ fitted
    cases fitted with
    | byteVector exact => simp [jsonOf, exact]
  | byteList limit =>
    intro _ _ fitted
    cases fitted with
    | byteList within => simp [jsonOf, within]
  | bitVector length =>
    intro _ _ fitted
    cases fitted with
    | bitVector exact => simp [jsonOf, serialize, exact, Bind.bind, Except.bind, pure, Except.pure]
  | bitList limit =>
    intro _ _ fitted
    cases fitted with
    | bitList within => simp [jsonOf, serialize, within, Bind.bind, Except.bind, pure, Except.pure]
  | progressiveBitList limit =>
    intro _ _ fitted
    cases fitted with
    | progressiveBitList within =>
      simp [jsonOf, serialize, boundCheck_of_withinBound _ _ within, Bind.bind, Except.bind,
        pure, Except.pure]
  | vector element length ih =>
    intro _ sound fitted
    cases fitted with
    | vector count each =>
      obtain ⟨document, wrote⟩ := jsonOfSequence_opaque_ok fun value member =>
        ih (wellFormed_vector sound) (each value member)
      simp [jsonOf, count, Spelling.part_opaque, wrote]
  | list element limit ih =>
    intro _ sound fitted
    cases fitted with
    | list within each =>
      obtain ⟨document, wrote⟩ := jsonOfSequence_opaque_ok fun value member =>
        ih (wellFormed_list sound) (each value member)
      simp [jsonOf, within, Spelling.part_opaque, wrote]
  | progressiveList element limit ih =>
    intro _ sound fitted
    cases fitted with
    | progressiveList within each =>
      obtain ⟨document, wrote⟩ := jsonOfSequence_opaque_ok fun value member =>
        ih (wellFormed_progressiveList sound) (each value member)
      simp [jsonOf, boundCheck_of_withinBound _ _ within, Spelling.part_opaque, wrote,
        Bind.bind, Except.bind]
  | container names fields ih =>
    intro _ sound fitted
    cases fitted with
    | @container _ _ values paired each =>
      obtain ⟨documents, wrote⟩ := jsonOfFields_opaque_ok fields values 0 paired
        fun ⟨field, value⟩ member => ih (wellFormed_container sound) field
          (List.of_mem_zip member).1 value (each _ member)
      simp [jsonOf, wrote, Bind.bind, Except.bind, pure, Except.pure]
  | progressiveContainer active names fields ih =>
    intro _ sound fitted
    cases fitted with
    | @progressiveContainer _ _ _ values paired each =>
      obtain ⟨documents, wrote⟩ := jsonOfFields_opaque_ok fields values 0 paired
        fun ⟨field, value⟩ member => ih (wellFormed_progressiveContainer sound) field
          (List.of_mem_zip member).1 value (each _ member)
      simp [jsonOf, wrote, Bind.bind, Except.bind, pure, Except.pure]
  | compatibleUnion selectors options ih =>
    intro _ sound fitted
    cases fitted with
    | @compatibleUnion _ _ selector option data _ named inner =>
      obtain ⟨document, wrote⟩ := ih (wellFormed_union sound) option
        (lookupOption_mem _ _ _ _ named) data inner
      simp [jsonOf, named, Spelling.part_opaque, wrote, Bind.bind, Except.bind, pure, Except.pure]
  | nil =>
    rename_i _ field member
    simp at member
  | cons field fields ih ihRest =>
    rename_i sound target member
    rcases List.mem_cons.mp member with here | later
    · subst target
      exact fun _ fitted => ih (allWellFormed_mem _ sound field List.mem_cons_self) fitted
    · exact ihRest (allWellFormed_tail sound) target later

end EthLib.Serialization.Ssz
