module

public import EthLib.Serialization.Proofs.Ssz.Codec.Admits
public import EthLib.Serialization.Ssz.Codec.Json
public import EthLib.Serialization.Ssz.Type.Valid

/-!
# Proofs: the JSON writer never fails

A well-formed type writes every value that it admits, under every spelling.

A mark has effect only where its shape allows it, so no mark makes the writer fail.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open Lean

/-- Elements that each write give a list of documents. -/
theorem jsonOfEach_ok (element : Desc) (spelling : Spelling) : ∀ (elements : List Value),
    (∀ value ∈ elements, ∃ document, jsonOf element spelling value = .ok document) →
    ∃ documents, jsonOfEach element spelling elements = .ok documents
  | [], _ => ⟨[], by simp [jsonOfEach]⟩
  | value :: rest, each => by
    obtain ⟨head, wroteHead⟩ := each value List.mem_cons_self
    obtain ⟨tail, wroteTail⟩ :=
      jsonOfEach_ok element spelling rest fun other member => each other (.tail _ member)
    exact ⟨head :: tail, by simp [jsonOfEach, wroteHead, wroteTail, Bind.bind, Except.bind,
      pure, Except.pure]⟩

/-- A run of one-byte integers that fit holds bytes. -/
theorem byteRun_ok : ∀ (elements : List Value),
    (∀ value ∈ elements, Fits (.uint 1) value) → ∃ data, byteRun elements = .ok data
  | [], _ => ⟨#[], byteRun_nil⟩
  | value :: rest, each => by
    obtain ⟨data, wrote⟩ :=
      byteRun_ok rest fun other member => each other (.tail _ member)
    have held := each value List.mem_cons_self
    cases held with
    | uint bound =>
      rename_i n
      have small : ¬ n ≥ 256 := by simp at bound; omega
      exact ⟨#[UInt8.ofNat n] ++ data, by
        simp [byteRun_uint, small, wrote, Bind.bind, Except.bind, pure, Except.pure]⟩

/-- Elements that each fit and write give a sequence document, under every spelling. -/
theorem jsonOfSequence_ok {element : Desc} {elements : List Value} (spelling : Spelling)
    (fitted : ∀ value ∈ elements, Fits element value)
    (each : ∀ value ∈ elements, ∃ document, jsonOf element spelling value = .ok document) :
    ∃ document, jsonOfSequence element spelling elements = .ok document := by
  obtain ⟨documents, wrote⟩ := jsonOfEach_ok element spelling elements each
  by_cases alias? : (spelling.isByte && element.isOneByte) = true
  · -- The alias applies only to one-byte integers, and each element of the run fits one.
    have single : element = .uint 1 := by
      cases element <;> simp [Desc.isOneByte] at alias?
      rename_i width
      by_cases one : width = 1 <;> simp_all
    subst single
    obtain ⟨data, run⟩ := byteRun_ok elements fitted
    simp [jsonOfSequence, alias?, run, Bind.bind, Except.bind, pure, Except.pure]
  · simp [jsonOfSequence, alias?, wrote, Bind.bind, Except.bind, pure, Except.pure]

/-- Fields paired with values that each write give a list of documents. -/
theorem jsonOfFields_ok (spelling : Spelling) :
    ∀ (fields : List Desc) (values : List Value) (position : Nat),
    fields.length = values.length →
    (∀ pair ∈ fields.zip values, ∀ spelling,
      ∃ document, jsonOf pair.1 spelling pair.2 = .ok document) →
    ∃ documents, jsonOfFields fields spelling position values = .ok documents
  | [], [], _, _, _ => ⟨[], by simp [jsonOfFields]⟩
  | field :: fields, value :: values, position, paired, each => by
    obtain ⟨head, wroteHead⟩ := each (field, value) List.mem_cons_self (spelling.part position)
    obtain ⟨tail, wroteTail⟩ := jsonOfFields_ok spelling fields values (position + 1)
      (by simpa using paired) fun pair member => each pair (.tail _ member)
    exact ⟨head :: tail, by simp [jsonOfFields, wroteHead, wroteTail,
      Bind.bind, Except.bind, pure, Except.pure]⟩
  | [], _ :: _, _, paired, _ => by simp at paired
  | _ :: _, [], _, paired, _ => by simp at paired

/-- A well-formed type writes every value that it admits, under every spelling. -/
theorem jsonOf_ok {shape : Desc} {value : Value} (formed : shape.wellFormed = .ok ())
    (fitted : Fits shape value) (spelling : Spelling) :
    ∃ document, jsonOf shape spelling value = .ok document := by
  revert formed value spelling
  induction shape using Desc.rec
    (motive_2 := fun fields => Desc.allWellFormed fields = .ok () →
      ∀ field ∈ fields, ∀ value, Fits field value → ∀ spelling,
        ∃ document, jsonOf field spelling value = .ok document) with
  | bool =>
    intro _ _ fitted _
    cases fitted with
    | bool b => exact ⟨.bool b, by simp [jsonOf]⟩
  | uint width =>
    intro _ _ fitted spelling
    cases fitted with
    | uint bound =>
      by_cases alias? : (spelling.isByte && width == 1) = true <;>
        simp [jsonOf, Nat.not_le.mpr bound, alias?]
  | byteVector length =>
    intro _ _ fitted _
    cases fitted with
    | byteVector exact => simp [jsonOf, exact]
  | byteList limit =>
    intro _ _ fitted spelling
    cases fitted with
    | byteList within => simp [jsonOf, within]
  | bitVector length =>
    intro _ _ fitted _
    cases fitted with
    | bitVector exact => simp [jsonOf, serialize, exact, Bind.bind, Except.bind, pure, Except.pure]
  | bitList limit =>
    intro _ _ fitted _
    cases fitted with
    | bitList within => simp [jsonOf, serialize, within, Bind.bind, Except.bind, pure, Except.pure]
  | progressiveBitList limit =>
    intro _ _ fitted _
    cases fitted with
    | progressiveBitList within =>
      simp [jsonOf, serialize, boundCheck_of_withinBound _ _ within, Bind.bind, Except.bind,
        pure, Except.pure]
  | vector element length ih =>
    intro _ sound fitted spelling
    cases fitted with
    | vector count each =>
      obtain ⟨document, wrote⟩ := jsonOfSequence_ok (spelling.part 0) each fun value member =>
        ih (wellFormed_vector sound) (each value member) _
      simp [jsonOf, count, wrote]
  | list element limit ih =>
    intro _ sound fitted spelling
    cases fitted with
    | list within each =>
      obtain ⟨document, wrote⟩ := jsonOfSequence_ok (spelling.part 0) each fun value member =>
        ih (wellFormed_list sound) (each value member) _
      simp [jsonOf, within, wrote]
  | progressiveList element limit ih =>
    intro _ sound fitted spelling
    cases fitted with
    | progressiveList within each =>
      obtain ⟨document, wrote⟩ := jsonOfSequence_ok (spelling.part 0) each fun value member =>
        ih (wellFormed_progressiveList sound) (each value member) _
      simp [jsonOf, boundCheck_of_withinBound _ _ within, wrote, Bind.bind, Except.bind]
  | container names fields ih =>
    intro _ sound fitted spelling
    cases fitted with
    | @container _ _ values paired each =>
      obtain ⟨documents, wrote⟩ := jsonOfFields_ok spelling fields values 0 paired
        fun ⟨field, value⟩ member => ih (wellFormed_container sound) field
          (List.of_mem_zip member).1 value (each _ member)
      simp [jsonOf, wrote, Bind.bind, Except.bind, pure, Except.pure]
  | progressiveContainer active names fields ih =>
    intro _ sound fitted spelling
    cases fitted with
    | @progressiveContainer _ _ _ values paired each =>
      obtain ⟨documents, wrote⟩ := jsonOfFields_ok spelling fields values 0 paired
        fun ⟨field, value⟩ member => ih (wellFormed_progressiveContainer sound) field
          (List.of_mem_zip member).1 value (each _ member)
      simp [jsonOf, wrote, Bind.bind, Except.bind, pure, Except.pure]
  | compatibleUnion selectors options ih =>
    intro _ sound fitted spelling
    cases fitted with
    | @compatibleUnion _ _ selector option data _ named inner =>
      obtain ⟨document, wrote⟩ := ih (wellFormed_union sound) option
        (lookupOption_mem _ _ _ _ named) data inner
        (spelling.part ((selectors.findIdx? (· == selector)).getD 0))
      simp [jsonOf, named, wrote, Bind.bind, Except.bind, pure, Except.pure]
  | nil =>
    rename_i _ _ member _ _ _
    simp at member
  | cons field fields ih ihRest =>
    rename_i sound target member value fitted spelling
    rcases List.mem_cons.mp member with here | later
    · subst here
      exact ih (allWellFormed_mem _ sound _ List.mem_cons_self) fitted spelling
    · exact ihRest (allWellFormed_tail sound) target later value fitted spelling

end EthLib.Serialization.Ssz
