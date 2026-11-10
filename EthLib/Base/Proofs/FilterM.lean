module

public import EthLib.Base.Except
import all Init.Data.List.Control

/-!
# `Base.Proofs.FilterM`

What a successful filter over a list in `Except` returns: only elements of the list.

It keeps each element of the list that passes the test, and only those, in their order.

Lean core states no lemma about such a filter, so this module reads its definition.
-/

@[expose] public section

namespace EthLib.Base

variable {ε α : Type}

/-- A filter that a computation runs keeps only elements of its list, or of what it started with.
-/
theorem mem_of_filterAuxM_ok {test : α → Except ε Bool} :
    ∀ {list kept out : List α}, List.filterAuxM test list kept = .ok out →
      ∀ value ∈ out, value ∈ list ∨ value ∈ kept
  | [], kept, out, computed => by
    simp only [List.filterAuxM, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact fun _ member => .inr member
  | first :: rest, kept, out, computed => by
    simp only [List.filterAuxM, bind_ok_iff] at computed
    obtain ⟨chosen, _, computed⟩ := computed
    intro value member
    rcases mem_of_filterAuxM_ok computed value member with inside | earlier
    · exact .inl (List.mem_cons_of_mem first inside)
    · cases chosen
      · exact .inr earlier
      · rcases List.mem_cons.mp earlier with rfl | earlier
        · exact .inl List.mem_cons_self
        · exact .inr earlier

/-- A filter that a computation runs keeps only elements of its list. -/
theorem mem_of_filterM_ok {test : α → Except ε Bool} {list out : List α}
    (computed : list.filterM test = .ok out) {value : α} (member : value ∈ out) :
    value ∈ list := by
  simp only [List.filterM, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨reversed, filtered, rfl⟩ := computed
  rcases mem_of_filterAuxM_ok filtered value (List.mem_reverse.mp member) with inside | none
  · exact inside
  · cases none

/-- A filter that a computation runs keeps what it started with, and each element that passes. -/
private theorem mem_filterAuxM_ok {test : α → Except ε Bool} :
    ∀ {list kept out : List α}, List.filterAuxM test list kept = .ok out →
      (∀ value ∈ kept, value ∈ out) ∧ ∀ value ∈ list, test value = .ok true → value ∈ out
  | [], kept, out, computed => by
    simp only [List.filterAuxM, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨fun _ member => member, fun _ member => absurd member List.not_mem_nil⟩
  | first :: rest, kept, out, computed => by
    simp only [List.filterAuxM, bind_ok_iff] at computed
    obtain ⟨chosen, chosenOk, computed⟩ := computed
    obtain ⟨keeps, passes⟩ := mem_filterAuxM_ok computed
    refine ⟨fun value member => keeps value ?_, fun value member test => ?_⟩
    · cases chosen
      · exact member
      · exact List.mem_cons_of_mem first member
    · rcases List.mem_cons.mp member with rfl | later
      · rw [chosenOk, Except.ok.injEq] at test
        subst test
        exact keeps value List.mem_cons_self
      · exact passes value later test

/-- A filter that a computation runs keeps each element of its list that passes the test. -/
theorem mem_filterM_ok_of_test {test : α → Except ε Bool} {list out : List α}
    (computed : list.filterM test = .ok out) {value : α} (member : value ∈ list)
    (passes : test value = .ok true) : value ∈ out := by
  simp only [List.filterM, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨reversed, filtered, rfl⟩ := computed
  exact List.mem_reverse.mpr ((mem_filterAuxM_ok filtered).2 value member passes)

/-- Each element that a filter returns was kept before, or passes the test. -/
private theorem passes_of_filterAuxM_ok {test : α → Except ε Bool} :
    ∀ {list kept out : List α}, List.filterAuxM test list kept = .ok out →
      ∀ value ∈ out, value ∈ kept ∨ test value = .ok true
  | [], kept, out, computed => by
    simp only [List.filterAuxM, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact fun _ member => .inl member
  | first :: rest, kept, out, computed => by
    simp only [List.filterAuxM, bind_ok_iff] at computed
    obtain ⟨chosen, chosenOk, computed⟩ := computed
    intro value member
    rcases passes_of_filterAuxM_ok computed value member with earlier | passes
    · cases chosen
      · exact .inl earlier
      · rcases List.mem_cons.mp earlier with rfl | earlier
        · exact .inr chosenOk
        · exact .inl earlier
    · exact .inr passes

/-- A filter that a computation runs keeps only elements that pass the test. -/
theorem passes_of_mem_filterM_ok {test : α → Except ε Bool} {list out : List α}
    (computed : list.filterM test = .ok out) {value : α} (member : value ∈ out) :
    test value = .ok true := by
  simp only [List.filterM, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨reversed, filtered, rfl⟩ := computed
  rcases passes_of_filterAuxM_ok filtered value (List.mem_reverse.mp member) with none | passes
  · cases none
  · exact passes

/-- A filter that a computation runs puts a part of its list, reversed, before what it started with.
-/
private theorem sublist_of_filterAuxM_ok {test : α → Except ε Bool} :
    ∀ {list kept out : List α}, List.filterAuxM test list kept = .ok out →
      ∃ chosen : List α, chosen.Sublist list ∧ out = chosen.reverse ++ kept
  | [], kept, out, computed => by
    simp only [List.filterAuxM, pure, Except.pure, Except.ok.injEq] at computed
    exact ⟨[], List.Sublist.slnil, by simp [computed]⟩
  | first :: rest, kept, out, computed => by
    simp only [List.filterAuxM, bind_ok_iff] at computed
    obtain ⟨chosen, -, computed⟩ := computed
    obtain ⟨part, sub, rfl⟩ := sublist_of_filterAuxM_ok computed
    cases chosen
    · exact ⟨part, sub.cons first, rfl⟩
    · exact ⟨first :: part, sub.cons_cons first, by simp⟩

/-- A filter that a computation runs returns a part of its list, in order. -/
theorem sublist_of_filterM_ok {test : α → Except ε Bool} {list out : List α}
    (computed : list.filterM test = .ok out) : out.Sublist list := by
  simp only [List.filterM, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨reversed, filtered, rfl⟩ := computed
  obtain ⟨chosen, sub, rfl⟩ := sublist_of_filterAuxM_ok filtered
  simpa using sub

end EthLib.Base
