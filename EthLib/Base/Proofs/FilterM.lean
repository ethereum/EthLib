module

public import EthLib.Base.Except
import all Init.Data.List.Control

/-!
# `Base.Proofs.FilterM`

What a successful filter over a list in `Except` returns: only elements of the list.

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

end EthLib.Base
