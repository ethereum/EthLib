module

public import EthLib.Base.Except

/-!
# `Base.Proofs.FoldlM`

When a fold over a list in `Except` succeeds, read one input at a time.

Each input has a key, and the keys of the list are distinct.

A state is ready for an input when the step from it on that input succeeds.

The fold succeeds when each step keeps the state ready for the inputs with another key.
-/

@[expose] public section

namespace EthLib.Base

/-- A fold over inputs with distinct keys succeeds when each step from a ready state succeeds.

Each step must keep ready the inputs with another key. -/
theorem foldlM_exists_ok_of_distinct {α σ ε : Type} {step : σ → α → Except ε σ}
    (key : α → Nat) (Ready : σ → α → Prop)
    (advance : ∀ last x, Ready last x → ∃ next, step last x = .ok next ∧
      ∀ y, key y ≠ key x → Ready last y → Ready next y) :
    ∀ (xs : List α) (start : σ), (xs.map key).Nodup → (∀ x ∈ xs, Ready start x) →
      ∃ out, xs.foldlM step start = .ok out
  | [], start, _, _ => ⟨start, rfl⟩
  | x :: rest, start, distinct, ready => by
    rw [List.map_cons, List.nodup_cons] at distinct
    obtain ⟨next, stepped, keeps⟩ := advance start x (ready x List.mem_cons_self)
    obtain ⟨out, folded⟩ := foldlM_exists_ok_of_distinct key Ready advance rest next distinct.2
      fun y member => keeps y (fun same => distinct.1 (same ▸ List.mem_map_of_mem member))
        (ready y (List.mem_cons_of_mem _ member))
    exact ⟨out, by rw [List.foldlM_cons, stepped]; exact folded⟩

end EthLib.Base
