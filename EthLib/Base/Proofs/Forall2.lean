module

public import EthLib.Base.Proofs.MapM
public import Mathlib.Data.List.Forall2

/-!
# `Base.Proofs.Forall2`

A successful map over a list in `Except` pairs each input, a member of the list, with its output.

Each member of the left list of a pairing has a partner in the right list.

A pairing implies a second one when the first implies it on members of the left list.
-/

@[expose] public section

namespace EthLib.Base

/-- A successful map pairs each input, a member of the list, with its output. -/
theorem forall₂_mem_of_mapM_ok {α β ε : Type} {f : α → Except ε β} {xs : List α} {ys : List β}
    (made : xs.mapM f = .ok ys) : List.Forall₂ (fun x y => x ∈ xs ∧ f x = .ok y) xs ys := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at made
    subst made
    exact .nil
  | cons x xs ih =>
    obtain ⟨y, rest, head, tail, rfl⟩ := mapM_cons_ok.mp made
    exact .cons ⟨List.mem_cons_self, head⟩
      ((ih tail).imp fun _ _ related => ⟨List.mem_cons_of_mem _ related.1, related.2⟩)

/-- Each member of the left list of a pairing has a partner in the right list. -/
theorem exists_mem_of_forall₂ {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → ∀ {x}, x ∈ xs → ∃ y ∈ ys, R x y
  | _, _, .nil, _, mem => by simp at mem
  | _, _, .cons head tail, _, mem => by
    rcases List.mem_cons.mp mem with rfl | mem
    · exact ⟨_, List.mem_cons_self, head⟩
    · obtain ⟨y, mem', related⟩ := exists_mem_of_forall₂ tail mem
      exact ⟨y, List.mem_cons_of_mem _ mem', related⟩

/-- A pairing implies a second one when the first implies it on members of the left list. -/
theorem forall₂_imp_of_mem {α β : Type} {first second : α → β → Prop} :
    ∀ {left : List α} {right : List β}, List.Forall₂ first left right →
      (∀ a b, a ∈ left → first a b → second a b) → List.Forall₂ second left right
  | _, _, .nil, _ => .nil
  | _, _, .cons head tail, implies =>
    .cons (implies _ _ List.mem_cons_self head)
      (forall₂_imp_of_mem tail fun a b member => implies a b (.tail _ member))

end EthLib.Base
