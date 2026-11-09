module

public import EthLib.Base.Proofs.MapM
public import Mathlib.Data.List.Forall2

/-!
# `Base.Proofs.Forall2`

A successful map over a list in `Except` relates its inputs and outputs pairwise.

Each input is related to its output, and is a member of the list.

Conversely, inputs related pairwise to outputs make the map succeed with those outputs.

Each member of the left list of a pairing has a partner in the right list.
-/

@[expose] public section

namespace EthLib.Base

/-- The results of a monadic map that succeeds, one for each input. -/
theorem forall₂_of_mapM_ok {α β ε : Type} {f : α → Except ε β} :
    ∀ {inputs : List α} {outputs : List β}, inputs.mapM f = .ok outputs →
      List.Forall₂ (fun input output => f input = .ok output) inputs outputs
  | [], outputs, made => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at made
    subst made
    exact .nil
  | input :: inputs, outputs, made => by
    simp only [List.mapM_cons, bind, Except.bind] at made
    cases first : f input with
    | error e => simp [first] at made
    | ok output =>
      cases rest : inputs.mapM f with
      | error e => simp [first, rest] at made
      | ok others =>
        simp only [first, rest, pure, Except.pure, Except.ok.injEq] at made
        subst made
        exact .cons first (forall₂_of_mapM_ok rest)

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

/-- Inputs that each map to their partner make the monadic map succeed with the partners. -/
theorem mapM_ok_of_forall₂ {α β ε : Type} {f : α → Except ε β} {xs : List α} {ys : List β}
    (related : List.Forall₂ (fun x y => f x = .ok y) xs ys) : xs.mapM f = .ok ys := by
  induction related with
  | nil => rfl
  | cons head _ ih =>
    rw [List.mapM_cons, head, ih]
    rfl

/-- Each member of the left list of a pairing has a partner in the right list. -/
theorem exists_mem_of_forall₂ {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → ∀ {x}, x ∈ xs → ∃ y ∈ ys, R x y
  | _, _, .nil, _, mem => by simp at mem
  | _, _, .cons head tail, _, mem => by
    rcases List.mem_cons.mp mem with rfl | mem
    · exact ⟨_, List.mem_cons_self, head⟩
    · obtain ⟨y, mem', related⟩ := exists_mem_of_forall₂ tail mem
      exact ⟨y, List.mem_cons_of_mem _ mem', related⟩

end EthLib.Base
