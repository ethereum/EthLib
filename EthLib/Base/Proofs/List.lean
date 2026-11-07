module

/-!
# `Base.Proofs.List`

Facts about lists that Lean core does not prove and that several layers use.

Removing the duplicates of a list leaves each element once.
-/

@[expose] public section

namespace EthLib.Base

/-- Removing the duplicates of a list leaves a list in which each element comes once. -/
theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] (l : List α) : l.eraseDups.Nodup := by
  -- The recursion removes the head from the tail, so it runs on the length.
  suffices ∀ n, ∀ l : List α, l.length ≤ n → l.eraseDups.Nodup from this _ l (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro l short
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp short)]
    exact List.nodup_nil
  | succ n ih =>
    intro l short
    cases l with
    | nil => exact List.nodup_nil
    | cons head tail =>
      rw [List.eraseDups_cons]
      refine List.nodup_cons.mpr ⟨fun mem => ?_, ih _ ?_⟩
      · rw [List.mem_eraseDups, List.mem_filter] at mem
        simp at mem
      · exact Nat.le_trans (List.length_filter_le _ _) (by simpa using short)

end EthLib.Base
