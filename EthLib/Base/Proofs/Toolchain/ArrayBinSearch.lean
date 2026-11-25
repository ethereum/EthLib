module

-- The proofs below read the bodies of `Array.binSearch` and `Array.binSearchAux`.
import all Init.Data.Array.BinSearch

/-!
# `Base.Proofs.Toolchain.ArrayBinSearch`

What a binary search finds, from `Init.Data.Array.BinSearch` of Lean.

Lean states no lemma about `Array.binSearch`.

This module reads its body and states the fact as a public theorem.

Other proofs cite it, so a Lean release that changes the body breaks this file only.
-/

@[expose] public section

namespace EthLib.Base.Toolchain.Array

universe u

/-- A range search that finds an entry finds an array entry, neither below nor above the key. -/
theorem binSearchAux_some {α : Type u} {lt : α → α → Bool} {as : Array α} {k a : α}
    (lo : Fin (as.size + 1)) (hi : Fin as.size) (h : lo.1 ≤ hi.1)
    (found : Array.binSearchAux lt id as k lo hi h = some a) :
    a ∈ as ∧ lt a k = false ∧ lt k a = false := by
  revert found
  fun_induction Array.binSearchAux lt id as k lo hi h
  all_goals intro found
  -- The search goes on in one half of the range.
  case case1 ih => exact ih found
  case case4 ih => exact ih found
  -- The search ends with nothing found.
  case case2 => simp at found
  case case3 => simp at found
  -- The middle entry is neither below nor above the key.
  case case5 below above _ =>
    simp only [id, Option.some.injEq] at found
    subst found
    exact ⟨Array.getElem_mem _, by simpa using below, by simpa using above⟩

/-- A full search that finds an entry finds an array entry, neither below nor above the key. -/
theorem binSearch_some {α : Type} {lt : α → α → Bool} {as : Array α} {k a : α}
    (found : as.binSearch k lt = some a) : a ∈ as ∧ lt a k = false ∧ lt k a = false := by
  unfold Array.binSearch at found
  dsimp only at found
  -- Each branch either searches a range of the array or finds nothing.
  repeat' split at found
  all_goals first | exact binSearchAux_some _ _ _ found | simp at found

end EthLib.Base.Toolchain.Array
