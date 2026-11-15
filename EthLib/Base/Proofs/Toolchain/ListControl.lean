module

-- The equations below restate the bodies of `List.filterAuxM` and `List.filterM`.
import all Init.Data.List.Control

/-!
# `Base.Proofs.Toolchain.ListControl`

The equations of the monadic filter over a list, from `Init.Data.List.Control` of Lean.

Lean states no lemma about `List.filterM` or its helper `List.filterAuxM`.

This module reads their bodies and states them as public theorems.

Other proofs cite these theorems, so a Lean release that changes a body breaks this file only.
-/

@[expose] public section

namespace EthLib.Base.Toolchain

universe v

variable {m : Type → Type v} [Monad m] {α : Type}

/-- On the empty list, the helper returns what it kept. -/
theorem filterAuxM_nil (f : α → m Bool) (acc : List α) :
    List.filterAuxM f [] acc = pure acc := by
  rw [List.filterAuxM]

/-- On a nonempty list, the helper tests the head, keeps it in front when it passes, and goes on. -/
theorem filterAuxM_cons (f : α → m Bool) (head : α) (tail acc : List α) :
    List.filterAuxM f (head :: tail) acc =
      f head >>= fun b => List.filterAuxM f tail (cond b (head :: acc) acc) := by
  rw [List.filterAuxM]

/-- The filter runs the helper from an empty list and reverses what it kept. -/
theorem filterM_eq (p : α → m Bool) (as : List α) :
    as.filterM p = List.filterAuxM p as [] >>= fun kept => pure kept.reverse := by
  rw [List.filterM]

end EthLib.Base.Toolchain
