module

public import EthLib.Consensus.ForkChoice.FastConfirmation
public import EthLib.Consensus.Proofs.ForkChoice.Store

/-!
# Proofs: the walk of roots from a block back to an older block

`getAncestorRoots` lists the roots from a block back to a terminal block, oldest first.

The list leaves out the terminal block.

- A successful walk is empty, or it ends with the block that it starts from.
- A walk that returns a root starts at a block above the terminal block.
- The roots of a walk after one of its roots are the walk from the block back to that root.

The last fact joins two walks into one.

A proof needs it when a definition walks to a root of an earlier walk and then onwards from it.

No theorem here states that the roots of a walk are ancestors of the block.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Fork}

namespace Store

variable {store : Store preset fork}

/-- A successful walk back from a block is empty, or it ends with that block.

The roots that the walk had when it reached the block follow, unchanged. -/
theorem getAncestorRoots_eq_nil_or {root terminal : Root} {acc roots : List Root}
    (walked : store.getAncestorRoots root terminal acc = .ok roots) :
    roots = [] ∨ ∃ older, roots = older ++ root :: acc := by
  fun_induction getAncestorRoots store root terminal acc generalizing roots with
  | case1 => cases walked
  | case2 root acc block found ih =>
    rw [bind_ok_iff] at walked
    obtain ⟨terminalBlock, -, walked⟩ := walked
    split at walked
    · exact Or.inl (Except.ok.inj walked).symm
    · dsimp only at walked
      split at walked
      · exact Or.inr ⟨[], (Except.ok.inj walked).symm⟩
      · split at walked
        · cases walked
        · rename_i parent parentFound
          split at walked
          · rename_i lower
            -- The walk from the parent puts the parent in front of this block.
            rcases ih parent parentFound lower walked with empty | ⟨older, rfl⟩
            · exact Or.inl empty
            · exact Or.inr ⟨older ++ [block.parentRoot], by simp⟩
          · cases walked

/-- A walk that returns a root starts at a known block above the terminal block.

The terminal block is known too. -/
theorem slot_lt_of_getAncestorRoots {root terminal : Root} {acc roots : List Root}
    (walked : store.getAncestorRoots root terminal acc = .ok roots) (nonempty : roots ≠ []) :
    ∃ block terminalBlock, store.blocks[root]? = some block ∧
      store.block terminal = .ok terminalBlock ∧ terminalBlock.slot < block.slot := by
  unfold getAncestorRoots at walked
  split at walked
  · cases walked
  · rename_i block found
    rw [bind_ok_iff] at walked
    obtain ⟨terminalBlock, terminalFound, walked⟩ := walked
    split at walked
    · exact absurd (Except.ok.inj walked).symm nonempty
    · rename_i higher
      exact ⟨block, terminalBlock, found, terminalFound, by simpa using higher⟩

/-- The walk back to a root of a longer walk returns the roots after it, from any block.

The roots `acc` and `otherAcc` are what each walk had when it reached the block.

The roots `newer` come before `acc` in the longer walk, and there is one at least. -/
private theorem getAncestorRoots_of_append_aux {root terminal mid : Root}
    {acc otherAcc older newer : List Root}
    (walked : store.getAncestorRoots root terminal acc = .ok (older ++ mid :: (newer ++ acc)))
    (nonempty : newer ≠ []) :
    store.getAncestorRoots root mid otherAcc = .ok (newer ++ otherAcc) := by
  fun_induction getAncestorRoots store root terminal acc generalizing otherAcc older newer with
  | case1 => cases walked
  | case2 root acc block found ih =>
    rw [bind_ok_iff] at walked
    obtain ⟨terminalBlock, -, walked⟩ := walked
    split at walked
    · simp [pure, Except.pure] at walked
    · dsimp only at walked
      split at walked
      · -- The walk ends here with one new root, which is `mid`, so `newer` is empty.
        have sizes := congrArg List.length (Except.ok.inj walked)
        simp only [List.length_cons, List.length_append] at sizes
        exact absurd (List.length_eq_zero_iff.mp (by omega)) nonempty
      · split at walked
        · cases walked
        · rename_i parent parentFound
          split at walked
          · rename_i lower
            -- The longer walk ends with the parent, this block, and then `acc`.
            rcases getAncestorRoots_eq_nil_or walked with empty | ⟨front, shape⟩
            · simp at empty
            -- So this block is the last root of `newer`.
            rcases List.eq_nil_or_concat newer with rfl | ⟨init, final, rfl⟩
            · exact absurd rfl nonempty
            have shape' : (older ++ mid :: init) ++ [final] ++ acc =
                (front ++ [block.parentRoot]) ++ [root] ++ acc := by simpa using shape
            obtain ⟨fronts, finals⟩ := List.append_inj' (List.append_cancel_right shape') rfl
            obtain rfl : root = final := by simpa using finals.symm
            rw [getAncestorRoots]
            split
            · rename_i missing
              rw [found] at missing
              cases missing
            rename_i same sameFound
            obtain rfl : block = same := Option.some.inj (found.symm.trans sameFound)
            cases init with
            | nil =>
              -- The parent is `mid`, so the walk back to `mid` stops at this block.
              obtain rfl : mid = block.parentRoot := by
                simpa using (List.append_inj' fronts rfl).2
              have midFound : store.block block.parentRoot = .ok parent :=
                block_ok_iff.mpr parentFound
              simp [midFound, bind, Except.bind, pure, Except.pure, lower]
            | cons next rest =>
              -- The walk from the parent back to `mid` returns the roots before this block.
              have recursed := ih parent parentFound lower (otherAcc := root :: otherAcc)
                (older := older) (newer := next :: rest) (by simpa using walked) (by simp)
              -- That walk returns a root, so `mid` is below the parent, and so below the block.
              obtain ⟨sameParent, midBlock, sameParentFound, midFound, midLower⟩ :=
                slot_lt_of_getAncestorRoots recursed (by simp)
              obtain rfl : parent = sameParent :=
                Option.some.inj (parentFound.symm.trans sameParentFound)
              have notMid : block.parentRoot ≠ mid := by
                rintro rfl
                rw [block_ok_iff.mpr parentFound] at midFound
                cases midFound
                exact absurd midLower (UInt64.lt_irrefl _)
              have higher : ¬block.slot ≤ midBlock.slot :=
                UInt64.not_le.mpr (UInt64.lt_trans midLower lower)
              simp only [midFound, bind, Except.bind, reduceIte, higher, notMid]
              split
              · rename_i missing
                rw [parentFound] at missing
                cases missing
              · rename_i other otherFound
                obtain rfl : parent = other :=
                  Option.some.inj (parentFound.symm.trans otherFound)
                rw [dite_eq_left_of_eq_true (eq_true lower), recursed]
                simp
          · cases walked

/-- The walk from a block back to a root of a longer walk returns the roots after that root.

So the roots of a walk after one of its roots are the walk from the block back to that root. -/
theorem getAncestorRoots_of_append {head terminal mid : Root} {older newer : List Root}
    (walked : store.getAncestorRoots head terminal = .ok (older ++ mid :: newer)) :
    store.getAncestorRoots head mid = .ok newer := by
  rcases List.eq_nil_or_concat newer with rfl | ⟨init, final, rfl⟩
  · -- The walk ends with `mid`, so `mid` is the block, and a block has no root above itself.
    obtain ⟨block, -, found, -, -⟩ := slot_lt_of_getAncestorRoots walked (by simp)
    rcases getAncestorRoots_eq_nil_or walked with empty | ⟨front, shape⟩
    · simp at empty
    obtain rfl : head = mid := by simpa using (List.append_inj' shape rfl).2.symm
    rw [getAncestorRoots]
    split
    · rename_i missing
      rw [found] at missing
      cases missing
    · rename_i same sameFound
      simp [block_ok_iff.mpr sameFound, bind, Except.bind, pure, Except.pure]
  · simpa using getAncestorRoots_of_append_aux (otherAcc := [])
      (by simpa using walked) (by simp : init.concat final ≠ [])

end Store

end EthLib.Consensus
