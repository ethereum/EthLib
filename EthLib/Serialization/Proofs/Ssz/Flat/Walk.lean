import EthLib.Serialization.Proofs.Ssz.Flat.Fold

/-! Walking a bounded tree from its leaves to its root, and what that walk computes. -/

namespace EthLib.Serialization.Ssz

variable {α : Type}

/--
Levels folded away one at a time, from the leaves upward.

The fill a level pads with is the empty subtree of the height reached so far.
That is what keeps a short level in step with the tree it sits in.
-/
def foldUpTo (combine : α → α → α) (zero : α) : (remaining folded : Nat) → List α → List α
  -- No levels left to fold, so the level reached is the answer.
  | 0, _, level => level
  | remaining + 1, folded, level =>
      -- One level folded away is one fewer to go, at one greater height.
      foldUpTo combine zero remaining (folded + 1)
        (pairLevel combine (zeroRoot combine zero folded) level)

/--
Root of the bounded tree over a list of nodes, built from the leaves upward.

Nothing about the hash is assumed, so this holds of whatever a fold turns out to be.
-/
def merkleizeFlat (combine : α → α → α) (zero : α) (depth : Nat) (level : List α) : α :=
  -- An empty level folds to nothing, and its root is the empty subtree of the full depth.
  (foldUpTo combine zero depth 0 level).headD (zeroRoot combine zero depth)

/-- The first node of a level is the leaf a depth-zero tree reads. -/
theorem headD_eq_paddedList (fill : α) (level : List α) :
    level.headD fill = paddedList fill level 0 := by
  -- Both readings return the first present node, or the identical fill when the list is empty.
  cases level <;> rfl

/--
The walk reaches the root the specification names, at whatever height it starts.

Stated for a partial walk so the induction has something to hold on to.
The height reached so far fixes the padding, and both sides move it in step.
-/
theorem foldUpTo_headD (combine : α → α → α) (zero : α) :
    ∀ (remaining folded : Nat) (level : List α),
      (foldUpTo combine zero remaining folded level).headD
          (zeroRoot combine zero (folded + remaining))
        = subtreeRoot combine remaining (paddedList (zeroRoot combine zero folded) level) := by
  intro remaining
  -- Each fold raises the height and shortens the level, so both stay quantified over.
  induction remaining with
  | zero =>
    -- Nothing left to fold: the first node is the leaf, and an absent one is the padding.
    exact fun _ level => headD_eq_paddedList _ level
  | succ remaining ih =>
    intro folded level
    -- The height the walk has reached is the same counted from either end.
    rw [foldUpTo, show folded + (remaining + 1) = folded + 1 + remaining by omega, ih]
    -- A pair of empty subtrees is the empty subtree one level up.
    show subtreeRoot combine remaining
        (paddedList (combine (zeroRoot combine zero folded) (zeroRoot combine zero folded)) _) = _
    -- Folding the level and folding the leaves it stands for agree.
    rw [paddedList_pairLevel, ← subtreeRoot_succ]

/-- The walk computes the tree the specification defines, over the leaves it was given. -/
theorem merkleizeFlat_eq (combine : α → α → α) (zero : α) (depth : Nat) (level : List α) :
    merkleizeFlat combine zero depth level
      = subtreeRoot combine depth (paddedList zero level) := by
  -- A walk of the full depth starts at height zero, where the padding is the zero node.
  simpa [merkleizeFlat, zeroRoot] using foldUpTo_headD combine zero depth 0 level

end EthLib.Serialization.Ssz
