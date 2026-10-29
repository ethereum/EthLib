import EthLib.Consensus.Ssz.Merkle.Merkleize

/-! Building a tree from its leaves upward, which is the order an implementation works in. -/

namespace EthLib.Consensus.Ssz

variable {α : Type}

/-- Leaves of a tree taken from a list, positions past the end reading as the fill. -/
def paddedList (fill : α) (nodes : List α) : Nat → α :=
  -- Missing positions read the same fill as the conceptual infinite padded leaf supply.
  fun position => nodes[position]?.getD fill

/-- One whole level folded away, each pair of leaves becoming the leaf above it. -/
def levelFold (combine : α → α → α) (leaves : Nat → α) : Nat → α :=
  -- Positions 2 and 3 below become position 1 above, and the same pairing applies everywhere.
  fun i => combine (leaves (2 * i)) (leaves (2 * i + 1))

/--
One level of nodes folded into the level above it.

A level of odd length is missing exactly one right sibling, at its end.
The fill stands in for that sibling, and for every leaf past the data.
-/
def pairLevel (combine : α → α → α) (fill : α) : List α → List α
  -- A final unpaired left node receives the fill as its missing right sibling.
  | [] => []
  | [node] => [combine node fill]
  | left :: right :: rest => combine left right :: pairLevel combine fill rest

/--
Folding the bottom level away leaves the same tree, one level shorter.

This is the whole of why an implementation may work upward from the leaves while the specification is stated downward from the root.
-/
theorem subtreeRoot_succ (combine : α → α → α) (depth : Nat) (leaves : Nat → α) :
    subtreeRoot combine (depth + 1) leaves
      = subtreeRoot combine depth (levelFold combine leaves) := by
  -- The leaf supply changes on the way down, so it stays quantified over.
  induction depth generalizing leaves with
  | zero => rfl
  | succ depth ih =>
    -- The right half's leaves, folded, are the folded leaves' right half.
    have shift : (levelFold combine fun i => leaves (i + 2 ^ (depth + 1)))
        = fun i => levelFold combine leaves (i + 2 ^ depth) := by
      funext i
      -- Both read the same two leaves, one half-width along and then paired.
      simp only [levelFold, Nat.pow_succ]
      congr 2 <;> omega
    -- Each half of the tree is then the same claim one level down.
    show combine (subtreeRoot combine (depth + 1) leaves)
        (subtreeRoot combine (depth + 1) fun i => leaves (i + 2 ^ (depth + 1)))
      = combine (subtreeRoot combine depth (levelFold combine leaves))
        (subtreeRoot combine depth fun i => levelFold combine leaves (i + 2 ^ depth))
    rw [ih, ih, shift]

/--
Folding a list agrees with folding the leaves it stands for.

A pair of fills folds to the fill of the level above, which is what keeps the padding of a short level in step with the padding of the tree it sits in.
-/
theorem paddedList_pairLevel (combine : α → α → α) (fill : α) (level : List α) :
    paddedList (combine fill fill) (pairLevel combine fill level)
      = levelFold combine (paddedList fill level) := by
  funext position
  -- The list shrinks by two and the position by one, so the position stays quantified over.
  induction level using pairLevel.induct generalizing position with
  | case1 =>
    -- An empty level reads as the fill everywhere, above and below alike.
    simp [paddedList, levelFold, pairLevel]
  | case2 node =>
    -- A lone node is paired with the fill, and past it both sides read two fills.
    cases position <;> simp [paddedList, levelFold, pairLevel]
  | case3 left right rest ih =>
    match position with
    -- The first leaf above is the first pair below.
    | 0 => simp [paddedList, levelFold, pairLevel]
    -- Every later one skips the pair just folded, which is the same claim two shorter.
    | position + 1 =>
      have below : 2 * (position + 1) = 2 * position + 1 + 1 := by omega
      simpa only [paddedList, levelFold, pairLevel, below, List.getElem?_cons_succ] using ih position

/-- Folding pairs a level up, so its length halves, an odd node keeping a place of its own. -/
theorem pairLevel_length (combine : α → α → α) (fill : α) (level : List α) :
    (pairLevel combine fill level).length = (level.length + 1) / 2 := by
  induction level using pairLevel.induct with
  | case1 => simp [pairLevel]
  | case2 => simp [pairLevel]
  -- Two nodes below became one above, and the rest is the same claim two shorter.
  | case3 _ _ rest ih => simp only [pairLevel, List.length_cons, ih]; omega

/--
Appending the fill to an odd level changes nothing about the level above it.

An implementation may write the missing sibling into the buffer, or supply it per pair.
This says the two come to the same thing.
-/
theorem pairLevel_append_fill (combine : α → α → α) (fill : α) (level : List α)
    (odd : level.length % 2 = 1) :
    pairLevel combine fill (level ++ [fill]) = pairLevel combine fill level := by
  induction level using pairLevel.induct with
  -- An empty level has even length, so there is nothing to append to.
  | case1 => simp at odd
  -- A lone node is paired with the fill either way.
  | case2 => rfl
  -- Two nodes below become one above, and the rest is the same claim two shorter.
  | case3 _ _ rest ih =>
    simp only [List.length_cons] at odd
    simp only [List.cons_append, pairLevel, ih (by omega)]

end EthLib.Consensus.Ssz
