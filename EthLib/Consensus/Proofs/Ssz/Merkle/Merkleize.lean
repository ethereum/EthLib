import EthLib.Consensus.Ssz.Merkle.Merkleize

/-! Laws of the abstract tree roots: padding depth, congruence, and roots past the data. -/

namespace EthLib.Consensus.Ssz

variable {α : Type}

/--
The chosen depth really does hold the requested number of leaves.

Without this the capacity check names a number unrelated to the tree built.
-/
theorem le_two_pow_depthFor (leafCount : Nat) : leafCount ≤ 2 ^ depthFor leafCount := by
  -- Recursing the proof the way the definition recurses keeps the two in step.
  -- Widths double one level up, and the halved count already fits the level below.
  induction leafCount using depthFor.induct with
  | case1 leafCount small => simp [depthFor, small]
  | case2 leafCount large ih => rw [depthFor, ite_eq_right large, Nat.pow_succ]; omega

/--
No shallower tree holds them, so the depth chosen is the least one that does.

Together with the bound above this pins the depth exactly.
That is what ties it to the specification's next power of two.
-/
theorem depthFor_le_of_le_two_pow {leafCount depth : Nat} (holds : leafCount ≤ 2 ^ depth) :
    depthFor leafCount ≤ depth := by
  induction leafCount using depthFor.induct generalizing depth with
  | case1 leafCount small =>
    -- A depth-zero tree is already the shallowest there is.
    simp [depthFor, small]
  | case2 leafCount large ih =>
    -- Two or more leaves need a level, so the bound must have come from one too.
    rw [depthFor, ite_eq_right large]
    cases depth with
    | zero => simp at holds; omega
    | succ shallower =>
      have := @ih shallower (by rw [Nat.pow_succ] at holds; omega)
      omega

/-- A leaf count that is already a power of two needs exactly the depth it names. -/
theorem depthFor_pow (depth : Nat) : depthFor (2 ^ depth) = depth := by
  -- No shallower tree holds that many leaves, and no deeper one is chosen.
  have below := depthFor_le_of_le_two_pow (Nat.le_refl (2 ^ depth))
  have above := (Nat.pow_le_pow_iff_right (by omega)).mp (le_two_pow_depthFor (2 ^ depth))
  omega

/--
Two leaf supplies that agree everywhere the tree reads give the same root.

The tree reads positions below its width and nothing else.
Every claim that a rearrangement leaves the root alone reduces to this one.
-/
theorem subtreeRoot_congr (combine : α → α → α) (depth : Nat) {f g : Nat → α}
    (agree : ∀ position, position < 2 ^ depth → f position = g position) :
    subtreeRoot combine depth f = subtreeRoot combine depth g := by
  -- The leaf supplies change on the way down, so they stay quantified over.
  induction depth generalizing f g with
  | zero =>
    -- A depth-zero tree reads position 0 alone, which the hypothesis covers.
    exact agree 0 (by decide)
  | succ depth ih =>
    -- Left half: positions below half the width, covered by the hypothesis.
    have left : subtreeRoot combine depth f = subtreeRoot combine depth g :=
      ih fun position bound => agree position (by omega)
    -- Right half: the same positions shifted up, still inside the full width.
    --
    --     full width = 2 ^ (depth + 1) = 2 ^ depth + 2 ^ depth
    --     shifted    = position + 2 ^ depth, with position < 2 ^ depth
    have right :
        subtreeRoot combine depth (fun i => f (i + 2 ^ depth))
          = subtreeRoot combine depth (fun i => g (i + 2 ^ depth)) :=
      ih fun position bound =>
        agree (position + 2 ^ depth) (by rw [Nat.pow_succ]; omega)
    simp [subtreeRoot, left, right]

/--
A tree of zero leaves folds to the table entry for its depth.

An empty subtree can then be answered by lookup rather than by hashing it out.
-/
theorem subtreeRoot_const_zero (combine : α → α → α) (zero : α) (depth : Nat) :
    subtreeRoot combine depth (fun _ => zero) = zeroRoot combine zero depth := by
  -- The leaf supply is the same constant at every level, so plain induction suffices.
  induction depth with
  | zero => rfl
  | succ depth ih => simp [subtreeRoot, zeroRoot, ih]

/--
Appending zero nodes to the data changes no leaf.

An implementation may fill its buffer out to the tree width, or leave it short.
Nothing above the leaves can tell the two apart.
-/
theorem padded_append_zeros (zero : α) (chunks : Array α) (count : Nat) :
    padded zero (chunks ++ Array.replicate count zero) = padded zero chunks := by
  -- Leaf supplies are functions, so they are equal once they agree pointwise.
  -- Past the data, the padding reads zero whether or not it was written.
  funext position
  simp only [padded, Array.getElem?_append, Array.getElem?_replicate]
  split <;> grind

/--
Materializing the padding does not change the root.

Cashed in whenever an implementation hashes a short buffer instead of a full one.
-/
theorem subtreeRoot_padded_append_zeros
    (combine : α → α → α) (zero : α) (depth : Nat) (chunks : Array α) (count : Nat) :
    subtreeRoot combine depth (padded zero (chunks ++ Array.replicate count zero))
      = subtreeRoot combine depth (padded zero chunks) := by
  -- The leaf supplies are equal outright, so the roots follow without induction.
  rw [padded_append_zeros]

/-- A tree whose data begins past the end of the array is the empty tree of its depth. -/
theorem subtreeRoot_padded_past_data (combine : α → α → α) (zero : α) (depth : Nat)
    (chunks : Array α) {start : Nat} (past : chunks.size ≤ start) :
    subtreeRoot combine depth (fun i => padded zero chunks (start + i))
      = zeroRoot combine zero depth := by
  -- Every position the tree reads lies past the data, so every leaf is zero.
  rw [← subtreeRoot_const_zero combine zero depth]
  refine subtreeRoot_congr combine depth fun position _ => ?_
  simp [padded, Array.getElem?_eq_none (show chunks.size ≤ start + position by omega)]

end EthLib.Consensus.Ssz
