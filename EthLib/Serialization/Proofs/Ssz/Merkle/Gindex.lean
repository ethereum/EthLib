import EthLib.Serialization.Ssz.Merkle.Gindex

/-! Arithmetic laws of the generalized indices, and the refusals their entry points make. -/

namespace EthLib.Serialization.Ssz

/-- The two children of a node are the two numbers whose halving gives it back. -/
theorem gindexParent_child (index : Nat) (rightSide : Bool) :
    gindexParent (gindexChild index rightSide) = index := by
  -- A child is the parent doubled, with one added on the right, and halving drops that.
  cases rightSide <;> simp [gindexParent, gindexChild]
  omega

/-- Siblings come in pairs, so naming one twice names the first again. -/
theorem gindexSibling_sibling (index : Nat) : gindexSibling (gindexSibling index) = index := by
  -- A sibling flips the lowest bit, and flipping it twice leaves it as it was.
  simp [gindexSibling, Nat.xor_assoc]

/-- An index sits at or above the power of two its depth names, and below the next. -/
theorem gindexDepth_bounds {index : Nat} (named : 1 ≤ index) :
    2 ^ Nat.log2 index ≤ index ∧ index < 2 ^ (Nat.log2 index + 1) :=
  -- The depth is where the leading bit sits, which is what brackets the index.
  ⟨Nat.log2_self_le (by omega), Nat.lt_log2_self⟩

/--
Splicing an index onto a position and reading it back gives the index unchanged.

An index carries its depth in its leading bit, so a splice is not a multiplication.
This round trip is what makes descending into a nested value's own tree sound.
-/
theorem gindexRebase_splice (outer index : Nat) (named : 1 ≤ index) :
    gindexRebase (outer * 2 ^ Nat.log2 index + (index - 2 ^ Nat.log2 index)) (Nat.log2 index)
      = index := by
  -- The index sits at or above its own leading bit, and below the next one up.
  obtain ⟨lower, upper⟩ := gindexDepth_bounds named
  -- So what the splice put below that bit is strictly narrower than the bit itself.
  have width : 2 ^ (Nat.log2 index + 1) = 2 ^ Nat.log2 index * 2 := by rw [Nat.pow_succ]
  -- Which means the outer position, shifted up past it, leaves no trace in the remainder.
  have below : (outer * 2 ^ Nat.log2 index + (index - 2 ^ Nat.log2 index)) % 2 ^ Nat.log2 index
      = index - 2 ^ Nat.log2 index := Nat.mul_add_mod_of_lt (by omega)
  simp only [gindexRebase, gindexBelow, below]
  -- Putting the leading bit back on what is left gives the index it was taken from.
  omega

/-- Siblings share a parent, which is the half both of them round down to. -/
theorem gindexSibling_half (index : Nat) : gindexSibling index / 2 = index / 2 := by
  -- Flipping the lowest bit leaves every bit above it alone, and those are the half.
  have shifted : (index ^^^ 1) >>> 1 = (index >>> 1) ^^^ (1 >>> 1) := Nat.shiftRight_xor_distrib
  simpa [gindexSibling, Nat.shiftRight_eq_div_pow] using shifted

/-- Siblings sit on opposite sides, so exactly one of the two is the odd one. -/
theorem gindexSibling_parity (index : Nat) : gindexSibling index % 2 = 1 - index % 2 := by
  -- The lowest bit is what a sibling flips, and the lowest bit is the parity.
  have flipped : (index ^^^ 1).testBit 0 = !index.testBit 0 := by rw [Nat.testBit_xor]; simp
  simp only [Nat.testBit_zero, gindexSibling] at flipped ⊢
  rcases Nat.mod_two_eq_zero_or_one index with side | side <;>
    rcases Nat.mod_two_eq_zero_or_one (index ^^^ 1) with pair | pair <;>
      simp [side, pair] at flipped ⊢

/-- An even node and its sibling are the left and right children of the node above them. -/
theorem gindexSibling_even {index : Nat} (even : index % 2 = 0) :
    index = 2 * (index / 2) ∧ gindexSibling index = 2 * (index / 2) + 1 := by
  -- The two facts a sibling keeps and flips are its half and its parity.
  have half := gindexSibling_half index
  have parity := gindexSibling_parity index
  omega

/-- An odd node and its sibling are the right and left children of the node above them. -/
theorem gindexSibling_odd {index : Nat} (odd : index % 2 = 1) :
    index = 2 * (index / 2) + 1 ∧ gindexSibling index = 2 * (index / 2) := by
  -- The two facts a sibling keeps and flips are its half and its parity.
  have half := gindexSibling_half index
  have parity := gindexSibling_parity index
  omega

/-- Climbing one more level is halving what the level below reached. -/
theorem shiftRight_succ (index level : Nat) : index >>> (level + 1) = index >>> level / 2 := by
  -- Shifting by a sum is shifting twice, and the last shift by one is a halving.
  rw [Nat.shiftRight_add]
  simp [Nat.shiftRight_eq_div_pow]

/-- The turn taken at one level is the parity of what the walk has reached there. -/
theorem gindexBit_parity (index level : Nat) :
    gindexBit index level = decide (index >>> level % 2 = 1) := by
  -- Reading a bit of an index is reading the lowest bit of the index shifted to it.
  simp [gindexBit]

/-- Climbing every level an index carries arrives at the root. -/
theorem shiftRight_depth {index : Nat} (named : 1 ≤ index) : index >>> Nat.log2 index = 1 := by
  -- The index sits at or above its own leading bit, and below the next one up.
  obtain ⟨lower, upper⟩ := gindexDepth_bounds named
  have doubled : 2 ^ (Nat.log2 index + 1) = 2 ^ Nat.log2 index * 2 := by rw [Nat.pow_succ]
  -- One leading bit is therefore all that is left once everything below it is shifted away.
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- The root sits on no branch, so a request naming it is refused. -/
theorem gindexLength_root : gindexLength 1 = .error .rootHasNoBranch :=
  -- The root needs no sibling, so it is not a valid single-branch request.
  rfl

/-- A number naming no node is refused before anything is measured of it. -/
theorem gindexDepth_zero : gindexDepth 0 = .error (.notAGindex 0) :=
  -- Zero cannot name a tree node because it carries no leading root bit.
  rfl

/-- A request naming no index is refused, since it would check nothing. -/
theorem rejectRelated_empty : rejectRelated [] = .error .emptyRequest :=
  -- With no claimed position, verification would establish nothing about the root.
  rfl

end EthLib.Serialization.Ssz
