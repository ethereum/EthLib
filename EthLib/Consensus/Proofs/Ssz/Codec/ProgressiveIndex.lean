import EthLib.Consensus.Ssz.Codec.Proof
import EthLib.Consensus.Proofs.Ssz.Merkle.Gindex

/-! Progressive chunk indices select their own leaf through the widening Merkle spine. -/

namespace EthLib.Consensus.Ssz

/-- Removing a suffix from a positive index subtracts exactly its number of turns. -/
theorem gindex_prefix_depth (index turns spine : Nat) (positive : 0 < spine)
    (ancestor : index >>> turns = spine) : Nat.log2 index = Nat.log2 spine + turns := by
  -- The quotient fixes the high bits.
  -- The remainder occupies only the removed low bits.
  rw [Nat.shiftRight_eq_div_pow] at ancestor
  have width := Nat.two_pow_pos turns
  have division := Nat.mod_add_div index (2 ^ turns)
  have remainder := Nat.mod_lt index width
  rw [ancestor, Nat.mul_comm (2 ^ turns) spine] at division
  obtain ⟨lower, upper⟩ := gindexDepth_bounds positive
  have low := Nat.mul_le_mul_right (2 ^ turns) lower
  have high := Nat.mul_le_mul_right (2 ^ turns) (Nat.succ_le_of_lt upper)
  simp only [Nat.succ_mul] at high
  -- A positive ancestor rules out a zero combined index.
  have nonzero : index ≠ 0 := by intro zero; simp [zero] at ancestor; omega
  apply (Nat.log2_eq_iff nonzero).mpr
  rw [Nat.pow_add, show Nat.log2 spine + turns + 1 = (Nat.log2 spine + 1) + turns by omega,
    Nat.pow_add]
  constructor <;> omega

private theorem progressive_selection : ∀ chunk depth spine start count,
    0 < spine → start + chunk < count →
    ∃ turns stop,
      0 < turns ∧
      progressiveChunkGindex chunk depth spine >>> turns = spine ∧
      spineWalk count (progressiveChunkGindex chunk depth spine) turns start (2 ^ depth) = .ok stop ∧
      stop.turnedLeft = true ∧ stop.capacity = 2 ^ stop.depth ∧
      stop.leavesFrom + gindexBelow (progressiveChunkGindex chunk depth spine) stop.depth = start + chunk ∧
      stop.leavesFrom < count := by
  -- Skip complete spine levels until the chunk lies in the current level's bounded tree.
  intro chunk
  induction chunk using Nat.strongRecOn with
  | ind chunk ih =>
    intro depth spine start count positive inside
    have width := Nat.two_pow_pos depth
    -- A chunk within the current capacity turns left.
    -- Otherwise it skips that capacity and follows the right spine.
    by_cases fits : chunk < 2 ^ depth
    · have index : progressiveChunkGindex chunk depth spine = spine * 2 * 2 ^ depth + chunk := by
        rw [progressiveChunkGindex, ite_eq_left fits]
      -- Removing the bounded segment’s low turns leaves the spine node followed by its left turn.
      have parent : (spine * 2 * 2 ^ depth + chunk) / 2 ^ depth = spine * 2 := by
        simp [Nat.add_div width, Nat.div_eq_of_lt fits, Nat.mod_eq_of_lt fits, Nat.two_pow_pos]
        exact fits
      have ancestor : (spine * 2 * 2 ^ depth + chunk) >>> (depth + 1) = spine := by
        rw [shiftRight_succ, Nat.shiftRight_eq_div_pow, parent]
        omega
      have turn : gindexBit (spine * 2 * 2 ^ depth + chunk) depth = false := by
        simp [gindexBit, Nat.testBit_eq_decide_div_mod_eq, parent]
      refine ⟨depth + 1, ⟨depth, start, 2 ^ depth, true⟩, by omega,
        by simpa only [index] using ancestor, ?_, rfl, rfl, ?_, by change start < count; omega⟩
      · simp [index, spineWalk, show ¬start ≥ count by omega, turn, pure, Except.pure]
      · simp [index, gindexBelow, Nat.mul_add_mod_of_lt fits]
    -- Skipping an occupied segment strictly decreases the remaining chunk ordinal.
    · have smaller : chunk - 2 ^ depth < chunk := by omega
      obtain ⟨turns, stop, nonzero, ancestor, walked, left, capacity, selected, reached⟩ :=
        ih (chunk - 2 ^ depth) smaller (depth + 2) (spine * 2 + 1) (start + 2 ^ depth)
          count (by omega) (by omega)
      have index : progressiveChunkGindex chunk depth spine =
          progressiveChunkGindex (chunk - 2 ^ depth) (depth + 2) (spine * 2 + 1) := by
        rw [progressiveChunkGindex, ite_eq_right fits]
      have turn : gindexBit (progressiveChunkGindex chunk depth spine) turns = true := by
        rw [gindexBit_parity, index, ancestor]; simp
      refine ⟨turns + 1, stop, by omega, ?_, ?_, left, capacity, ?_, reached⟩
      · rw [index, shiftRight_succ, ancestor]
        omega
      · rw [spineWalk]
        simp only [show ¬start ≥ count by omega, ite_false, turn, Bool.not_true, Bool.false_eq_true]
        simpa only [index, Nat.pow_add, show 2 ^ 2 = 4 by decide] using walked
      · rw [index]
        omega

/-- A progressive chunk's path leaves the spine at its bounded subtree and exact leaf ordinal. -/
theorem progressiveChunkGindex_selection (chunk count : Nat) (inside : chunk < count) :
    let index := progressiveChunkGindex chunk
    ∃ stop : SpineStop,
      2 ≤ index ∧ gindexBit index (Nat.log2 index - 1) = false ∧
      spineWalk count index (Nat.log2 index - 1) 0 1 = .ok stop ∧
      stop.turnedLeft = true ∧ stop.capacity = 2 ^ stop.depth ∧
      stop.leavesFrom + gindexBelow index stop.depth = chunk ∧ stop.leavesFrom < count := by
  -- The outer index 2 contributes the left turn below the mixed-in word.
  obtain ⟨turns, stop, positive, ancestor, walked, left, capacity, selected, reached⟩ :=
    progressive_selection chunk 0 2 0 count (by decide) (by simpa using inside)
  have depth := gindex_prefix_depth (progressiveChunkGindex chunk) turns 2 (by decide) ancestor
  -- The initial contents index contributes one leading left turn in addition to the spine path.
  have turnsDepth : Nat.log2 (progressiveChunkGindex chunk) - 1 = turns := by
    change Nat.log2 (progressiveChunkGindex chunk) = 1 + turns at depth
    omega
  refine ⟨stop, ?_, ?_, ?_, left, capacity, by simpa using selected, reached⟩
  -- Skipping an occupied segment strictly decreases the remaining chunk ordinal.
  · have smaller := Nat.div_le_self (progressiveChunkGindex chunk) (2 ^ turns)
    rw [Nat.shiftRight_eq_div_pow] at ancestor
    omega
  · rw [turnsDepth, gindexBit_parity, ancestor]; rfl
  · simpa only [turnsDepth, Nat.pow_zero] using walked

end EthLib.Consensus.Ssz
